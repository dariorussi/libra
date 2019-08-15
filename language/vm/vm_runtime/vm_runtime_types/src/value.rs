// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::loaded_data::{struct_def::StructDef, types::Type};
use canonical_serialization::*;
use failure::prelude::*;
use std::{
    cell::{Ref, RefCell},
    convert::TryFrom,
    mem::replace,
    ops::Add,
    rc::Rc,
};
use types::{
    access_path::AccessPath,
    account_address::{AccountAddress, ADDRESS_LENGTH},
    byte_array::ByteArray,
};
use vm::{
    errors::*,
    gas_schedule::{words_in, AbstractMemorySize, GasAlgebra, GasCarrier, CONST_SIZE, REFERENCE_SIZE, STRUCT_SIZE},
    IndexKind,
};

#[cfg(test)]
#[path = "unit_tests/value_prop_tests.rs"]
mod value_prop_tests;
#[cfg(test)]
#[path = "unit_tests/value_tests.rs"]
mod value_tests;
#[cfg(test)]
#[path = "unit_tests/vm_types.rs"]
mod vm_types;

/// Runtime representation of a value.
///
/// `ValueImpl` is a single enum that describes all possible values expressed in Move and those
/// internal to the runtime (e.g. `Invalid`).
/// `ValueImpl` is private to this module and wrapper types are used to limit the values available
/// in different context.
/// For instance, `[Value]` is a wrapper of `ValueImpl` that does not allow `Invalid` to be
/// represented. In that sense instances of `[Value]` are what gets pushed/popped on the
/// stack and effectively the values representable in Move.
#[derive(PartialEq, Eq, Debug, Clone)]
enum ValueImpl {
    /// Locals are invalid on entry of a function and when moved out.
    Invalid,
    // Primitive types
    U64(u64),
    Address(AccountAddress),
    Bool(bool),
    ByteArray(ByteArray),
    String(String),

    /// A struct in Move.
    Struct(Struct),

    /// Reference to a local.
    Reference(Reference),
    /// Global reference into storage.
    GlobalRef(GlobalRef),
    /// A reference to a local.
    ///
    /// This value is used to promote a value into a reference lazily when borrowing a local.
    LocalRef(Reference),
}

/// A Move value.
///
/// `Value` is just a wrapper type around `[ValueImpl]` which allows only Move types.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Value(ValueImpl);

/// Internal representation for a reference or a mutable value.
#[derive(PartialEq, Eq, Debug, Clone)]
struct MutVal(Rc<RefCell<Value>>);

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Struct(Vec<MutVal>);

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Reference(MutVal);

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Locals(Vec<ValueImpl>);

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum ReferenceValue {
    Reference(Reference),
    GlobalRef(GlobalRef),
}

/// Status for on chain data (published resources):
/// CLEAN - the data was only read
/// DIRTY - the data was changed anywhere in the data tree of the given resource
/// DELETED - MoveFrom was called on the given AccessPath for the given resource
#[rustfmt::skip]
#[allow(non_camel_case_types)]
#[derive(PartialEq, Eq, Debug, Clone)]
enum GlobalDataStatus {
    CLEAN   = 0,
    DIRTY   = 1,
    DELETED = 2,
}

/// A root into an instance on chain.
/// Holds flags about the status of the instance and a reference count to balance
/// Borrow* and ReleaseRef
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct RootAccessPath {
    status: GlobalDataStatus,
    ap: AccessPath,
}

/// A GlobalRef holds the reference to the data and a shared reference to the root so
/// status flags and reference count can be properly managed
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct GlobalRef {
    root: Rc<RefCell<RootAccessPath>>,
    reference: MutVal,
}

impl ValueImpl {
    fn into_value(self) -> std::result::Result<Value, VMInvariantViolation> {
        match self {
            ValueImpl::Invalid => Err(VMInvariantViolation::InternalTypeError),
            ValueImpl::LocalRef(reference) => reference.into_value(),
            _ => Ok(Value(self)),
        }
    }

    fn copy_value(&self) -> std::result::Result<Value, VMInvariantViolation> {
        match self {
            ValueImpl::Invalid => Err(VMInvariantViolation::InternalTypeError),
            ValueImpl::LocalRef(reference) => reference.copy_value(),
            _ => Ok(Value(self.clone())),
        }
    }

    fn borrow_field(
        &self,
        field_offset: usize,
    ) -> std::result::Result<Value, VMInvariantViolation> {
        match self {
            ValueImpl::Struct(s) => s.get_field_reference(field_offset),
            _ => Err(VMInvariantViolation::InternalTypeError),
        }
    }

    fn size(&self) -> AbstractMemorySize<GasCarrier> {
        match self {
            ValueImpl::Invalid | ValueImpl::U64(_) | ValueImpl::Bool(_) => *CONST_SIZE,
            ValueImpl::Address(_) => AbstractMemorySize::new(ADDRESS_LENGTH as u64),
            // Possible debate topic: Should we charge based upon the size of the string.
            // At this moment, we take the view that you should be charged as though you are
            // copying the string onto the stack here. This doesn't replicate
            // the semantics that we utilize currently, but this string may
            // need to be copied at some later time, so we need to charge based
            // upon the size of the memory that will possibly need to be accessed.
            ValueImpl::String(s) => words_in(AbstractMemorySize::new(s.len() as u64)),
            ValueImpl::ByteArray(key) => AbstractMemorySize::new(key.len() as u64),
            ValueImpl::Struct(s) => s.size(),
            ValueImpl::Reference(reference) => reference.size(),
            ValueImpl::GlobalRef(reference) => reference.size(),
            ValueImpl::LocalRef(reference) => reference.0.size(),
        }
    }

    // Structural equality for Move values
    fn equals(&self, v2: &ValueImpl) -> std::result::Result<bool, VMInvariantViolation> {
        match (self, v2) {
            // TODO: this does not look right to me....
            (ValueImpl::Invalid, ValueImpl::Invalid) => Ok(true),
            // values
            (ValueImpl::U64(u1), ValueImpl::U64(u2)) => Ok(u1 == u2),
            (ValueImpl::Bool(b1), ValueImpl::Bool(b2)) => Ok(b1 == b2),
            (ValueImpl::Address(a1), ValueImpl::Address(a2)) => Ok(a1 == a2),
            (ValueImpl::ByteArray(ba1), ValueImpl::ByteArray(ba2)) => Ok(ba1 == ba2),
            (ValueImpl::String(s1), ValueImpl::String(s2)) => Ok(s1 == s2),
            (ValueImpl::Struct(s1), ValueImpl::Struct(s2)) => s1.equals(s2),
            // references
            (ValueImpl::Reference(ref1), ValueImpl::Reference(ref2)) => ref1.equals(ref2),
            (ValueImpl::GlobalRef(gr1), ValueImpl::GlobalRef(gr2)) => gr1.equals(gr2),
            (ValueImpl::GlobalRef(gr), ValueImpl::Reference(reference)) => gr.equals_ref(reference),
            (ValueImpl::Reference(reference), ValueImpl::GlobalRef(gr)) => gr.equals_ref(reference),
            _ => Err(VMInvariantViolation::InternalTypeError),
        }
    }

    /// Normal code should always know what type this value has. This is made available only for
    /// tests.
    #[allow(non_snake_case)]
    #[doc(hidden)]
    fn to_type_FOR_TESTING(&self) -> Type {
        match self {
            ValueImpl::Invalid => unreachable!("Cannot ask type of invalid location"),
            ValueImpl::U64(_) => Type::U64,
            ValueImpl::Address(_) => Type::Address,
            ValueImpl::Bool(_) => Type::Bool,
            ValueImpl::ByteArray(_) => Type::ByteArray,
            ValueImpl::String(_) => Type::String,
            ValueImpl::Struct(s) => Type::Struct(s.to_struct_def_FOR_TESTING()),
            ValueImpl::Reference(reference) => {
                Type::Reference(Box::new(reference.to_type_FOR_TESTING()))
            }
            ValueImpl::GlobalRef(reference) => {
                Type::Reference(Box::new(reference.to_type_FOR_TESTING()))
            }
            ValueImpl::LocalRef(reference) => reference.to_type_FOR_TESTING(),
        }
    }
}

impl Value {
    fn new(value: ValueImpl) -> Self {
        Value(value)
    }

    pub fn u64(value: u64) -> Self {
        Value(ValueImpl::U64(value))
    }

    pub fn address(address: AccountAddress) -> Self {
        Value(ValueImpl::Address(address))
    }

    pub fn bool(value: bool) -> Self {
        Value(ValueImpl::Bool(value))
    }

    pub fn byte_array(bytearray: ByteArray) -> Self {
        Value(ValueImpl::ByteArray(bytearray))
    }

    pub fn string(s: String) -> Self {
        Value(ValueImpl::String(s))
    }

    pub fn struct_(s: Struct) -> Self {
        Value(ValueImpl::Struct(s))
    }

    pub fn reference(reference: Reference) -> Self {
        Value(ValueImpl::Reference(reference))
    }

    pub fn global_ref(reference: GlobalRef) -> Self {
        Value(ValueImpl::GlobalRef(reference))
    }

    pub fn value_as<T>(self) -> Option<T>
    where
        Option<T>: From<Value>,
    {
        std::convert::Into::into(self)
    }

    pub fn size(&self) -> AbstractMemorySize<GasCarrier> {
        self.0.size()
    }

    fn copy_value(&self) -> std::result::Result<Value, VMInvariantViolation> {
        self.0.copy_value()
    }

    fn borrow_field(
        &self,
        field_offset: usize,
    ) -> std::result::Result<Value, VMInvariantViolation> {
        self.0.borrow_field(field_offset)
    }

    pub fn equals(&self, v2: &Value) -> std::result::Result<bool, VMInvariantViolation> {
        self.0.equals(&v2.0)
    }

    pub fn not_equals(&self, v2: &Value) -> std::result::Result<bool, VMInvariantViolation> {
        self.equals(v2).and_then(|res| Ok(!res))
    }

    pub fn is_global_ref(&self) -> bool {
        match &self.0 {
            ValueImpl::GlobalRef(_) => true,
            _ => false,
        }
    }

    pub fn as_struct_ref(&self) -> Option<&Struct> {
        match &self.0 {
            ValueImpl::Struct(s) => Some(s),
            _ => None,
        }
    }

    /// Normal code should always know what type this value has. This is made available only for
    /// tests.
    #[allow(non_snake_case)]
    #[doc(hidden)]
    pub fn to_type_FOR_TESTING(&self) -> Type {
        self.0.to_type_FOR_TESTING()
    }
}

impl From<Value> for Option<u64> {
    fn from(value: Value) -> Option<u64> {
        match value.0 {
            ValueImpl::U64(i) => Some(i),
            _ => None,
        }
    }
}

impl From<Value> for Option<bool> {
    fn from(value: Value) -> Option<bool> {
        match value.0 {
            ValueImpl::Bool(b) => Some(b),
            _ => None,
        }
    }
}

impl From<Value> for Option<AccountAddress> {
    fn from(value: Value) -> Option<AccountAddress> {
        match value.0 {
            ValueImpl::Address(address) => Some(address),
            _ => None,
        }
    }
}

impl From<Value> for Option<ByteArray> {
    fn from(value: Value) -> Option<ByteArray> {
        match value.0 {
            ValueImpl::ByteArray(byte_array) => Some(byte_array),
            _ => None,
        }
    }
}

impl From<Value> for Option<Struct> {
    fn from(value: Value) -> Option<Struct> {
        match value.0 {
            ValueImpl::Struct(s) => Some(s),
            _ => None,
        }
    }
}

impl From<Value> for Option<ReferenceValue> {
    fn from(value: Value) -> Option<ReferenceValue> {
        match value.0 {
            ValueImpl::Reference(reference) => Some(ReferenceValue::Reference(reference)),
            ValueImpl::GlobalRef(reference) => Some(ReferenceValue::GlobalRef(reference)),
            _ => None,
        }
    }
}

impl From<Value> for Option<Reference> {
    fn from(value: Value) -> Option<Reference> {
        match value.0 {
            ValueImpl::Reference(reference) => Some(reference),
            _ => None,
        }
    }
}

impl From<Value> for Option<GlobalRef> {
    fn from(value: Value) -> Option<GlobalRef> {
        match value.0 {
            ValueImpl::GlobalRef(reference) => Some(reference),
            _ => None,
        }
    }
}

impl MutVal {
    fn new(v: Value) -> Self {
        MutVal(Rc::new(RefCell::new(v)))
    }

    fn peek(&self) -> Ref<Value> {
        self.0.borrow()
    }

    fn into_value(self) -> std::result::Result<Value, VMInvariantViolation> {
        match Rc::try_unwrap(self.0) {
            Ok(cell) => Ok(cell.into_inner()),
            Err(_) => Err(VMInvariantViolation::LocalReferenceError),
        }
    }

    fn copy_value(&self) -> std::result::Result<Value, VMInvariantViolation> {
        self.peek().copy_value()
    }

    fn size(&self) -> AbstractMemorySize<GasCarrier> {
        self.peek().size()
    }

    fn borrow_field(
        &self,
        field_offset: usize,
    ) -> std::result::Result<Value, VMInvariantViolation> {
        self.peek().borrow_field(field_offset)
    }

    fn write_value(self, value: Value) {
        self.0.replace(value);
    }

    /// Normal code should always know what type this value has. This is made available only for
    /// tests.
    #[allow(non_snake_case)]
    #[doc(hidden)]
    fn to_type_FOR_TESTING(&self) -> Type {
        self.peek().to_type_FOR_TESTING()
    }

    fn equals(&self, v2: &MutVal) -> std::result::Result<bool, VMInvariantViolation> {
        self.peek().equals(&v2.peek())
    }
}

impl Reference {
    pub fn new(value: Value) -> Self {
        Reference(MutVal::new(value))
    }

    fn into_value(self) -> std::result::Result<Value, VMInvariantViolation> {
        self.0.into_value()
    }

    fn copy_value(&self) -> std::result::Result<Value, VMInvariantViolation> {
        self.0.copy_value()
    }

    fn size(&self) -> AbstractMemorySize<GasCarrier> {
        words_in(*REFERENCE_SIZE)
    }

    fn borrow_field(
        &self,
        field_offset: usize,
    ) -> std::result::Result<Value, VMInvariantViolation> {
        self.0.borrow_field(field_offset)
    }

    fn write_value(self, value: Value) {
        self.0.write_value(value);
    }

    fn equals(&self, ref2: &Reference) -> std::result::Result<bool, VMInvariantViolation> {
        self.0.equals(&ref2.0)
    }

    /// Normal code should always know what type this value has. This is made available only for
    /// tests.
    #[allow(non_snake_case)]
    #[doc(hidden)]
    fn to_type_FOR_TESTING(&self) -> Type {
        self.0.to_type_FOR_TESTING()
    }
}

impl Struct {
    pub fn new(values: Vec<Value>) -> Self {
        let mut fields = vec![];
        for value in values {
            fields.push(MutVal::new(value));
        }
        Struct(fields)
    }

    #[allow(dead_code)]
    pub fn get_field_reference(
        &self,
        field_offset: usize,
    ) -> std::result::Result<Value, VMInvariantViolation> {
        if let Some(field_ref) = self.0.get(field_offset) {
            Ok(Value::reference(Reference(field_ref.clone())))
        } else {
            Err(VMInvariantViolation::InternalTypeError)
        }
    }

    pub fn get_field_value(
        &self,
        field_offset: usize,
    ) -> std::result::Result<Value, VMInvariantViolation> {
        if let Some(field_ref) = self.0.get(field_offset) {
            field_ref.copy_value()
        } else {
            Err(VMInvariantViolation::InternalTypeError)
        }
    }

    fn equals(&self, s2: &Struct) -> std::result::Result<bool, VMInvariantViolation> {
        if self.0.len() != s2.0.len() {
            return Err(VMInvariantViolation::InternalTypeError);
        }
        for (v1, v2) in self.0.iter().zip(&s2.0) {
            if !v1.equals(v2)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Normal code should always know what type this value has. This is made available only for
    /// tests.
    #[allow(non_snake_case)]
    #[doc(hidden)]
    fn to_struct_def_FOR_TESTING(&self) -> StructDef {
        let fields = self.0.iter().map(MutVal::to_type_FOR_TESTING).collect();
        StructDef::new(fields)
    }

    pub fn size(&self) -> AbstractMemorySize<GasCarrier> {
        self.0
            .iter()
            .fold(*STRUCT_SIZE, |acc, vl| acc.map2(vl.size(), Add::add))
    }
}

impl ReferenceValue {
    pub fn new(value: Value) -> std::result::Result<Self, VMInvariantViolation> {
        match value.0 {
            ValueImpl::Reference(reference) => Ok(ReferenceValue::Reference(reference)),
            ValueImpl::GlobalRef(reference) => Ok(ReferenceValue::GlobalRef(reference)),
            _ => Err(VMInvariantViolation::InternalTypeError),
        }
    }

    pub fn borrow_field(
        self,
        field_offset: usize,
    ) -> std::result::Result<Value, VMInvariantViolation> {
        match self {
            ReferenceValue::GlobalRef(ref reference) => reference.borrow_field(field_offset),
            ReferenceValue::Reference(ref reference) => reference.borrow_field(field_offset),
        }
    }

    pub fn read_ref(self) -> std::result::Result<Value, VMInvariantViolation> {
        match self {
            ReferenceValue::GlobalRef(reference) => reference.copy_value(),
            ReferenceValue::Reference(reference) => reference.copy_value(),
        }
    }

    pub fn write_ref(self, value: Value) {
        match self {
            ReferenceValue::GlobalRef(reference) => reference.write_value(value),
            ReferenceValue::Reference(reference) => reference.write_value(value),
        }
    }
}

impl RootAccessPath {
    pub fn new(ap: AccessPath) -> Self {
        RootAccessPath {
            status: GlobalDataStatus::CLEAN,
            ap,
        }
    }

    fn mark_dirty(&mut self) {
        self.status = GlobalDataStatus::DIRTY;
    }

    #[allow(dead_code)]
    fn mark_deleted(&mut self) {
        self.status = GlobalDataStatus::DELETED;
    }
}

impl GlobalRef {
    pub fn make_root(ap: AccessPath, value: Value) -> Self {
        GlobalRef {
            root: Rc::new(RefCell::new(RootAccessPath::new(ap))),
            reference: MutVal::new(value),
        }
    }

    pub fn move_to(ap: AccessPath, value: Struct) -> Self {
        let mut root = RootAccessPath::new(ap);
        root.mark_dirty();
        GlobalRef {
            root: Rc::new(RefCell::new(root)),
            reference: MutVal::new(Value::struct_(value)),
        }
    }

    fn new_ref(root: &GlobalRef, reference: MutVal) -> Self {
        GlobalRef {
            root: Rc::clone(&root.root),
            reference,
        }
    }

    // Return the resource behind the reference.
    // If the reference is not exclusively held by the cache (ref count 0) returns None
    pub fn get_data(self) -> Option<Value> {
        match Rc::try_unwrap(self.root) {
            Ok(_) => match Rc::try_unwrap(self.reference.0) {
                Ok(res) => Some(res.into_inner()),
                Err(_) => None,
            },
            Err(_) => None,
        }
    }

    pub fn is_loadable(&self) -> bool {
        !self.is_deleted()
    }

    pub fn is_dirty(&self) -> bool {
        self.root.borrow().status == GlobalDataStatus::DIRTY
    }

    pub fn is_deleted(&self) -> bool {
        self.root.borrow().status == GlobalDataStatus::DELETED
    }

    pub fn is_clean(&self) -> bool {
        self.root.borrow().status == GlobalDataStatus::CLEAN
    }

    pub fn move_from(&mut self) -> std::result::Result<Value, VMInvariantViolation> {
        self.root.borrow_mut().mark_deleted();
        self.reference.copy_value()
    }

    pub fn size(&self) -> AbstractMemorySize<GasCarrier> {
        words_in(*REFERENCE_SIZE)
    }

    fn borrow_field(
        &self,
        field_offset: usize,
    ) -> std::result::Result<Value, VMInvariantViolation> {
        let field_ref = self.reference.borrow_field(field_offset)?.value_as::<Reference>().unwrap().0;
        Ok(Value::global_ref(GlobalRef::new_ref(self, field_ref)))
    }

    fn copy_value(&self) -> std::result::Result<Value, VMInvariantViolation> {
        let value = self.reference.copy_value()?;
        Ok(value)
    }

    fn write_value(self, value: Value) {
        self.root.borrow_mut().mark_dirty();
        self.reference.write_value(value);
    }

    fn equals(&self, v2: &GlobalRef) -> std::result::Result<bool, VMInvariantViolation> {
        self.reference.equals(&v2.reference)
    }

    fn equals_ref(&self, v2: &Reference) -> std::result::Result<bool, VMInvariantViolation> {
        self.reference.equals(&v2.0)
    }

    /// Normal code should always know what type this value has. This is made available only for
    /// tests.
    #[allow(non_snake_case)]
    #[doc(hidden)]
    fn to_type_FOR_TESTING(&self) -> Type {
        self.reference.to_type_FOR_TESTING()
    }
}

impl Locals {
    pub fn new(size: usize) -> Self {
        Locals(vec![ValueImpl::Invalid; size])
    }

    pub fn copy_loc(&self, idx: usize) -> std::result::Result<Value, VMInvariantViolation> {
        if let Some(local_ref) = self.0.get(idx) {
            local_ref.copy_value()
        } else {
            Err(VMInvariantViolation::IndexOutOfBounds(
                IndexKind::LocalPool,
                idx,
                self.0.len(),
            ))
        }
    }

    pub fn move_loc(&mut self, idx: usize) -> std::result::Result<Value, VMInvariantViolation> {
        if let Some(local_ref) = self.0.get_mut(idx) {
            let old_local = replace(local_ref, ValueImpl::Invalid);
            old_local.into_value()
        } else {
            Err(VMInvariantViolation::IndexOutOfBounds(
                IndexKind::LocalPool,
                idx,
                self.0.len(),
            ))
        }
    }

    pub fn store_loc(
        &mut self,
        idx: usize,
        value: Value,
    ) -> std::result::Result<(), VMInvariantViolation> {
        if let Some(local_ref) = self.0.get_mut(idx) {
            replace(local_ref, value.0);
            Ok(())
        } else {
            Err(VMInvariantViolation::IndexOutOfBounds(
                IndexKind::LocalPool,
                idx,
                self.0.len(),
            ))
        }
    }

    pub fn borrow_loc(&mut self, idx: usize) -> std::result::Result<Value, VMInvariantViolation> {
        if let Some(local_ref) = self.0.get_mut(idx) {
            match local_ref {
                ValueImpl::GlobalRef(_) | ValueImpl::Reference(_) | ValueImpl::Invalid => {
                    Err(VMInvariantViolation::InternalTypeError)
                }
                ValueImpl::LocalRef(reference) => Ok(Value::reference(reference.clone())),
                _ => {
                    let ref_value = MutVal::new(Value::new(local_ref.clone()));
                    let new_local_ref = ValueImpl::LocalRef(Reference(ref_value.clone()));
                    replace(local_ref, new_local_ref);
                    Ok(Value::reference(Reference(ref_value)))
                }
            }
        } else {
            Err(VMInvariantViolation::IndexOutOfBounds(
                IndexKind::LocalPool,
                idx,
                self.0.len(),
            ))
        }
    }

    pub fn equals(&self, other: &Locals) -> bool {
        if self.0.len() != other.0.len() {
            return false;
        }
        for (a, b) in self.0.iter().zip(&other.0) {
            match a.equals(b) {
                Ok(res) => {
                    if !res {
                        return false;
                    }
                }
                Err(_) => return false,
            }
        }
        true
    }
}

impl Value {
    /// Serialize this value using `SimpleSerializer`.
    pub fn simple_serialize(&self) -> Option<Vec<u8>> {
        SimpleSerializer::<Vec<u8>>::serialize(self).ok()
    }

    /// Deserialize this value using `SimpleDeserializer` and a provided struct definition.
    pub fn simple_deserialize(blob: &[u8], resource: StructDef) -> VMRuntimeResult<Value> {
        let mut deserializer = SimpleDeserializer::new(blob);
        deserialize_struct(&mut deserializer, &resource)
    }
}

fn deserialize_struct(
    deserializer: &mut SimpleDeserializer,
    struct_def: &StructDef,
) -> VMRuntimeResult<Value> {
    let mut s_vals: Vec<Value> = Vec::new();
    for field_type in struct_def.field_definitions() {
        match field_type {
            Type::Bool => {
                if let Ok(b) = deserializer.decode_bool() {
                    s_vals.push(Value::bool(b));
                } else {
                    return Err(VMRuntimeError {
                        loc: Location::new(),
                        err: VMErrorKind::DataFormatError,
                    });
                }
            }
            Type::U64 => {
                if let Ok(val) = deserializer.decode_u64() {
                    s_vals.push(Value::u64(val));
                } else {
                    return Err(VMRuntimeError {
                        loc: Location::new(),
                        err: VMErrorKind::DataFormatError,
                    });
                }
            }
            Type::String => {
                if let Ok(bytes) = deserializer.decode_variable_length_bytes() {
                    if let Ok(s) = String::from_utf8(bytes) {
                        s_vals.push(Value::string(s));
                        continue;
                    }
                }
                return Err(VMRuntimeError {
                    loc: Location::new(),
                    err: VMErrorKind::DataFormatError,
                });
            }
            Type::ByteArray => {
                if let Ok(bytes) = deserializer.decode_variable_length_bytes() {
                    s_vals.push(Value::byte_array(ByteArray::new(bytes)));
                    continue;
                }
                return Err(VMRuntimeError {
                    loc: Location::new(),
                    err: VMErrorKind::DataFormatError,
                });
            }
            Type::Address => {
                if let Ok(bytes) = deserializer.decode_variable_length_bytes() {
                    if let Ok(addr) = AccountAddress::try_from(bytes) {
                        s_vals.push(Value::address(addr));
                        continue;
                    }
                }
                return Err(VMRuntimeError {
                    loc: Location::new(),
                    err: VMErrorKind::DataFormatError,
                });
            }
            Type::Struct(s_fields) => {
                if let Ok(s) = deserialize_struct(deserializer, s_fields) {
                    s_vals.push(s);
                } else {
                    return Err(VMRuntimeError {
                        loc: Location::new(),
                        err: VMErrorKind::DataFormatError,
                    });
                }
            }
            Type::Reference(_) => {
                return Err(VMRuntimeError {
                    loc: Location::new(),
                    err: VMErrorKind::InvalidData,
                })
            }
            Type::MutableReference(_) => {
                return Err(VMRuntimeError {
                    loc: Location::new(),
                    err: VMErrorKind::InvalidData,
                })
            }
        }
    }
    Ok(Value::struct_(Struct::new(s_vals)))
}

impl CanonicalSerialize for Value {
    fn serialize(&self, serializer: &mut impl CanonicalSerializer) -> Result<()> {
        match &self.0 {
            ValueImpl::U64(val) => {
                serializer.encode_u64(*val)?;
            }
            ValueImpl::Address(addr) => {
                // TODO: this is serializing as a vector but we want just raw bytes
                // however the AccountAddress story is a bit difficult to work with right now
                serializer.encode_variable_length_bytes(addr.as_ref())?;
            }
            ValueImpl::Bool(b) => {
                serializer.encode_bool(*b)?;
            }
            ValueImpl::String(s) => {
                // TODO: must define an api for canonical serializations of string.
                // Right now we are just using Rust to serialize the string
                serializer.encode_variable_length_bytes(s.as_bytes())?;
            }
            ValueImpl::Struct(vals) => {
                for mut_val in &vals.0 {
                    mut_val.peek().serialize(serializer)?;
                }
            }
            ValueImpl::ByteArray(bytearray) => {
                serializer.encode_variable_length_bytes(bytearray.as_bytes())?;
            }
            _ => unreachable!("invalid type to serialize"),
        }
        Ok(())
    }
}
