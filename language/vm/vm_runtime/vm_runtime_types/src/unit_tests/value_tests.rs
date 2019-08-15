// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_simple_mutate() {
    let mut locals = Locals::new(1);
    locals
        .store_loc(0, Value::u64(1))
        .expect("Local 0 must be available");
    let loc_ref = locals.borrow_loc(0).expect("Local 0 must be available");
    loc_ref
        .value_as::<Reference>()
        .expect("Value must be a Reference")
        .write_value(Value::u64(2));

    assert!(locals
        .copy_loc(0)
        .expect("Local 0 must be available")
        .equals(&Value::u64(2))
        .expect("Equals must succeed"));
}

#[test]
fn test_cloned_value() {
    let mut locals = Locals::new(1);
    locals
        .store_loc(0, Value::u64(1))
        .expect("Local 0 must be available");
    let loc_copy = locals.copy_loc(0).expect("Local 0 must be available");

    let loc_ref = locals.borrow_loc(0).expect("Local 0 must be available");
    loc_ref
        .value_as::<Reference>()
        .expect("Value must be a Reference")
        .write_value(Value::u64(2));

    assert!(locals
        .copy_loc(0)
        .expect("Local 0 must be available")
        .equals(&Value::u64(2))
        .expect("Equals must succeed"));
    assert!(loc_copy
        .equals(&Value::u64(1))
        .expect("Equals must succeed"));
}

#[test]
fn test_cloned_references() {
    let mut locals = Locals::new(1);
    locals
        .store_loc(0, Value::u64(1))
        .expect("Local 0 must be available");

    let loc_ref = locals.borrow_loc(0).expect("Local 0 must be available");
    let loc_ref_clone = loc_ref.clone();

    loc_ref
        .value_as::<Reference>()
        .expect("Value must be a Reference")
        .write_value(Value::u64(2));

    assert!(locals
        .copy_loc(0)
        .expect("Local 0 must be available")
        .equals(&Value::u64(2))
        .expect("Equals must succeed"));
    assert!(loc_ref_clone
        .equals(&locals.borrow_loc(0).expect("Local 0 must be available"))
        .expect("Equals must succeed"));
}

#[test]
fn test_mutate_struct() {
    let mut locals = Locals::new(1);
    locals
        .store_loc(
            0,
            Value::struct_(Struct::new(vec![Value::u64(1), Value::u64(2)])),
        )
        .expect("Local 0 must be available");

    let loc_ref = locals.borrow_loc(0).expect("Local 0 must be available");
    let field_ref = loc_ref
        .value_as::<Reference>()
        .expect("Value must be a Reference")
        .borrow_field(1)
        .expect("Field must exist");

    field_ref
        .value_as::<Reference>()
        .unwrap()
        .write_value(Value::u64(3));

    let v_after = Value::struct_(Struct::new(vec![Value::u64(1), Value::u64(3)]));
    assert!(locals
        .borrow_loc(0)
        .expect("Local 0 must be available")
        .value_as::<Reference>()
        .expect("Must be a Reference")
        .copy_value()
        .expect("Must be a valid local")
        .equals(&v_after)
        .expect("Equals must succeed"));
}
