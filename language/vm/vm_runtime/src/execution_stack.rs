// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    code_cache::module_cache::ModuleCache,
    frame::Frame,
    loaded_data::function::{FunctionRef, FunctionReference},
};
use std::{fmt, marker::PhantomData};
use vm::errors::*;
use vm_runtime_types::value::{Locals, Value};

pub struct ExecutionStack<'alloc, 'txn, P>
where
    'alloc: 'txn,
    P: ModuleCache<'alloc>,
{
    stack: Vec<Value>,
    function_stack: Vec<Frame<'txn, FunctionRef<'txn>>>,
    pub module_cache: P,

    // A execution stack will holds an instance of code cache for the lifetime of alloc.
    phantom: PhantomData<&'alloc ()>,
}

impl<'alloc, 'txn, P> ExecutionStack<'alloc, 'txn, P>
where
    'alloc: 'txn,
    P: ModuleCache<'alloc>,
{
    pub fn new(module_cache: P) -> Self {
        ExecutionStack {
            function_stack: vec![],
            stack: vec![],
            module_cache,
            phantom: PhantomData,
        }
    }

    pub fn push_call(&mut self, function: FunctionRef<'txn>) -> VMResult<()> {
        let mut locals = Locals::new(function.local_count());
        let arg_count = function.arg_count();
        for i in 0..arg_count {
            locals.store_loc(arg_count - i - 1, self.pop()?)?;
        }
        self.function_stack.push(Frame::new(function, locals));
        Ok(Ok(()))
    }

    pub fn pop_call(&mut self) -> VMResult<()> {
        self.function_stack
            .pop()
            .ok_or(VMInvariantViolation::EmptyCallStack)?;
        Ok(Ok(()))
    }

    pub fn top_frame(&self) -> Result<&Frame<'txn, FunctionRef<'txn>>, VMInvariantViolation> {
        Ok(self
            .function_stack
            .last()
            .ok_or(VMInvariantViolation::EmptyCallStack)?)
    }

    pub fn top_frame_mut(
        &mut self,
    ) -> Result<&mut Frame<'txn, FunctionRef<'txn>>, VMInvariantViolation> {
        Ok(self
            .function_stack
            .last_mut()
            .ok_or(VMInvariantViolation::EmptyCallStack)?)
    }

    pub fn is_call_stack_empty(&self) -> bool {
        self.function_stack.is_empty()
    }

    pub fn location(&self) -> Result<Location, VMInvariantViolation> {
        Ok(self.top_frame()?.into())
    }

    pub fn push(&mut self, value: Value) {
        self.stack.push(value)
    }

    pub fn peek(&self) -> Result<&Value, VMInvariantViolation> {
        Ok(self
            .stack
            .last()
            .ok_or(VMInvariantViolation::EmptyValueStack)?)
    }

    pub fn peek_at(&self, index: usize) -> Result<&Value, VMInvariantViolation> {
        let size = self.stack.len();
        Ok(self
            .stack
            .get(size - index - 1)
            .ok_or(VMInvariantViolation::EmptyValueStack)?)
    }

    pub fn pop(&mut self) -> Result<Value, VMInvariantViolation> {
        Ok(self
            .stack
            .pop()
            .ok_or(VMInvariantViolation::EmptyValueStack)?)
    }

    pub fn pop_as<T>(&mut self) -> VMResult<T>
    where
        Option<T>: From<Value>,
    {
        let top = self.pop()?.value_as();
        match top {
            Some(v) => Ok(Ok(v)),
            None => {
                Ok(Err(VMRuntimeError {
                    loc: self.location()?,
                    err: VMErrorKind::TypeError,
                }))
            }
        }
    }

    pub fn popn(&mut self, n: u16) -> Result<Vec<Value>, VMInvariantViolation> {
        let remaining_stack_size = self
            .stack
            .len()
            .checked_sub(n as usize)
            .ok_or(VMInvariantViolation::EmptyValueStack)?;
        let args = self.stack.split_off(remaining_stack_size);
        Ok(args)
    }

    pub fn call_stack_height(&self) -> usize {
        self.function_stack.len()
    }

    pub fn set_stack(&mut self, stack: Vec<Value>) {
        self.stack = stack;
    }

    pub fn get_value_stack(&self) -> &Vec<Value> {
        &self.stack
    }

    pub fn push_frame(&mut self, func: FunctionRef<'txn>) {
        self.function_stack.push(Frame::new(func, Locals::new(0)));
    }
}

impl<'alloc, 'txn, P> fmt::Debug for ExecutionStack<'alloc, 'txn, P>
where
    'alloc: 'txn,
    P: ModuleCache<'alloc>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Stack: {:?}", self.stack)?;
        writeln!(f, "Current Frames: {:?}", self.function_stack)
    }
}
