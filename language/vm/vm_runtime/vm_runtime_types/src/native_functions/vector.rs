// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use super::dispatch::NativeReturnStatus;
use crate::value::Value;
use std::collections::VecDeque;

const LENGTH_COST: u64 = 30; // TODO: determine experimentally

#[allow(unreachable_code)]
pub fn native_length(_arguments: VecDeque<Value>) -> NativeReturnStatus {
    unimplemented!("Computing length of a vector collection");
    let cost = LENGTH_COST;
    let return_values = vec![Value::u64(0)];
    NativeReturnStatus::Success {
        cost,
        return_values,
    }
}
