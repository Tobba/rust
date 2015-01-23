// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The `Void` type, an uninhabited enumeration

use prelude::*;

use fmt;
use error::{Error, FromError};

/// An uninhabited enumeration useful for representing values that cannot exist
/// at runtime.
#[derive(Copy)]
pub enum Void {}

impl<E: Error> FromError<Void> for E {
    fn from_error(v: Void) -> E {
        match v {}
    }
}

impl PartialEq for Void {
    fn eq(&self, _other: &Void) -> bool {
        match *self {}
    }
}

impl Clone for Void {
    fn clone(&self) -> Void {
        match *self {}
    }
}

impl fmt::Debug for Void {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
        match *self {}
    }
}
impl fmt::Display for Void {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
        match *self {}
    }
}
