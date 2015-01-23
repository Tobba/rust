// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::prelude::*;

use core::io::prelude::*;
use core::io::{Cursor, NegativeSeek, SeekPos};
use core::iter::repeat;
use core::slice;
use core::void::Void;

use vec::Vec;

impl Read for Cursor<Vec<u8>> {
    type Err = Void;
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Void> {
        let pos = self.position();
        let n = {
            let inner = self.get_ref();
            if pos > inner.len() as u64 { return Ok(0) }
            let mut slice = &inner[(pos as usize)..];
            try!(slice.read(buf))
        };
        self.set_position(pos + n as u64);
        Ok(n)
    }
}

impl Seek for Cursor<Vec<u8>> {
    type Err = NegativeSeek;

    fn seek(&mut self, pos: SeekPos) -> Result<u64, NegativeSeek> {
        let old_pos = self.position();
        let new_pos = {
            let mut c = Cursor::new(&self.get_mut()[]);
            c.set_position(old_pos);
            try!(c.seek(pos))
        };
        self.set_position(new_pos);
        Ok(new_pos)
    }
}

impl Write for Vec<u8> {
    type Err = Void;

    fn write(&mut self, buf: &[u8]) -> Result<usize, Void> {
        self.push_all(buf);
        Ok(buf.len())
    }
}

impl Write for Cursor<Vec<u8>> {
    type Err = Void;

    fn write(&mut self, buf: &[u8]) -> Result<usize, Void> {
        let pos = self.position();
        let mut len = self.get_ref().len();
        if pos == len as u64 {
            self.get_mut().push_all(buf)
        } else {
            // Make sure the internal buffer is as least as big as where we
            // currently are
            let difference = pos as i64 - len as i64;
            if difference > 0 {
                self.get_mut().extend(repeat(0).take(difference as usize));
                len += difference as usize;
            }

            // Figure out what bytes will be used to overwrite what's currently
            // there (left), and what will be appended on the end (right)
            let cap = len - (pos as usize);
            let (left, right) = if cap <= buf.len() {
                (&buf[..cap], &buf[cap..])
            } else {
                let result: (_, &[_]) = (buf, &[]);
                result
            };

            // Do the necessary writes
            if left.len() > 0 {
                let dst = &mut self.get_mut()[(pos as usize)..];
                slice::bytes::copy_memory(dst, left);
            }
            if right.len() > 0 {
                self.get_mut().push_all(right);
            }
        }

        // Bump us forward
        self.set_position(pos + buf.len() as u64);
        Ok(buf.len())
    }
}
