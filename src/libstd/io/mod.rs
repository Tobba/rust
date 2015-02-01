// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Traits, helpers, and type definitions for core I/O functionality.
//!
//! > **NOTE**: This module is very much a work in progress and is under active
//! > development. At this time it is still recommended to use the `old_io`
//! > module while the details of this module shake out.

#![unstable = "this new I/O module is still under active deveopment and APIs \
               are subject to tweaks fairly regularly"]

use core::prelude::*;

use borrow::ByRef;
use core::io as core_io;
use error::FromError;
use fmt;
use mem;
use slice;
use vec::Vec;

pub use core::io::{Read, Write, Seek, BufferedRead};
pub use core::io::{EndOfFile, SeekPos, NegativeSeek};
pub use core::io::{Cursor, sink, Sink, empty, Empty, repeat, Repeat, copy};
pub use core::io::{Tee, Bytes, Take, Chain, Broadcast, MapErr};
pub use core::io::{Chars, CharsError};

pub mod prelude;

const DEFAULT_BUF_SIZE: usize = 64 * 1024;

/// Extension methods for all instances of `Read`, typically imported through
/// `std::io::prelude::*`.
pub trait ReadExt: Read + Sized {
    /// Read all remaining bytes in this source, placing them into `buf`.
    ///
    /// This function will continuously invoke `read` until `Ok(0)` or an error
    /// is reached, at which point this function will immediately return.
    ///
    /// This function will only successfully return if an invocation of `Ok(0)`
    /// succeeds at which point all bytes have been read into `buf`.
    ///
    /// # Errors
    ///
    /// If a read error is encountered then this function immediately returns.
    /// Any bytes which have already been read will be present in `buf`.
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> Result<(), Self::Err> {
        loop {
            let cur_len = buf.len();
            if buf.capacity() == cur_len {
                buf.reserve(DEFAULT_BUF_SIZE);
            }
            let n = {
                let buf = unsafe {
                    let base = buf.as_mut_ptr().offset(cur_len as isize);
                    let len = buf.capacity() - cur_len;
                    slice::from_raw_mut_buf(mem::copy_lifetime(buf, &base), len)
                };
                // Our buffer we're passing down to `read` is uninitialized data
                // (the end of a `Vec`) but the read operation will be *much*
                // faster if we don't have to zero it out. In order to prevent
                // LLVM from generating an `undef` value by reading from this
                // uninitialized memory, we force LLVM to think it's initialized
                // by sending it through a black box. This should prevent actual
                // undefined behavior after optimizations.
                black_box(&buf);
                try!(self.read(buf))
            };
            if n == 0 { return Ok(()) }
            unsafe { buf.set_len(cur_len + n) }
        }

        // Semi-hack used to prevent LLVM from retaining any assumptions about
        // `dummy` over this function call
        fn black_box<T>(dummy: T) {
            unsafe { asm!("" : : "r"(&dummy)) }
        }
    }

    /// Create a "by reference" adaptor for this instance of `Read`.
    ///
    /// The returned adaptor also implements `Read` and will simply borrow this
    /// current reader.
    fn by_ref(&mut self) -> ByRef<Self> {
        core_io::ReadExt::by_ref(self)
    }

    /// Create an adaptor which will transform errors to another type.
    ///
    /// The returned reader will transform errors of type `Self::Err` to `E`
    /// via the `FromError` trait.
    fn map_err<Err, F: FnMut(Self::Err) -> Err>(self, mapper: F) -> MapErr<Self, Err, F> {
        core_io::ReadExt::map_err(self, mapper)
    }

    /// Transform this `Read` instance to an `Iterator` over its bytes.
    ///
    /// The returned type implements `Iterator` where the `Item` is `Result<u8,
    /// R::Err>`.  The yielded item is `Ok` if a byte was successfully read and
    /// `Err` otherwise for I/O errors. EOF is mapped to returning `None` for
    /// this iterator.
    fn bytes(self) -> Bytes<Self> {
        core_io::ReadExt::bytes(self)
    }

    /// Transform this `Read` instance to an `Iterator` over `char`s.
    ///
    /// This adaptor will attempt to interpret this reader as an UTF-8 encoded
    /// sequence of characters. The returned iterator will return `None` once
    /// EOF is reached for this reader (and it's not in the middle of decoding a
    /// character). Otherwise each element yielded will be a `Result<char, E>`
    /// where `E` may contain information about what I/O error occurred or where
    /// decoding failed.
    ///
    /// Currently this adaptor will discard intermediate data read, and should
    /// be avoided if this is not desired.
    #[unstable = "the error semantics of the returned structure are uncertain"]
    fn chars(self) -> Chars<Self> {
        core_io::ReadExt::chars(self)
    }

    /// Create an adaptor which will chain this stream with another.
    ///
    /// The returned instance of `Read` will yield all this object's bytes
    /// until EOF is reached. Afterwards the bytes of `next` will be yielded
    /// infinitely.
    fn chain<R: Read, Err=Self::Err>(self, next: R) -> Chain<Self, R, Err>
	where Err: FromError<Self::Err>,
		  Err: FromError<R::Err>
    {
		  
        core_io::ReadExt::chain(self, next)
    }

    /// Create an adaptor which will read at most `limit` bytes from it.
    ///
    /// This function returns a new instance of `Read` which will read at most
    /// `limit` bytes, after which it will always return EOF (`Ok(0)`). Any
    /// read errors will not count towards the number of bytes read and future
    /// calls to `read` may succeed.
    fn take(self, limit: u64) -> Take<Self> {
        core_io::ReadExt::take(self, limit)
    }

    /// Creates a reader adaptor which will write all read data into the given
    /// output stream.
    ///
    /// Whenever the returned `Read` instance is read it will write the read
    /// data to `out`. The current semantics of this implementation imply that
    /// a `write` error will not report how much data was initially read.
    #[unstable = "the error semantics of the returned structure are uncertain"]
    fn tee<W: Write, Err=Self::Err>(self, out: W) -> Tee<Self, W, Err>
        where Err: FromError<Self::Err>,
              Err: FromError<W::Err>,
              Err: FromError<EndOfFile>
    {
        core_io::ReadExt::tee(self, out)
    }
}

impl<T: Read> ReadExt for T {}

/// Extension methods for all instances of `Write`, typically imported through
/// `std::io::prelude::*`.
pub trait WriteExt: Write + Sized {
    /// Attempts to write an entire buffer into this write.
    ///
    /// This method will continuously call `write` while there is more data to
    /// write. This method will not return until the entire buffer has been
    /// successfully written or an error occurs. The first error generated from
    /// this method will be returned.
    ///
    /// # Errors
    ///
    /// This function will return the first error that `write` returns.
    #[unstable = "this function loses information about intermediate writes"]
    fn write_all(&mut self, buf: &[u8]) -> Result<(), Self::Err>
        where Self::Err: FromError<EndOfFile>
    {
        core_io::WriteExt::write_all(self, buf)
    }

    /// Writes a formatted string into this writer, returning any error
    /// encountered.
    ///
    /// This method is primarily used to interface with the `format_args!`
    /// macro, but it is rare that this should explicitly be called. The
    /// `write!` macro should be favored to invoke this method instead.
    ///
    /// This function internally uses the `write_all` method on this trait and
    /// hence will continuously write data so long as no errors are received.
    /// This also means that partial writes are not indicated in this signature.
    ///
    /// # Errors
    ///
    /// This function will return any I/O error reported while formatting.
    #[unstable = "this function loses information about intermediate writes"]
    fn write_fmt(&mut self, fmt: fmt::Arguments) -> Result<(), Self::Err>
        where Self::Err: FromError<EndOfFile>
    {
        core_io::WriteExt::write_fmt(self, fmt)
    }

    /// Create a "by reference" adaptor for this instance of `Write`.
    ///
    /// The returned adaptor also implements `Write` and will simply borrow this
    /// current writer.
    fn by_ref(&mut self) -> ByRef<Self> {
        core_io::WriteExt::by_ref(self)
    }

    /// Create an adaptor which will transform errors to another type.
    ///
    /// The returned writer will transform errors of type `Self::Err` to `E`
    /// via the `FromError` trait.
    fn map_err<Err, F: FnMut(Self::Err) -> Err>(self, mapper: F) -> MapErr<Self, Err, F> {
        core_io::WriteExt::map_err(self, mapper)
    }

    /// Creates a new writer which will write all data to both this writer and
    /// another writer.
    ///
    /// All data written to the returned writer will both be written to `self`
    /// as well as `other`. Note that the error semantics of the current
    /// implementation do not precisely track where errors happen. For example
    /// an error on the second call to `write` will not report that the first
    /// call to `write` succeeded.
    #[unstable = "the error semantics of the returned structure are uncertain"]
    fn broadcast<W: Write, Err=Self::Err>(self, other: W) -> Broadcast<Self, W, Err>
        where Err: FromError<Self::Err>,
              Err: FromError<W::Err>,
              Err: FromError<EndOfFile>
    {
        core_io::WriteExt::broadcast(self, other)
    }
}

impl<T: Write> WriteExt for T {}
