// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Core I/O primitives (basis of std::io)

use prelude::*;

use borrow::ByRef;
use cmp;
use error::{FromError, Error};
use fmt;
use str;

pub use self::util::{copy, empty, Empty, repeat, Repeat, sink, Sink};
pub use self::mem::{Cursor, NegativeSeek};

mod util;
mod mem;
pub mod prelude;

/// A trait for objects which are byte-oriented sources.
///
/// Readers are defined by one method, `read`. Each call to `read` will attempt
/// to pull bytes from this source into a provided buffer.
///
/// Readers are intended to be composable with one another. Many objects
/// throughout the I/O and related libraries take and provide types which
/// implement the `Read` trait.
pub trait Read {
    /// The type of errors returned from the methods on this trait.
    type Err;

    /// Pull some bytes from this source into the specified buffer, returning
    /// how many bytes were read.
    ///
    /// This function does not provide any guarantees about whether it blocks
    /// waiting for data, but if an object needs to block for a read but cannot
    /// it will typically signal this via an `Err` return value.
    ///
    /// If the return value of this method is `Ok(n)`, then it must be
    /// guaranteed that `0 <= n <= buf.len()`. If `n` is `0` then it indicates
    /// that this reader as reached "end of file" and will likely no longer be
    /// able to produce more bytes, but this is not guaranteed, however. A
    /// nonzero `n` value indicates that the buffer `buf` has been filled in
    /// with `n` bytes of data from this source.
    ///
    /// No guarantees are provided about the contents of `buf` when this
    /// function is called, implementations cannot rely on any property of the
    /// contents of `buf` being true.
    ///
    /// # Errors
    ///
    /// If this function encounters any form of I/O or other error, an error
    /// variant will be returned. If an error is returned then it is guaranteed
    /// that no bytes were read successfully.
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Err>;
}

#[allow(missing_docs)] // docs on std::io::ReadExt
pub trait ReadExt: Read + Sized {
    fn by_ref(&mut self) -> ByRef<Self> {
        ByRef { inner: self }
    }
    fn map_err<E: FromError<Self::Err>>(self) -> MapErr<Self, E> {
        MapErr { inner: self }
    }
    fn bytes(self) -> Bytes<Self> {
        Bytes { inner: self }
    }
    fn chars(self) -> Chars<Self> {
        Chars { inner: self }
    }
    fn chain<R: Read<Err=Self::Err>>(self, next: R) -> Chain<Self, R> {
        Chain { first: self, second: next, done_first: false }
    }
    fn take(self, limit: u64) -> Take<Self> {
        Take { inner: self, limit: limit }
    }
    fn tee<W: Write<Err=Self::Err>>(self, out: W) -> Tee<Self, W>
        where W::Err: FromError<EndOfFile>
    {
        Tee { reader: self, writer: out }
    }
}

impl<T: Read> ReadExt for T {}

/// A trait for objects which are byte-oriented sink.
///
/// Writers are defined by one method, `write`. This function will attempt to
/// write some data into the object, returning how many bytes were successfully
/// written.
///
/// Another commonly overridden method is the `flush` method for writers such as
/// buffered writers.
///
/// Writers are intended to be composable with one another. Many objects
/// throughout the I/O and related libraries take and provide types which
/// implement the `Write` trait.
pub trait Write {
    /// The type of errors returned from the methods on this trait.
    type Err;

    /// Write a buffer into this object, returning how many bytes were read.
    ///
    /// This function will attempt to write the entire contents of `buf`, but
    /// the entire write may not succeed, or the write may also generate an
    /// error. A call to `write` represents *at most one* attempt to write to
    /// any wrapped object.
    ///
    /// Calls to `write` are not guaranteed to block waiting for data to be
    /// written, and a write which would otherwise block is indicated through an
    /// `Err` variant.
    ///
    /// If the return value is `Ok(n)` then it must be guaranteed that
    /// `0 <= n <= buf.len()`. A return value of `0` typically means that the
    /// underlying object is no longer able to accept bytes and will likely not
    /// be able to in the future as well, or that the buffer provided is empty.
    ///
    /// # Errors
    ///
    /// Each call to `write` may generate an I/O error indicating that the
    /// operation could not be completed. If an error is returned then no bytes
    /// in the buffer were successfully written to this writer.
    ///
    /// It is **not** considered an error if the entire buffer could not be
    /// written to this writer.
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Err>;

    /// Flush this output stream, ensuring that all intermediately buffered
    /// contents reach their destination.
    ///
    /// This is by default a no-op and implementers of the `Write` trait should
    /// decide whether their stream needs to be buffered or not.
    fn flush(&mut self) -> Result<(), Self::Err> { Ok(()) }
}

/// An error which is used as a starting point to create new errors in
/// `write_all`.
///
/// This error is converted to `Self::Err` and is used to signify that the end
/// of a stream has been reached and no more bytes can be written.
#[derive(Copy, Clone)]
pub struct EndOfFile;

#[allow(missing_docs)] // docs in std::io
pub trait WriteExt: Write + Sized {
    fn write_all(&mut self, mut buf: &[u8]) -> Result<(), Self::Err>
        where Self::Err: FromError<EndOfFile>
    {
        while buf.len() > 0 {
            let n = try!(self.write(buf));
            if n == 0 { return Err(FromError::from_error(EndOfFile)) }
            buf = &buf[n..];
        }
        Ok(())
    }
    fn write_fmt(&mut self, fmt: fmt::Arguments) -> Result<(), Self::Err>
        where Self::Err: FromError<EndOfFile>
    {
        // Create a shim which translates a Writer to a fmt::Writer and saves
        // off I/O errors. instead of discarding them
        struct Adaptor<'a, T: 'a, E> {
            inner: &'a mut T,
            error: Result<(), E>,
        }

        impl<'a, T: Write> fmt::Writer for Adaptor<'a, T, T::Err>
            where T::Err: FromError<EndOfFile>
        {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                match self.inner.write_all(s.as_bytes()) {
                    Ok(()) => Ok(()),
                    Err(e) => {
                        self.error = Err(e);
                        Err(fmt::Error)
                    }
                }
            }
        }

        let mut output = Adaptor { inner: self, error: Ok(()) };
        match fmt::write(&mut output, fmt) {
            Ok(()) => Ok(()),
            Err(..) => output.error
        }
    }
    fn by_ref(&mut self) -> ByRef<Self> {
        ByRef { inner: self }
    }
    fn map_err<E: FromError<Self::Err>>(self) -> MapErr<Self, E> {
        MapErr { inner: self }
    }
    fn broadcast<W: Write<Err=Self::Err>>(self, other: W) -> Broadcast<Self, W>
        where Self::Err: FromError<EndOfFile>
    {
        Broadcast { first: self, second: other }
    }
}

impl<T: Write> WriteExt for T {}

/// An object implementing `Seek` internally has some form of cursor which can
/// be moved within a stream of bytes.
///
/// The stream typically has a fixed size, allowing seeking relative to either
/// end or the current offset.
pub trait Seek {
    /// The type of errors returned from the methods on this trait.
    type Err;

    /// Seek to an offset, in bytes, in a stream
    ///
    /// A seek beyond the end of a stream is allowed, but seeking before offset
    /// 0 is an error.
    ///
    /// Seeking past the end of the stream does not modify the underlying
    /// stream, but the next write may cause the previous data to be filled in
    /// with a bit pattern.
    ///
    /// This method returns the new position within the stream if the seek
    /// operation completed successfully.
    ///
    /// # Errors
    ///
    /// Seeking to a negative offset is considered an error
    fn seek(&mut self, pos: SeekPos) -> Result<u64, Self::Err>;
}

/// Enumeration of possible methods to seek within an I/O object.
#[derive(Copy, PartialEq, Eq, Clone, Show)]
pub enum SeekPos {
    /// Set the offset to the provided number of bytes.
    FromStart(u64),

    /// Set the offset to the size of this object plus the specified number of
    /// bytes.
    ///
    /// It is possible to seek beyond the end of an object, but is an error to
    /// seek before byte 0.
    FromEnd(i64),

    /// Set the offset to the current position plus the specified number of
    /// bytes.
    ///
    /// It is possible to seek beyond the end of an object, but is an error to
    /// seek before byte 0.
    FromCur(i64),
}

/// A Buffer is a type of reader which has some form of internal buffering to
/// allow certain kinds of reading operations to be more optimized than others.
///
/// This type extends the `Read` trait with a few methods that are not
/// possible to reasonably implement with purely a read interface.
pub trait BufferedRead: Read {
    /// Fills the internal buffer of this object, returning the buffer contents.
    ///
    /// Note that none of the contents will be "read" in the sense that later
    /// calling `read` may return the same contents.
    ///
    /// The `consume` function must be called with the number of bytes that are
    /// consumed from this buffer returned to ensure that the bytes are never
    /// returned twice.
    ///
    /// An empty buffer returned indicates that the stream has reached EOF.
    ///
    /// # Error
    ///
    /// This function will return an I/O error if the underlying reader was
    /// read, but returned an error.
    fn fill_buf(&mut self) -> Result<&[u8], Self::Err>;

    /// Tells this buffer that `amt` bytes have been consumed from the buffer,
    /// so they should no longer be returned in calls to `read`.
    fn consume(&mut self, amt: usize);
}

impl<'a, R: Read> Read for ByRef<'a, R> {
    type Err = R::Err;
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, R::Err> {
        self.inner.read(buf)
    }
}

impl<'a, R: Read> Read for &'a mut R {
    type Err = R::Err;
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, R::Err> {
        Read::read(*self, buf)
    }
}

impl<'a, W: Write> Write for ByRef<'a, W> {
    type Err = W::Err;
    fn write(&mut self, buf: &[u8]) -> Result<usize, W::Err> {
        self.inner.write(buf)
    }
    fn flush(&mut self) -> Result<(), W::Err> {
        self.inner.flush()
    }
}

impl<'a, W: Write> Write for &'a mut W {
    type Err = W::Err;
    fn write(&mut self, buf: &[u8]) -> Result<usize, W::Err> {
        Write::write(*self, buf)
    }
    fn flush(&mut self) -> Result<(), W::Err> {
        Write::flush(*self)
    }
}

/// A `Write` adaptor which will write data to multiple locations.
///
/// For more information, see `WriteExt::broadcast`.
pub struct Broadcast<T, U> {
    first: T,
    second: U,
}

impl<T: Write, U: Write<Err=T::Err>> Write for Broadcast<T, U>
    where T::Err: FromError<EndOfFile>
{
    type Err = T::Err;

    fn write(&mut self, data: &[u8]) -> Result<usize, T::Err> {
        let n = try!(self.first.write(data));
        // TODO: what if the write fails? (we wrote something)
        try!(self.second.write_all(&data[..n]));
        Ok(n)
    }

    fn flush(&mut self) -> Result<(), T::Err> {
        self.first.flush().and(self.second.flush())
    }
}

/// Adaptor to transform errors of one type to another.
///
/// For more information see `ReadExt::map_err` or `WriteExt::map_err`.
pub struct MapErr<T, E> {
    inner: T,
}

impl<T: Read, E: FromError<T::Err>> Read for MapErr<T, E> {
    type Err = E;
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, E> {
        self.inner.read(buf).map_err(FromError::from_error)
    }
}

impl<T: Write, E: FromError<T::Err>> Write for MapErr<T, E> {
    type Err = E;
    fn write(&mut self, buf: &[u8]) -> Result<usize, E> {
        self.inner.write(buf).map_err(FromError::from_error)
    }
    fn flush(&mut self) -> Result<(), E> {
        self.inner.flush().map_err(FromError::from_error)
    }
}

/// Adaptor to chain together two instances of `Read`.
///
/// For more information, see `ReadExt::chain`.
pub struct Chain<T, U> {
    first: T,
    second: U,
    done_first: bool,
}

impl<T: Read, U: Read<Err=T::Err>> Read for Chain<T, U> {
    type Err = T::Err;
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, T::Err> {
        if !self.done_first {
            match try!(self.first.read(buf)) {
                0 => { self.done_first = true; }
                n => return Ok(n),
            }
        }
        self.second.read(buf)
    }
}

/// Reader adaptor which limits the bytes read from an underlying reader.
///
/// For more information, see `ReadExt::take`.
pub struct Take<T> {
    inner: T,
    limit: u64,
}

impl<T: Read> Read for Take<T> {
    type Err = T::Err;
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, T::Err> {
        let max = cmp::min(buf.len() as u64, self.limit);
        let buf = &mut buf[..(max as usize)];
        let n = try!(self.inner.read(buf));
        self.limit -= n as u64;
        Ok(n)
    }
}

/// An adaptor which will emit all read data to a specified writer as well.
///
/// For more information see `ReadExt::tee`
pub struct Tee<R, W> {
    reader: R,
    writer: W,
}

impl<R: Read, W: Write<Err=R::Err>> Read for Tee<R, W>
    where W::Err: FromError<EndOfFile>
{
    type Err = R::Err;

    fn read(&mut self, buf: &mut [u8]) -> Result<usize, R::Err> {
        let n = try!(self.reader.read(buf));
        // TODO: what if the write fails? (we read something)
        try!(self.writer.write_all(&buf[..n]));
        Ok(n)
    }
}

/// A bridge from implementations of `Read` to an `Iterator` of `u8`.
///
/// See `ReadExt::bytes` for more information.
pub struct Bytes<R> {
    inner: R,
}

impl<R: Read> Iterator for Bytes<R> {
    type Item = Result<u8, R::Err>;

    fn next(&mut self) -> Option<Result<u8, R::Err>> {
        let mut buf = [0];
        match self.inner.read(&mut buf) {
            Ok(0) => None,
            Ok(..) => Some(Ok(buf[0])),
            Err(e) => Some(Err(e)),
        }
    }
}

/// A bridge from implementations of `Read` to an `Iterator` of `char`.
///
/// See `ReadExt::chars` for more information.
pub struct Chars<R> {
    inner: R,
}

/// An enumeration of possible errors that can be generated from the `Chars`
/// adapter.
#[derive(PartialEq, Clone, Show)]
pub enum CharsError<E> {
    /// Variant representing that the underlying stream was read successfully
    /// but it did not contain valid utf8 data.
    NotUtf8,

    /// Variant representing that an I/O error occurred.
    Other(E),
}

impl<R: Read> Iterator for Chars<R> {
    type Item = Result<char, CharsError<R::Err>>;

    fn next(&mut self) -> Option<Result<char, CharsError<R::Err>>> {
        let mut buf = [0];
        let first_byte = match self.inner.read(&mut buf) {
            Ok(0) => return None,
            Ok(..) => buf[0],
            Err(e) => return Some(Err(CharsError::Other(e))),
        };
        let width = str::utf8_char_width(first_byte);
        if width == 1 { return Some(Ok(first_byte as char)) }
        if width == 0 { return Some(Err(CharsError::NotUtf8)) }
        let mut buf = [first_byte, 0, 0, 0];
        {
            let mut start = 1;
            while start < width {
                match self.inner.read(&mut buf[start..width]) {
                    Ok(0) => return Some(Err(CharsError::NotUtf8)),
                    Ok(n) if n == width - start => break,
                    Ok(n) => start += n,
                    Err(e) => return Some(Err(CharsError::Other(e))),
                }
            }
        }
        Some(match str::from_utf8(&buf[..width]).ok() {
            Some(s) => Ok(s.char_at(0)),
            None => Err(CharsError::NotUtf8),
        })
    }
}

impl<E: Error> Error for CharsError<E> {
    fn description(&self) -> &str {
        match *self {
            CharsError::NotUtf8 => "invalid utf8 encoding",
            CharsError::Other(ref e) => e.description(),
        }
    }
    fn cause(&self) -> Option<&Error> {
        match *self {
            CharsError::NotUtf8 => None,
            CharsError::Other(ref e) => e.cause(),
        }
    }
}

impl<E: fmt::Display> fmt::Display for CharsError<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            CharsError::NotUtf8 => {
                "byte stream did not contain valid utf8".fmt(f)
            }
            CharsError::Other(ref e) => e.fmt(f),
        }
    }
}
