#![no_implicit_prelude]

use core::prelude::*;

use std::error::Error;
use std::io::prelude::*;
use std::io::{sink, empty, repeat, WriteAllError};
use std::fmt;

#[test]
fn sink_sinks() {
    let mut s = sink();
    assert_eq!(s.write(&[]), Ok(0));
    assert_eq!(s.write(&[0]), Ok(1));
    assert_eq!(s.write(&[0; 1024]), Ok(1024));
    assert_eq!(s.by_ref().write(&[0; 1024]), Ok(1024));
}

#[test]
fn empty_reads() {
    let mut e = empty();
    assert_eq!(e.read(&mut []), Ok(0));
    assert_eq!(e.read(&mut [0]), Ok(0));
    assert_eq!(e.read(&mut [0; 1024]), Ok(0));
    assert_eq!(e.by_ref().read(&mut [0; 1024]), Ok(0));
}

#[test]
fn repeat_repeats() {
    let mut r = repeat(4);
    let mut b = [0; 1024];
    assert_eq!(r.read(&mut b), Ok(1024));
    assert!(b.iter().all(|b| *b == 4));
}

#[test]
fn take_some_bytes() {
    assert_eq!(repeat(4).take(100).bytes().count(), 100);
    assert_eq!(repeat(4).take(100).bytes().next(), Some(Ok(4)));
    assert_eq!(repeat(1).take(10).chain(repeat(2).take(10)).bytes().count(), 20);
}

#[derive(PartialEq, Show)]
struct MyMemoryError;
impl WriteAllError for MyMemoryError {
    fn eof() -> MyMemoryError { MyMemoryError }
    fn interrupted(&self) -> bool { false }
}
impl Error for MyMemoryError {
    fn description(&self) -> &str { "foo" }
}
impl fmt::Display for MyMemoryError {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
        Ok(())
    }
}

#[test]
fn tee() {
    let mut buf = [0; 10];
    {
        let mut ptr: &mut [u8] = &mut buf;
        assert_eq!(repeat(4).map_err::<MyMemoryError>()
                            .tee((&mut ptr).map_err())
                            .take(5).read(&mut [0; 10]), Ok(5));
    }
    assert_eq!(buf, [4, 4, 4, 4, 4, 0, 0, 0, 0, 0]);
}

#[test]
fn broadcast() {
    let mut buf1 = [0; 10];
    let mut buf2 = [0; 10];
    {
        let mut ptr1: &mut [u8] = &mut buf1;
        let mut ptr2: &mut [u8] = &mut buf2;

        assert_eq!((&mut ptr1).map_err::<MyMemoryError>()
                             .broadcast((&mut ptr2).map_err())
                             .write(&[1, 2, 3]), Ok(3));
    }
    assert_eq!(buf1, buf2);
    assert_eq!(buf1, [1, 2, 3, 0, 0, 0, 0, 0, 0, 0]);
}

