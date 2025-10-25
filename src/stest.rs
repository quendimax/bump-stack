// I've tested it only on linux/x86_64
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

//! Static tests for the `Stack` struct.

use super::*;
use util::const_assert_eq;

struct T9 {
    _m1: u64, // 8
    _m2: u8,  // 1
}

struct T19 {
    _m1: u16, // 2
    _m2: u64, // 8
    _m3: u32, // 4
    _m4: u32, // 4
    _m5: u8,  // 1
}

// ELEMENT_ALIGN
const_assert_eq!(Stack::<u8, 1>::ELEMENT_ALIGN, 1);
const_assert_eq!(Stack::<u16, 1>::ELEMENT_ALIGN, 2);
const_assert_eq!(Stack::<u32, 1>::ELEMENT_ALIGN, 4);
const_assert_eq!(Stack::<u64, 1>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T9, 1>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T19, 1>::ELEMENT_ALIGN, 8);

const_assert_eq!(Stack::<u8, 2>::ELEMENT_ALIGN, 2);
const_assert_eq!(Stack::<u16, 2>::ELEMENT_ALIGN, 2);
const_assert_eq!(Stack::<u32, 2>::ELEMENT_ALIGN, 4);
const_assert_eq!(Stack::<u64, 2>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T9, 2>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T19, 2>::ELEMENT_ALIGN, 8);

const_assert_eq!(Stack::<u8, 4>::ELEMENT_ALIGN, 4);
const_assert_eq!(Stack::<u16, 4>::ELEMENT_ALIGN, 4);
const_assert_eq!(Stack::<u32, 4>::ELEMENT_ALIGN, 4);
const_assert_eq!(Stack::<u64, 4>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T9, 4>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T19, 4>::ELEMENT_ALIGN, 8);

const_assert_eq!(Stack::<u8, 8>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<u16, 8>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<u32, 8>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<u64, 8>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T9, 8>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T19, 8>::ELEMENT_ALIGN, 8);

// ELEMENT_SIZE
const_assert_eq!(Stack::<u8, 1>::ELEMENT_SIZE, 1);
const_assert_eq!(Stack::<u16, 1>::ELEMENT_SIZE, 2);
const_assert_eq!(Stack::<u32, 1>::ELEMENT_SIZE, 4);
const_assert_eq!(Stack::<u64, 1>::ELEMENT_SIZE, 8);
const_assert_eq!(Stack::<T9, 1>::ELEMENT_SIZE, 16);
const_assert_eq!(Stack::<T19, 1>::ELEMENT_SIZE, 24);

const_assert_eq!(Stack::<u8, 2>::ELEMENT_SIZE, 2);
const_assert_eq!(Stack::<u16, 2>::ELEMENT_SIZE, 2);
const_assert_eq!(Stack::<u32, 2>::ELEMENT_SIZE, 4);
const_assert_eq!(Stack::<u64, 2>::ELEMENT_SIZE, 8);
const_assert_eq!(Stack::<T9, 2>::ELEMENT_SIZE, 16);
const_assert_eq!(Stack::<T19, 2>::ELEMENT_SIZE, 24);

const_assert_eq!(Stack::<u8, 4>::ELEMENT_SIZE, 4);
const_assert_eq!(Stack::<u16, 4>::ELEMENT_SIZE, 4);
const_assert_eq!(Stack::<u32, 4>::ELEMENT_SIZE, 4);
const_assert_eq!(Stack::<u64, 4>::ELEMENT_SIZE, 8);
const_assert_eq!(Stack::<T9, 4>::ELEMENT_SIZE, 16);
const_assert_eq!(Stack::<T19, 4>::ELEMENT_SIZE, 24);

const_assert_eq!(Stack::<u8, 8>::ELEMENT_SIZE, 8);
const_assert_eq!(Stack::<u16, 8>::ELEMENT_SIZE, 8);
const_assert_eq!(Stack::<u32, 8>::ELEMENT_SIZE, 8);
const_assert_eq!(Stack::<u64, 8>::ELEMENT_SIZE, 8);
const_assert_eq!(Stack::<T9, 8>::ELEMENT_SIZE, 16);
const_assert_eq!(Stack::<T19, 8>::ELEMENT_SIZE, 24);

const_assert_eq!(Stack::<T19, 32>::ELEMENT_SIZE, 32);
const_assert_eq!(Stack::<T19, 128>::ELEMENT_SIZE, 128);
