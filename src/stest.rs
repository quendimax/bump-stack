// A list of platforms where I could test it
#![cfg(any(
    all(target_os = "linux", target_arch = "x86_64"),
    all(target_os = "macos", target_arch = "aarch64")
))]

//! Static tests for the `Stack` struct.

use super::*;
use util::const_assert_eq;

struct T9 {
    _m1: u64, // 8
    _m2: u8,  // 1
}

struct T35 {
    _m1: u16,      // 2
    _m2: u64,      // 8
    _m3: u32,      // 4
    _m4: [u8; 16], // 16
    _m5: u32,      // 4
    _m6: u8,       // 1
}

struct T83 {
    _m1: u16,       // 2
    _m2: u64,       // 8
    _m3: u32,       // 4
    _m4: [u32; 16], // 64
    _m5: u32,       // 4
    _m6: u8,        // 1
}

// u8, MIN_ALIGN=1
const_assert_eq!(Stack::<u8>::ELEMENT_ALIGN, 1);
const_assert_eq!(Stack::<u8>::ELEMENT_SIZE, 1);
const_assert_eq!(Stack::<u8>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<u8>::FOOTER_SIZE, 48);
const_assert_eq!(Stack::<u8>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<u8>::CHUNK_MIN_SIZE, 64);
const_assert_eq!(Stack::<u8>::CHUNK_FIRST_SIZE, 512);
const_assert_eq!(Stack::<u8>::CHUNK_MAX_SIZE, 4 << 30);

// u16, MIN_ALIGN=1
const_assert_eq!(Stack::<u16>::ELEMENT_ALIGN, 2);
const_assert_eq!(Stack::<u16>::ELEMENT_SIZE, 2);
const_assert_eq!(Stack::<u16>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<u16>::FOOTER_SIZE, 48);
const_assert_eq!(Stack::<u16>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<u16>::CHUNK_MIN_SIZE, 64);
const_assert_eq!(Stack::<u16>::CHUNK_FIRST_SIZE, 512);
const_assert_eq!(Stack::<u16>::CHUNK_MAX_SIZE, 4 << 30);

// u32, MIN_ALIGN=1
const_assert_eq!(Stack::<u32>::ELEMENT_ALIGN, 4);
const_assert_eq!(Stack::<u32>::ELEMENT_SIZE, 4);
const_assert_eq!(Stack::<u32>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<u32>::FOOTER_SIZE, 48);
const_assert_eq!(Stack::<u32>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<u32>::CHUNK_MIN_SIZE, 64);
const_assert_eq!(Stack::<u32>::CHUNK_FIRST_SIZE, 512);
const_assert_eq!(Stack::<u32>::CHUNK_MAX_SIZE, 4 << 30);

// u64, MIN_ALIGN=1
const_assert_eq!(Stack::<u64>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<u64>::ELEMENT_SIZE, 8);
const_assert_eq!(Stack::<u64>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<u64>::FOOTER_SIZE, 48);
const_assert_eq!(Stack::<u64>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<u64>::CHUNK_MIN_SIZE, 64);
const_assert_eq!(Stack::<u64>::CHUNK_FIRST_SIZE, 512);
const_assert_eq!(Stack::<u64>::CHUNK_MAX_SIZE, 4 << 30);

// T9, MIN_ALIGN=1
const_assert_eq!(Stack::<T9>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T9>::ELEMENT_SIZE, 16);
const_assert_eq!(Stack::<T9>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<T9>::FOOTER_SIZE, 48);
const_assert_eq!(Stack::<T9>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<T9>::CHUNK_MIN_SIZE, 128);
const_assert_eq!(Stack::<T9>::CHUNK_FIRST_SIZE, 512);
const_assert_eq!(Stack::<T9>::CHUNK_MAX_SIZE, 4 << 30);

// T35, MIN_ALIGN=1
const_assert_eq!(Stack::<T35>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T35>::ELEMENT_SIZE, 40);
const_assert_eq!(Stack::<T35>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<T35>::FOOTER_SIZE, 48);
const_assert_eq!(Stack::<T35>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<T35>::CHUNK_MIN_SIZE, 128);
const_assert_eq!(Stack::<T35>::CHUNK_FIRST_SIZE, 512);
const_assert_eq!(Stack::<T35>::CHUNK_MAX_SIZE, 4 << 30);

// T83, MIN_ALIGN=1
const_assert_eq!(Stack::<T83>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T83>::ELEMENT_SIZE, 88);
const_assert_eq!(Stack::<T83>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<T83>::FOOTER_SIZE, 48);
const_assert_eq!(Stack::<T83>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<T83>::CHUNK_MIN_SIZE, 256);
const_assert_eq!(Stack::<T83>::CHUNK_FIRST_SIZE, 1024);
const_assert_eq!(Stack::<T83>::CHUNK_MAX_SIZE, 4 << 30);
