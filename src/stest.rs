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
const_assert_eq!(Stack::<u8, 1>::ELEMENT_ALIGN, 1);
const_assert_eq!(Stack::<u8, 1>::ELEMENT_SIZE, 1);
const_assert_eq!(Stack::<u8, 1>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<u8, 1>::FOOTER_SIZE, 40);
const_assert_eq!(Stack::<u8, 1>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<u8, 1>::CHUNK_MIN_SIZE, 64);
const_assert_eq!(Stack::<u8, 1>::CHUNK_FIRST_SIZE, 512);
const_assert_eq!(Stack::<u8, 1>::CHUNK_MAX_SIZE, 0x400_0000_0000_0000);

// u16, MIN_ALIGN=1
const_assert_eq!(Stack::<u16, 1>::ELEMENT_ALIGN, 2);
const_assert_eq!(Stack::<u16, 1>::ELEMENT_SIZE, 2);
const_assert_eq!(Stack::<u16, 1>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<u16, 1>::FOOTER_SIZE, 40);
const_assert_eq!(Stack::<u16, 1>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<u16, 1>::CHUNK_MIN_SIZE, 64);
const_assert_eq!(Stack::<u16, 1>::CHUNK_FIRST_SIZE, 512);
const_assert_eq!(Stack::<u16, 1>::CHUNK_MAX_SIZE, 0x400_0000_0000_0000);

// u32, MIN_ALIGN=1
const_assert_eq!(Stack::<u32, 1>::ELEMENT_ALIGN, 4);
const_assert_eq!(Stack::<u32, 1>::ELEMENT_SIZE, 4);
const_assert_eq!(Stack::<u32, 1>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<u32, 1>::FOOTER_SIZE, 40);
const_assert_eq!(Stack::<u32, 1>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<u32, 1>::CHUNK_MIN_SIZE, 64);
const_assert_eq!(Stack::<u32, 1>::CHUNK_FIRST_SIZE, 512);
const_assert_eq!(Stack::<u32, 1>::CHUNK_MAX_SIZE, 0x400_0000_0000_0000);

// u64, MIN_ALIGN=1
const_assert_eq!(Stack::<u64, 1>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<u64, 1>::ELEMENT_SIZE, 8);
const_assert_eq!(Stack::<u64, 1>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<u64, 1>::FOOTER_SIZE, 40);
const_assert_eq!(Stack::<u64, 1>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<u64, 1>::CHUNK_MIN_SIZE, 64);
const_assert_eq!(Stack::<u64, 1>::CHUNK_FIRST_SIZE, 512);
const_assert_eq!(Stack::<u64, 1>::CHUNK_MAX_SIZE, 0x400_0000_0000_0000);

// T9, MIN_ALIGN=1
const_assert_eq!(Stack::<T9, 1>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T9, 1>::ELEMENT_SIZE, 16);
const_assert_eq!(Stack::<T9, 1>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<T9, 1>::FOOTER_SIZE, 40);
const_assert_eq!(Stack::<T9, 1>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<T9, 1>::CHUNK_MIN_SIZE, 64);
const_assert_eq!(Stack::<T9, 1>::CHUNK_FIRST_SIZE, 512);
const_assert_eq!(Stack::<T9, 1>::CHUNK_MAX_SIZE, 0x400_0000_0000_0000);

// T35, MIN_ALIGN=1
const_assert_eq!(Stack::<T35, 1>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T35, 1>::ELEMENT_SIZE, 40);
const_assert_eq!(Stack::<T35, 1>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<T35, 1>::FOOTER_SIZE, 40);
const_assert_eq!(Stack::<T35, 1>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<T35, 1>::CHUNK_MIN_SIZE, 128);
const_assert_eq!(Stack::<T35, 1>::CHUNK_FIRST_SIZE, 512);
const_assert_eq!(Stack::<T35, 1>::CHUNK_MAX_SIZE, 0x400_0000_0000_0000);

// T83, MIN_ALIGN=1
const_assert_eq!(Stack::<T83, 1>::ELEMENT_ALIGN, 8);
const_assert_eq!(Stack::<T83, 1>::ELEMENT_SIZE, 88);
const_assert_eq!(Stack::<T83, 1>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<T83, 1>::FOOTER_SIZE, 40);
const_assert_eq!(Stack::<T83, 1>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<T83, 1>::CHUNK_MIN_SIZE, 256);
const_assert_eq!(Stack::<T83, 1>::CHUNK_FIRST_SIZE, 1024);
const_assert_eq!(Stack::<T83, 1>::CHUNK_MAX_SIZE, 0x400_0000_0000_0000);

// u8, MIN_ALIGN=4
const_assert_eq!(Stack::<u8, 4>::ELEMENT_ALIGN, 4);
const_assert_eq!(Stack::<u8, 4>::ELEMENT_SIZE, 4);
const_assert_eq!(Stack::<u8, 4>::FOOTER_ALIGN, 8);
const_assert_eq!(Stack::<u8, 4>::FOOTER_SIZE, 40);
const_assert_eq!(Stack::<u8, 4>::CHUNK_ALIGN, 8);
const_assert_eq!(Stack::<u8, 4>::CHUNK_MIN_SIZE, 64);
const_assert_eq!(Stack::<u8, 4>::CHUNK_FIRST_SIZE, 512);
const_assert_eq!(Stack::<u8, 4>::CHUNK_MAX_SIZE, 0x400_0000_0000_0000);

// T9, MIN_ALIGN=64
const_assert_eq!(Stack::<T9, 64>::ELEMENT_ALIGN, 64);
const_assert_eq!(Stack::<T9, 64>::ELEMENT_SIZE, 64);
const_assert_eq!(Stack::<T9, 64>::FOOTER_ALIGN, 64);
const_assert_eq!(Stack::<T9, 64>::FOOTER_SIZE, 40);
const_assert_eq!(Stack::<T9, 64>::CHUNK_ALIGN, 64);
const_assert_eq!(Stack::<T9, 64>::CHUNK_MIN_SIZE, 256);
const_assert_eq!(Stack::<T9, 64>::CHUNK_FIRST_SIZE, 1024);
const_assert_eq!(Stack::<T9, 64>::CHUNK_MAX_SIZE, 0x400_0000_0000_0000);
