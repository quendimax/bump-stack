#![cfg(any(
    all(target_os = "linux", target_arch = "x86_64"),
    all(target_os = "macos", target_arch = "aarch64")
))]

use super::*;

macro_rules! assert {
    ($expr:expr $(,)?) => {
        const _: [(); 0 - !{ $expr } as usize] = [];
    };
}

macro_rules! assert_eq {
    ($l_expr:expr, $r_expr:expr $(,)?) => {
        assert!(($l_expr) == ($r_expr));
    };
}

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

struct T115 {
    _m1: u16,       // 2
    _m2: u64,       // 8
    _m3: u32,       // 4
    _m4: [u32; 24], // 96
    _m5: u32,       // 4
    _m6: u8,        // 1
}

// u8, MIN_ALIGN=1
assert_eq!(Stack::<u8>::ELEMENT_ALIGN, 1);
assert_eq!(Stack::<u8>::ELEMENT_SIZE, 1);
assert_eq!(Stack::<u8>::FOOTER_ALIGN, 8);
assert_eq!(Stack::<u8>::FOOTER_SIZE, 48);
assert_eq!(Stack::<u8>::CHUNK_ALIGN, 8);
assert_eq!(Stack::<u8>::CHUNK_MIN_SIZE, 128 - ALLOC_OVERHEAD);
assert_eq!(Stack::<u8>::CHUNK_FIRST_SIZE, 512 - ALLOC_OVERHEAD);
assert_eq!(Stack::<u8>::CHUNK_MAX_SIZE, (4 << 30) - ALLOC_OVERHEAD);

// u16, MIN_ALIGN=1
assert_eq!(Stack::<u16>::ELEMENT_ALIGN, 2);
assert_eq!(Stack::<u16>::ELEMENT_SIZE, 2);
assert_eq!(Stack::<u16>::FOOTER_ALIGN, 8);
assert_eq!(Stack::<u16>::FOOTER_SIZE, 48);
assert_eq!(Stack::<u16>::CHUNK_ALIGN, 8);
assert_eq!(Stack::<u16>::CHUNK_MIN_SIZE, 128 - ALLOC_OVERHEAD);
assert_eq!(Stack::<u16>::CHUNK_FIRST_SIZE, 512 - ALLOC_OVERHEAD);
assert_eq!(Stack::<u16>::CHUNK_MAX_SIZE, (4 << 30) - ALLOC_OVERHEAD);

// u32, MIN_ALIGN=1
assert_eq!(Stack::<u32>::ELEMENT_ALIGN, 4);
assert_eq!(Stack::<u32>::ELEMENT_SIZE, 4);
assert_eq!(Stack::<u32>::FOOTER_ALIGN, 8);
assert_eq!(Stack::<u32>::FOOTER_SIZE, 48);
assert_eq!(Stack::<u32>::CHUNK_ALIGN, 8);
assert_eq!(Stack::<u32>::CHUNK_MIN_SIZE, 128 - ALLOC_OVERHEAD);
assert_eq!(Stack::<u32>::CHUNK_FIRST_SIZE, 512 - ALLOC_OVERHEAD);
assert_eq!(Stack::<u32>::CHUNK_MAX_SIZE, (4 << 30) - ALLOC_OVERHEAD);

// u64, MIN_ALIGN=1
assert_eq!(Stack::<u64>::ELEMENT_ALIGN, 8);
assert_eq!(Stack::<u64>::ELEMENT_SIZE, 8);
assert_eq!(Stack::<u64>::FOOTER_ALIGN, 8);
assert_eq!(Stack::<u64>::FOOTER_SIZE, 48);
assert_eq!(Stack::<u64>::CHUNK_ALIGN, 8);
assert_eq!(Stack::<u64>::CHUNK_MIN_SIZE, 128 - ALLOC_OVERHEAD);
assert_eq!(Stack::<u64>::CHUNK_FIRST_SIZE, 512 - ALLOC_OVERHEAD);
assert_eq!(Stack::<u64>::CHUNK_MAX_SIZE, (4 << 30) - ALLOC_OVERHEAD);

// T9, MIN_ALIGN=1
assert_eq!(Stack::<T9>::ELEMENT_ALIGN, 8);
assert_eq!(Stack::<T9>::ELEMENT_SIZE, 16);
assert_eq!(Stack::<T9>::FOOTER_ALIGN, 8);
assert_eq!(Stack::<T9>::FOOTER_SIZE, 48);
assert_eq!(Stack::<T9>::CHUNK_ALIGN, 8);
assert_eq!(Stack::<T9>::CHUNK_MIN_SIZE, 128 - ALLOC_OVERHEAD);
assert_eq!(Stack::<T9>::CHUNK_FIRST_SIZE, 512 - ALLOC_OVERHEAD);
assert_eq!(Stack::<T9>::CHUNK_MAX_SIZE, (4 << 30) - ALLOC_OVERHEAD);
assert!(Stack::<T9>::ELEMENT_SIZE.is_multiple_of(Stack::<T9>::ELEMENT_ALIGN));

// T35, MIN_ALIGN=1
assert_eq!(Stack::<T35>::ELEMENT_ALIGN, 8);
assert_eq!(Stack::<T35>::ELEMENT_SIZE, 40);
assert_eq!(Stack::<T35>::FOOTER_ALIGN, 8);
assert_eq!(Stack::<T35>::FOOTER_SIZE, 48);
assert_eq!(Stack::<T35>::CHUNK_ALIGN, 8);
assert_eq!(Stack::<T35>::CHUNK_MIN_SIZE, 256 - ALLOC_OVERHEAD);
assert_eq!(Stack::<T35>::CHUNK_FIRST_SIZE, 512 - ALLOC_OVERHEAD);
assert_eq!(Stack::<T35>::CHUNK_MAX_SIZE, (4 << 30) - ALLOC_OVERHEAD);
assert!(Stack::<T35>::ELEMENT_SIZE.is_multiple_of(Stack::<T35>::ELEMENT_ALIGN));

// T83, MIN_ALIGN=1
assert_eq!(Stack::<T115>::ELEMENT_ALIGN, 8);
assert_eq!(Stack::<T115>::ELEMENT_SIZE, 120);
assert_eq!(Stack::<T115>::FOOTER_ALIGN, 8);
assert_eq!(Stack::<T115>::FOOTER_SIZE, 48);
assert_eq!(Stack::<T115>::CHUNK_ALIGN, 8);
assert_eq!(Stack::<T115>::CHUNK_MIN_SIZE, 512 - ALLOC_OVERHEAD);
assert_eq!(Stack::<T115>::CHUNK_FIRST_SIZE, 1024 - ALLOC_OVERHEAD);
assert_eq!(Stack::<T115>::CHUNK_MAX_SIZE, (4 << 30) - ALLOC_OVERHEAD);
assert!(Stack::<T115>::ELEMENT_SIZE.is_multiple_of(Stack::<T115>::ELEMENT_ALIGN));
