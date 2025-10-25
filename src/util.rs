//! Some helper functions for bump-stack.

pub(crate) const fn max(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
}

/// Rounds `n` down to the nearest multiple of `divisor`.
///
/// # Panics
///
/// With debug assertions enabled, panics if `divisor` is not a power of two.
pub(crate) const fn round_down_to(n: usize, divisor: usize) -> usize {
    debug_assert!(divisor.is_power_of_two());
    n & !(divisor - 1)
}

/// Returns the biggest power of two smaller than or equal to `n`.
///
/// # Panics
///
/// With debug assertions enabled, panics if `n` is zero.
pub(crate) const fn round_down_to_pow2(n: usize) -> usize {
    debug_assert!(n > 0);
    let lead_zeros = n.leading_zeros();
    let mask = usize::MAX << (usize::BITS - lead_zeros - 1);
    n & mask
}

#[inline(always)]
pub(crate) unsafe fn write_with<F, T>(ptr: *mut T, f: F)
where
    F: FnOnce() -> T,
{
    #[inline(always)]
    unsafe fn inner_writer<T, F>(ptr: *mut T, f: F)
    where
        F: FnOnce() -> T,
    {
        // This function is translated as:
        // - allocate space for a T on the stack
        // - call f() with the return value being put onto this stack space
        // - memcpy from the stack to the heap
        //
        // Ideally we want LLVM to always realize that doing a stack
        // allocation is unnecessary and optimize the code so it writes
        // directly into the heap instead. It seems we get it to realize
        // this most consistently if we put this critical line into it's
        // own function instead of inlining it into the surrounding code.
        unsafe { core::ptr::write(ptr, f()) };
    }

    unsafe { inner_writer(ptr, f) };
}

macro_rules! const_assert {
    ($expr:expr $(,)?) => {
        const _: [(); 0 - !{ $expr } as usize] = [];
    };
}

pub(crate) use const_assert;

macro_rules! const_assert_eq {
    ($l_expr:expr, $r_expr:expr $(,)?) => {
        crate::util::const_assert!(($l_expr) == ($r_expr));
    };
}

pub(crate) use const_assert_eq;

#[cfg(test)]
mod utest {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn round_down_to_n() {
        assert_eq!(round_down_to(0, 1), 0);
        assert_eq!(round_down_to(0, 2), 0);
        assert_eq!(round_down_to(0, 0x8000_0000_0000_0000), 0);

        assert_eq!(round_down_to(3, 1), 3);
        assert_eq!(round_down_to(3, 2), 2);
        assert_eq!(round_down_to(3, 0x8000_0000_0000_0000), 0);

        assert_eq!(round_down_to(7, 1), 7);
        assert_eq!(round_down_to(7, 2), 6);
        assert_eq!(round_down_to(7, 4), 4);
        assert_eq!(round_down_to(7, 0x8000_0000_0000_0000), 0);

        assert_eq!(round_down_to(1, 1), 1);
    }

    #[test]
    #[cfg_attr(debug_assertions, should_panic)]
    fn round_down_to_n_panics() {
        assert_eq!(round_down_to(1, 0), 0);
        assert_eq!(round_down_to(usize::MAX, 0), 0);
    }

    #[test]
    fn round_down_to_pow_2() {
        assert_eq!(round_down_to_pow2(1), 1);
        assert_eq!(round_down_to_pow2(2), 2);
        assert_eq!(round_down_to_pow2(3), 2);
        assert_eq!(round_down_to_pow2(4), 4);
        assert_eq!(round_down_to_pow2(5), 4);
        assert_eq!(round_down_to_pow2(6), 4);
        assert_eq!(round_down_to_pow2(7), 4);
        assert_eq!(round_down_to_pow2(8), 8);

        assert_eq!(
            round_down_to_pow2(isize::MAX as usize),
            0x4000_0000_0000_0000
        );
        assert_eq!(
            round_down_to_pow2(isize::MAX as usize + 1),
            0x8000_0000_0000_0000
        );
        assert_eq!(round_down_to_pow2(usize::MAX - 1), 0x8000_0000_0000_0000);
        assert_eq!(round_down_to_pow2(usize::MAX), 0x8000_0000_0000_0000);
    }

    #[test]
    #[cfg_attr(debug_assertions, should_panic)]
    fn round_down_to_pow_2_panics() {
        assert_eq!(round_down_to_pow2(0), 0);
    }
}
