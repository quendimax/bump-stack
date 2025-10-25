//! Some helper functions for bump-stack.

#[inline(always)]
pub(crate) const fn max(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
}

#[inline(always)]
pub(crate) const fn round_down_to(n: usize, align: usize) -> usize {
    n & !(align - 1)
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
