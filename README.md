# `bump-stack`

**`Stack<T>` is a [LIFO] collection that uses bump allocation inside.**

[![Crates.io Version](https://img.shields.io/crates/v/bump-stack)](https://crates.io/crates/bump-stack)
[![docs.rs (with version)](https://img.shields.io/docsrs/bump-stack/latest)](https://docs.rs/bump-stack/latest/bump_stack/)
[![Crates.io Total Downloads](https://img.shields.io/crates/d/bump-stack)](https://crates.io/crates/bump-stack)
[![License](https://img.shields.io/badge/License-MPL%202.0-blue.svg)](https://opensource.org/licenses/MPL-2.0)

[LIFO]: https://en.wikipedia.org/wiki/Stack_(abstract_data_type)

## Getting Started

[`Stack`] mostly implements a subset of [`Vec`]'s API, but it also have some own
features.

[`Stack`]: crate::Stack
[`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html

### Add `bump_stack` dependency to your crate

To start using `bump_stack`, add it to your `Cargo.toml`:

```toml
[dependencies]
bump_stack = "*"
```

### Populating

In order to populate a new stack, use different [`From`] trait implementations:

```rust
use bump_stack::Stack;

let _ = Stack::from([1, 2, 3]);
```

Also, as expected, [`Stack`] allows to add new elements by pushing them on the
stack.

```rust
use bump_stack::Stack;

let stack = Stack::new();

assert_eq!(stack.push(1), &1);
assert_eq!(stack.push(2), &2);
assert_eq!(stack.push(3), &3);
```

Note, that, in contrast to [`Vec`], we push new elements using immutable
reference (why? read in the [Allocation](#allocation) part). Also `push` returns
a reference to the just pushed element.

### Removing elements

Remove an element is possible only by calling [`pop`] method.

```rust
use bump_stack::Stack;

let mut stack = Stack::from([1, 2, 3]);

assert_eq!(stack.pop(), Some(3));
assert_eq!(stack.pop(), Some(2));
assert_eq!(stack.pop(), Some(1));
```

### Iteration

Pushing new elements by immutable reference allows to do that during iteration.
To avoid infinite loop, iteration runs over elements that have already existed
at the moment of creating the iterator.

```rust
use bump_stack::Stack;

let stk = Stack::from([1, 2, 4]);

for elem in stk.iter() {
    stk.push(*elem);
}
assert_eq!(stk.len(), 6);
assert_eq!(stk, [1, 2, 4, 1, 2, 4]);
```

## Allocation

`Stack<T>` uses a linked list of memory chunks that contain elements of the type
`T`. If the current memory chunk is full, the stack allocates another one from
the global allocator (usually two times bigger than the previous chunk), and
keeps pushing new elements to this new chunk. So, in contrast to `Vec`, `Stack`
doesn't move old elements from the small chunk into the bigger one. Exactly this
property allows to push new elements by immutable reference, because adding
element never causes moving old elements.

When we pop elements from the stack, if the current chunk becomes empty, then
there are possible two steps:

1. If the chunk is the last chunk in the list, it is not deallocated, but it is
   kept for future use as a cache.

2. If the chunk is not the last one, and we already have another chunk as a
   cache, the smallest from both is deallocated, and the biggest is kept as a
   cache.

## Some notes

This crate was heavily inspired by [`bumpalo`] crate, and originally used it
code as a start point. So, although most of the code is different now, it still
can contain some `bumpalo`'s code snippets.

I am not an expert in licensing, but if my choice of license (MPL 2.0 is more
copyleftish than `bumpalo`'s MIT or Apache 2.0) in some way breaks the spirit of
the `bumpalo` crate, please let me know.

[`bumpalo`]: https://crates.io/crates/bumpalo
