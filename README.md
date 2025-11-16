# `bump-stack`

`Stack<T>` is a [LIFO] collection that uses bump allocation inside. It is
considered to implement a subset of [`Vec`]'s API. But it also have some own
features.

[LIFO]: https://en.wikipedia.org/wiki/Stack_(abstract_data_type)
[`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html

### Distiguishes from `Vec`

`Stack<T>` has API that is mostly a subset of API of the standard `Vec<T>`. But
there are some differences.

- `Stack` can add new elements only by pushing them on its back.
- `Stack` can remove elements only popping them from its back.
- `Stack` doesn't have access to its element by indexing. But it has iterators
  over every element.

### Allocation

`Stack<T>` uses a linked list of chunks of memory that contain its elements of
the `T` type. If the current memory chunk is full, the stack allocates another
one (two times bigger than previous) from the global allocator, and keeps
pushing new elements to this new chunk. So, in contrast to `Vec`, `Stack`
doesn't move old elements from the small chunk into the bigger one.

### Iteration

Pushing new elements by immutable reference allows to do that during iteration.
To avoid inifinite loop, iteration runs over element that have already existed
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
