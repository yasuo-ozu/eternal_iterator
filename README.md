# eternal_iterator

[![Test Status](https://github.com/yasuo-ozu/eternal_iterator/workflows/Tests/badge.svg?event=push)](https://github.com/yasuo-ozu/eternal_iterator/actions)
[![Crate](https://img.shields.io/crates/v/eternal_iterator.svg)](https://crates.io/crates/eternal_iterator)
[![Docs](https://docs.rs/eternal_iterator/badge.svg)](https://docs.rs/eternal_iterator)

This Rust crate provides EternalIterator trait, which promises that the iterator
iterates forever.

```rs
let mut it = core::iter::repeat(123_i32).map(|i| i * 2)
		.enumerate().skip(5).step_by(2).zip(core::iter::once(3).chain(10..));
assert_eq!(it.next_eternal(), ((5, 246), 3));
assert_eq!(it.next_eternal(), ((7, 246), 10));
assert_eq!(it.next(), Some(((9, 246), 11)));
assert_eq!(it.next_eternal(), ((11, 246), 12));
```
