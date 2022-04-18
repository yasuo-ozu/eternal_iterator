//! This crate provides [`EternalIterator`], which promises that the iterator
//! iterates forever.
//!
//! This crate is compatible with [`core::iter`]. So you can use methods in
//! [`core::iter`] to generate iterators.
//!
//! ```
//! # use eternal_iterator::prelude::*;
//! let mut it = core::iter::repeat(123_i32).map(|i| i * 2)
//! 		.enumerate().skip(5).step_by(2).zip(core::iter::once(3).chain(10..));
//! assert_eq!(it.next_eternal(), ((5, 246), 3));
//! assert_eq!(it.next_eternal(), ((7, 246), 10));
//! assert_eq!(it.next(), Some(((9, 246), 11)));
//! assert_eq!(it.next_eternal(), ((11, 246), 12));
//! ```
pub mod prelude {
	pub use crate::EternalIterator;
}

///
/// Like [`Iterator`][std::iter::Iterator], but promises that the iterator
/// iterates forever.
///
/// # Safety
/// The implemented member [`next_eternal()`][EternalIterator::next_eternal]
/// must return the same value as the
/// [`Iterator::next()`][std::iter::Iterator::next] returns on the same
/// iterator.
#[must_use]
pub unsafe trait EternalIterator: Iterator {
	/// Advances the iterator and returns the next value like
	/// [`Iterator::next()`][std::iter::Iterator::next], but does not
	/// return None value, which means that the iterator lasts forever.
	///
	/// It returns the same value as the
	/// [`Iterator::next()`][std::iter::Iterator::next] returns on the same
	/// iterator.
	///
	/// ```
	/// # use eternal_iterator::prelude::*;
	/// let mut it = core::iter::repeat(123);
	/// assert_eq!(it.next_eternal(), 123);
	/// assert_eq!(it.next_eternal(), 123);
	/// assert_eq!(it.next_eternal(), 123);
	/// assert_eq!(it.next_eternal(), 123);
	/// ```
	fn next_eternal(&mut self) -> Self::Item;
}

// SAFETY: precondition is satisfied obviously.
unsafe impl<I: EternalIterator + ?Sized> EternalIterator for &mut I {
	#[inline]
	fn next_eternal(&mut self) -> I::Item {
		(**self).next_eternal()
	}
}

macro_rules! impl_eternal_iterator {
	($(impl [$($param:tt)*] for $obj:ty;)+) => {
		$(
			// SAFETY: precondition is satisfied obviously.
			unsafe impl<$($param)*> EternalIterator for $obj
			where
				$obj: Iterator
			{
				#[inline]
				fn next_eternal(&mut self) -> Self::Item {
					if let Some(item) = self.next() {
						item
					} else {
						unreachable!()
					}
				}
			}
		)+
	};
}

macro_rules! impl_eternal_iterator_blanket {
	($($($pitem:ident)::+ [$($id:ident),+];)+) => {
		$(
			impl_eternal_iterator! { impl [$($id: EternalIterator),+] for $($pitem)::+<$($id),+>; }
		)+
	};
}

impl_eternal_iterator! {
	impl [A: Clone] for core::iter::Repeat<A>;
	impl [A, F: FnMut() -> A] for core::iter::RepeatWith<F>;
	impl [I: Clone + Iterator] for core::iter::Cycle<I>;
	impl [A: Iterator, B: EternalIterator<Item = A::Item>] for core::iter::Chain<A, B>;
	impl [A: EternalIterator, B: EternalIterator] for core::iter::Zip<A, B>;
	impl ['a, T: 'a + Clone, I: EternalIterator<Item = &'a T>] for core::iter::Cloned<I>;
	impl [I: EternalIterator, St, F] for core::iter::Scan<I, St, F>;
	impl [I: EternalIterator, F] for core::iter::FilterMap<I, F>;
	impl [I: EternalIterator, F] for core::iter::Map<I, F>;
	impl [II: IntoIterator, I: EternalIterator<Item = II>] for core::iter::Flatten<I>;
	impl [I: EternalIterator, F] for core::iter::Inspect<I, F>;
	impl [I: EternalIterator, P] for core::iter::Filter<I, P>;
	impl [I: EternalIterator, P] for core::iter::SkipWhile<I, P>;
	impl [I: EternalIterator, U: IntoIterator, F] for core::iter::FlatMap<I, U, F>;
	impl [A] for core::ops::RangeFrom<A>;
	impl [I: EternalIterator<Item = u16>] for core::char::DecodeUtf16<I>;
}

impl_eternal_iterator_blanket! {
	core::iter::Enumerate[I];
	core::iter::Copied[I];
	core::iter::Fuse[I];
	core::iter::Skip[I];
	core::iter::StepBy[I];
	core::iter::Peekable[I];
}

/// It is used on the implementation of [`from_fn()`]. See [`from_fn()`]
/// document for details.
#[derive(Clone)]
pub struct FromFn<F>(F);

/// Creates a new iterator where each iteration calls the provided closure
/// `F: FnMut() -> T`.
///
/// This allows creating a custom iterator with any behavior without using the
/// more verbose syntax of creating a dedicated type and implementing the
/// [`Iterator`] or [`EternalIterator`] trait for it.
///
/// ```
/// # use eternal_iterator::prelude::*;
/// # use eternal_iterator::from_fn;
/// let mut count = 0_i32;
/// let mut it = from_fn(move || {
/// 	count += 1;
/// 	count
/// });
/// assert_eq!(it.next_eternal(), 1);
/// assert_eq!(it.next_eternal(), 2);
/// assert_eq!(it.next_eternal(), 3);
/// ```
#[inline]
pub fn from_fn<T, F>(f: F) -> FromFn<F>
where
	F: FnMut() -> T,
{
	FromFn(f)
}

impl<T, F> Iterator for FromFn<F>
where
	F: FnMut() -> T,
{
	type Item = T;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		Some(self.next_eternal())
	}
}

// SAFETY: precondition is satisfied obviously.
unsafe impl<T, F> EternalIterator for FromFn<F>
where
	F: FnMut() -> T,
{
	#[inline]
	fn next_eternal(&mut self) -> Self::Item {
		(self.0)()
	}
}

/// It is used on the implementation of [`successors()`]. See [`successors()`]
/// document for details.
#[derive(Clone)]
pub struct Successors<T, F> {
	next: T,
	succ: F,
}

/// Creates a new iterator where each successive item is computed based on the
/// preceding one.
///
/// The iterator starts with the given first item (if any) and calls the given
/// `FnMut(&T) -> T` closure to compute each item’s successor.
///
/// It is alternative of [`core::iter::successors()`].
///
/// ```
/// # use eternal_iterator::successors;
/// # use eternal_iterator::prelude::*;
/// let mut it = successors(123_i32, |val: &i32| {
/// 	if *val % 2 == 0 {
/// 		*val / 2
/// 	} else {
/// 		3 * *val + 1
/// 	}
/// });
/// assert_eq!(it.next_eternal(), 123);
/// assert_eq!(it.next_eternal(), 370);
/// assert_eq!(it.next_eternal(), 185);
/// ```
pub fn successors<T, F>(next: T, succ: F) -> Successors<T, F> {
	Successors { next, succ }
}

impl<T, F> Iterator for Successors<T, F>
where
	F: FnMut(&T) -> T,
{
	type Item = T;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		Some(self.next_eternal())
	}
}

// SAFETY: precondition is satisfied obviously.
unsafe impl<T, F> EternalIterator for Successors<T, F>
where
	F: FnMut(&T) -> T,
{
	#[inline]
	fn next_eternal(&mut self) -> Self::Item {
		let item = (self.succ)(&self.next);
		std::mem::replace(&mut self.next, item)
	}
}