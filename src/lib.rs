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
	#[inline]
	fn next_eternal(&mut self) -> Self::Item {
		if let Some(item) = self.next() {
			item
		} else {
			unreachable!()
		}
	}

	/// Generate new `N`-sized array using [`EternalIterator::next_eternal()`].
	/// Uninhabited values may cause UB here.
	///
	/// ```
	/// # use eternal_iterator::prelude::*;
	/// let arr: [i32; 5] = (0..).next_array();
	/// assert_eq!(arr, [0, 1, 2, 3, 4]);
	/// ```
	fn next_array<const N: usize>(&mut self) -> [Self::Item; N] {
		use core::mem::MaybeUninit;
		let mut arr = MaybeUninit::<[Self::Item; N]>::uninit();
		// SAFETY: The sizes of both size is the same and uninitialized MaybeUninit is
		// valid.
		unsafe { &mut *(arr.as_mut_ptr() as *mut [MaybeUninit<Self::Item>; N]) }
			.iter_mut()
			.for_each(|mu| {
				*mu = MaybeUninit::new(self.next_eternal());
			});

		// SAFETY: MaybeUninited is initialized here.
		unsafe { arr.assume_init() }
	}
}

// SAFETY: precondition is satisfied obviously.
unsafe impl<I: EternalIterator + ?Sized> EternalIterator for &mut I {
	#[inline]
	fn next_eternal(&mut self) -> I::Item {
		(**self).next_eternal()
	}
}

macro_rules! impl_eternal_iterator {
	($($(#[doc = $doc:expr])* impl [$($param:tt)*] for $obj:ty $({ $lassert:expr => [$($rassert:expr),*] })*;)+) => {
		$(
			// SAFETY: precondition is satisfied obviously.
			$(
				#[doc = $doc]
			)*
			$(
				#[doc = concat!(
					"```\n# use eternal_iterator::*;\nlet mut it = ",
					$lassert,
					$(concat!(
						";\nassert_eq!(it.next_eternal(), ",
						$rassert,
						")"
					),)*
					";\n```"
				)]
			)*
			unsafe impl<$($param)*> EternalIterator for $obj
			where
				$obj: Iterator
			{
			}
		)+
	};
}

macro_rules! impl_eternal_iterator_blanket {
	($($(#[doc = $doc:expr])* $($pitem:ident)::+ [$($id:ident),+] $({ $lassert:expr => [$($rassert:expr),*] })*;)+) => {
		$(
			impl_eternal_iterator! { $(#[doc = $doc])* impl [$($id: EternalIterator),+] for $($pitem)::+<$($id),+> $({ $lassert => [$($rassert),*] })*; }
		)+
	};
}

impl_eternal_iterator! {
	impl [A: Clone] for core::iter::Repeat<A> {
		"std::iter::repeat(123)" => ["123", "123", "123"]
	};
	impl [A, F: FnMut() -> A] for core::iter::RepeatWith<F> {
		"std::iter::repeat_with(|| 123)" => ["123", "123", "123"]
	};
	impl [I: Clone + Iterator] for core::iter::Cycle<I> {
		"(0..2).cycle()" => ["0", "1", "0", "1"]
	};
	impl [A: Iterator, B: EternalIterator<Item = A::Item>] for core::iter::Chain<A, B> {
		"(0..2).chain(4..)" => ["0", "1", "4", "5"]
	};
	impl [A: EternalIterator, B: EternalIterator] for core::iter::Zip<A, B> {
		"(0..).zip(4..)" => ["(0, 4)", "(1, 5)", "(2, 6)"]
	};
	impl ['a, T: 'a + Clone, I: EternalIterator<Item = &'a T>] for core::iter::Cloned<I> {
		"std::iter::repeat(&123).cloned()" => ["123", "123", "123"]
	};
	impl [I: EternalIterator, F] for core::iter::FilterMap<I, F> {
		"(0..).filter_map(|x| (x % 2 == 0).then(|| x))" => ["0", "2", "4"]
	};
	impl [I: EternalIterator, F] for core::iter::Map<I, F> {
		"(0..).map(|x| x * 2)" => ["0", "2", "4"]
	};
	impl [II: IntoIterator, I: EternalIterator<Item = II>] for core::iter::Flatten<I> {
		"(0..).map(|x| x..(x + 2)).flatten()" => ["0", "1", "1", "2", "2"]
	};
	impl [I: EternalIterator, F] for core::iter::Inspect<I, F>;
	impl [I: EternalIterator, P] for core::iter::Filter<I, P> {
		"(0..).filter(|x| x % 2 == 0)" => ["0", "2", "4"]
	};
	impl [I: EternalIterator, P] for core::iter::SkipWhile<I, P> {
		"(-3_i32..).skip_while(|x| x.is_negative())" => ["0", "1", "2"]
	};
	impl [I: EternalIterator, U: IntoIterator, F] for core::iter::FlatMap<I, U, F> {
		"(0..).flat_map(|x| x..(x + 2))" => ["0", "1", "1", "2"]
	};
	impl [A] for core::ops::RangeFrom<A> {
		"(0..)" => ["0", "1", "2"]
	};
	impl [I: EternalIterator<Item = u16>] for core::char::DecodeUtf16<I>;
}

impl_eternal_iterator_blanket! {
	core::iter::Enumerate[I] {
		"std::iter::repeat(123).enumerate()" => ["(0, 123)", "(1, 123)", "(2, 123)"]
	};
	core::iter::Copied[I] {
		"std::iter::repeat(&123).copied()" => ["123", "123", "123"]
	};
	core::iter::Fuse[I] {
		"(0..).fuse()" => ["0", "1", "2"]
	};
	core::iter::Skip[I] {
		"(0..).skip(2)" => ["2", "3", "4"]
	};
	core::iter::StepBy[I]{
		"(0..).step_by(2)" => ["0", "2", "4"]
	};
	core::iter::Peekable[I] {
		"(0..).peekable()" => ["0", "1", "2"]
	};
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
/// `FnMut(&T) -> T` closure to compute each item???s successor.
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
		core::mem::replace(&mut self.next, item)
	}
}

/// It is used on the implementation of [`wrap_unsafe()`]. See [`wrap_unsafe()`]
/// document for details.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default, Debug)]
pub struct UnsafeWrapper<I>(I);

/// Wraps [`Iterator`] to be seen as [`EternalIterator`].
///
/// # Safety
/// [`Iterator::next()`] of `slot` never returns `None` value.
///
/// ```
/// # use eternal_iterator::prelude::*;
/// # use eternal_iterator::wrap_unsafe;
/// struct I;
/// impl Iterator for I {
/// 	type Item = i32;
/// 	fn next(&mut self) -> Option<i32> {
/// 		Some(123)
/// 	}
/// }
/// let mut it = unsafe { wrap_unsafe(I) };
/// assert_eq!(it.next_eternal(), 123);
/// assert_eq!(it.next_eternal(), 123);
/// assert_eq!(it.next_eternal(), 123);
/// assert_eq!(it.next_eternal(), 123);
/// ```
pub unsafe fn wrap_unsafe<II: IntoIterator>(slot: II) -> UnsafeWrapper<II::IntoIter> {
	UnsafeWrapper(slot.into_iter())
}

/// Safe version of [`wrap_unsafe()`]
///
/// ```
/// # use eternal_iterator::prelude::*;
/// # use eternal_iterator::wrap;
/// let mut it = wrap(core::iter::repeat(123));
/// assert_eq!(it.next_eternal(), 123);
/// assert_eq!(it.next_eternal(), 123);
/// assert_eq!(it.next_eternal(), 123);
/// assert_eq!(it.next_eternal(), 123);
/// ```
pub fn wrap<I: EternalIterator, II: IntoIterator<IntoIter = I>>(slot: II) -> UnsafeWrapper<I> {
	UnsafeWrapper(slot.into_iter())
}

impl<I: Iterator> Iterator for UnsafeWrapper<I> {
	type Item = I::Item;
	fn next(&mut self) -> Option<I::Item> {
		self.0.next()
	}
}

// SAFETY: Checked with `wrap_unsafe()`
unsafe impl<I: Iterator> EternalIterator for UnsafeWrapper<I> {}

impl<I: Iterator> core::iter::FusedIterator for UnsafeWrapper<I> {}

impl<I: Iterator, const N: usize> From<UnsafeWrapper<I>> for [I::Item; N] {
	fn from(mut it: UnsafeWrapper<I>) -> Self {
		it.next_array()
	}
}
