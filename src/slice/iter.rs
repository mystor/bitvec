//! `BitSlice` iterator implementations.

use super::BitSlice;

use crate::{
	cursor::Cursor,
	store::BitStore,
};

use core::{
	iter::FusedIterator,
	mem,
};

#[cfg(feature = "alloc")]
use crate::pointer::BitPtr;

/** Produces a read-only iterator over all the bits in the `BitSlice`.

This iterator follows the ordering in the `BitSlice` type, and implements
`ExactSizeIterator` as `BitSlice` has a known, fixed, length, and
`DoubleEndedIterator` as it has known ends.
**/
impl<'a, C, T> IntoIterator for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = bool;
	type IntoIter = Iter<'a, C, T>;

	/// Iterates over the slice.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// An iterator over the slice domain.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0b1010_1100u8.bits::<BigEndian>();
	/// let mut count = 0;
	/// for bit in bits {
	///   if bit { count += 1; }
	/// }
	/// assert_eq!(count, 4);
	/// ```
	fn into_iter(self) -> Self::IntoIter {
		Iter {
			inner: self
		}
	}
}

/** State keeper for chunked iteration over a `BitSlice`.

# Type Parameters

- `C: Cursor`: The bit-order type of the underlying `BitSlice`.
- `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Clone, Debug)]
pub struct Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	pub(super) inner: &'a BitSlice<C, T>,
	/// The width of the chunks.
	pub(super) width: usize,
}

impl<'a, C, T> DoubleEndedIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the back of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.bits::<BigEndian>();
	/// let mut chunks = bits.chunks(5);
	/// assert_eq!(chunks.next_back(), Some(&bits[5 ..]));
	/// assert_eq!(chunks.next_back(), Some(&bits[.. 5]));
	/// assert!(chunks.next_back().is_none());
	/// ```
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let len = self.inner.len();
		let rem = len % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let (head, tail) = self.inner.split_at(len - size);
		self.inner = head;
		Some(tail)
	}
}

/// Mark that the iterator has an exact size.
impl<'a, C, T> ExactSizeIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/// Mark that the iterator will not resume after halting.
impl<'a, C, T> FusedIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.bits::<LittleEndian>();
	/// let mut chunks = bits.chunks(5);
	/// assert_eq!(chunks.next(), Some(&bits[.. 5]));
	/// assert_eq!(chunks.next(), Some(&bits[5 ..]));
	/// assert!(chunks.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		use core::cmp::min;
		if self.inner.is_empty() {
			return None;
		}
		let size = min(self.inner.len(), self.width);
		let (head, tail) = self.inner.split_at(size);
		self.inner = tail;
		Some(head)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// let mut chunks = bits.chunks(5);
	/// assert_eq!(chunks.size_hint(), (2, Some(2)));
	/// chunks.next();
	/// assert_eq!(chunks.size_hint(), (1, Some(1)));
	/// chunks.next();
	/// assert_eq!(chunks.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.inner.is_empty() {
			return (0, Some(0));
		}
		let len = self.inner.len();
		let (n, r) = (len / self.width, len % self.width);
		let len = n + (r > 0) as usize;
		(len, Some(len))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert_eq!(bits.chunks(3).count(), 3);
	/// ```
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// let mut chunks = bits.chunks(3);
	/// assert_eq!(chunks.nth(1), Some(&bits[3 .. 6]));
	/// assert_eq!(chunks.nth(0), Some(&bits[6 ..]));
	/// assert!(chunks.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		use core::cmp::min;
		let (start, ovf) = n.overflowing_mul(self.width);
		let len = self.inner.len();
		if start >= len || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let end = start.checked_add(self.width)
			.map(|s| min(s, len))
			.unwrap_or(len);
		let out = &self.inner[start .. end];
		self.inner = &self.inner[end ..];
		Some(out)
	}

	/// Consumes the iterator, returning only the final chunk.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last chunk in the iterator slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert_eq!(bits.chunks(3).last(), Some(&bits[6 ..]));
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for mutable chunked iteration over a `BitSlice`.

# Type Parameters

- `C: Cursor`: The bit-order type of the underlying `BitSlice`.
- `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Debug)]
pub struct ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	pub(super) inner: &'a mut BitSlice<C, T>,
	/// The width of the chunks.
	pub(super) width: usize,
}

impl<'a, C, T> DoubleEndedIterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the back of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let len = self.inner.len();
		let rem = len % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(len - size);
		self.inner = head;
		Some(tail)
	}
}

impl<'a, C, T> ExactSizeIterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	fn next(&mut self) -> Option<Self::Item> {
		use core::cmp::min;
		if self.inner.is_empty() {
			return None;
		}
		let size = min(self.inner.len(), self.width);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(size);
		self.inner = tail;
		Some(head)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.inner.is_empty() {
			return (0, Some(0));
		}
		let len = self.inner.len();
		let (n, r) = (len / self.width, len % self.width);
		let len = n + (r > 0) as usize;
		(len, Some(len))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		use core::cmp::min;
		let (start, ovf) = n.overflowing_mul(self.width);
		let len = self.inner.len();
		if start >= len || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let end = start.checked_add(self.width)
			.map(|s| min(s, len))
			.unwrap_or(len);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(start);
		let (_, nth) = head.split_at_mut(end - start);
		self.inner = tail;
		Some(nth)
	}

	/// Consumes the iterator, returning only the final chunk.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last chunk in the iterator slice, if any.
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for exact chunked iteration over a `BitSlice`.

# Type Parameters

- `C: Cursor`: The bit-order type of the underlying `BitSlice`.
- `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Clone, Debug)]
pub struct ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	pub(super) inner: &'a BitSlice<C, T>,
	/// The excess of the original `BitSlice`, which is not iterated.
	pub(super) extra: &'a BitSlice<C, T>,
	/// The width of the chunks.
	pub(super) width: usize,
}

impl<'a, C, T> ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the remainder of the original slice, which will not be included
	/// in the iteration.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The remaining slice that iteration will not include.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// let chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.remainder(), &bits[6 ..]);
	/// ```
	pub fn remainder(&self) -> &'a BitSlice<C, T> {
		self.extra
	}
}

impl<'a, C, T> DoubleEndedIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the back of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.bits::<BigEndian>();
	/// let mut chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.next_back(), Some(&bits[3 .. 6]));
	/// assert_eq!(chunks_exact.next_back(), Some(&bits[0 .. 3]));
	/// assert!(chunks_exact.next_back().is_none());
	/// ```
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, tail) = self.inner.split_at(self.inner.len() - self.width);
		self.inner = head;
		Some(tail)
	}
}

/// Mark that the iterator has an exact size.
impl<'a, C, T> ExactSizeIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/// Mark that the iterator will not resume after halting.
impl<'a, C, T> FusedIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.bits::<LittleEndian>();
	/// let mut chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.next(), Some(&bits[0 .. 3]));
	/// assert_eq!(chunks_exact.next(), Some(&bits[3 .. 6]));
	/// assert!(chunks_exact.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, tail) = self.inner.split_at(self.width);
		self.inner = tail;
		Some(head)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// let mut chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.size_hint(), (2, Some(2)));
	/// chunks_exact.next();
	/// assert_eq!(chunks_exact.size_hint(), (1, Some(1)));
	/// chunks_exact.next();
	/// assert_eq!(chunks_exact.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.width;
		(len, Some(len))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert_eq!(bits.chunks_exact(3).count(), 2);
	/// ```
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 2u8.bits::<BigEndian>();
	/// let mut chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.nth(1), Some(&bits[3 .. 6]));
	/// assert!(chunks_exact.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.width);
		if start >= self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let (_, tail) = self.inner.split_at(start);
		self.inner = tail;
		self.next()
	}

	/// Consumes the iterator, returning only the final chunk.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last chunk in the iterator slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert_eq!(bits.chunks_exact(3).last(), Some(&bits[3 .. 6]));
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for mutable exact chunked iteration over a `BitSlice`.

# Type Parameters

- `C: Cursor`: The bit-order type of the underlying `BitSlice`.
- `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Debug)]
pub struct ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	pub(super) inner: &'a mut BitSlice<C, T>,
	/// The excess of the original `BitSlice`, which is not iterated.
	pub(super) extra: &'a mut BitSlice<C, T>,
	/// The width of the chunks.
	pub(super) width: usize,
}

impl<'a, C, T> ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the remainder of the original slice, which will not be included
	/// in the iteration.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The remaining slice that iteration will not include.
	pub fn into_remainder(self) -> &'a mut BitSlice<C, T> {
		self.extra
	}
}

impl<'a, C, T> DoubleEndedIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the back of th eslice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	fn next_back(&mut self) -> Option<Self::Item> {
		unimplemented!()
	}
}

impl<'a, C, T> ExactSizeIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(self.width);
		self.inner = tail;
		Some(head)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.width;
		(len, Some(len))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.width);
		if start >= self.inner.len() || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (_, tail) = tmp.split_at_mut(start);
		self.inner = tail;
		self.next()
	}

	/// Consumes the iterator, returning only the final chunk.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last chunk in the iterator slice, if any.
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for iteration over a `BitSlice`.

# Type Parameters

- `C: Cursor`: The bit-order type of the underlying `BitSlice`.
- `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Clone, Debug)]
pub struct Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	pub(super) inner: &'a BitSlice<C, T>,
}

impl<'a, C, T> Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Accesses the `BitPtr` representation of the slice.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The `BitPtr` representation of the remaining slice.
	#[cfg(feature = "alloc")]
	pub(crate) fn bitptr(&self) -> BitPtr<T> {
		self.inner.bitptr()
	}
}

impl<'a, C, T> DoubleEndedIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next bit from the back of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last bit in the slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = &1u8.bits::<BigEndian>()[6 ..];
	/// let mut iter = bits.iter();
	/// assert!(iter.next_back().unwrap());
	/// assert!(!iter.next_back().unwrap());
	/// assert!(iter.next_back().is_none());
	/// ```
	fn next_back(&mut self) -> Option<Self::Item> {
		self.inner.split_last().map(|(b, r)| {
			self.inner = r;
			b
		})
	}
}

/// Mark that the iterator has an exact size.
impl<'a, C, T> ExactSizeIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/// Mark that the iterator will not resume after halting.
impl<'a, C, T> FusedIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = bool;

	/// Advances the iterator by one, returning the first bit in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading bit in the iterator, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = &1u8.bits::<LittleEndian>()[.. 2];
	/// let mut iter = bits.iter();
	/// assert!(iter.next().unwrap());
	/// assert!(!iter.next().unwrap());
	/// assert!(iter.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		self.inner.split_first().map(|(b, r)| {
			self.inner = r;
			b
		})
	}

	/// Hints at the number of bits remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum bits remaining.
	/// - `Option<usize>`: The maximum bits remaining.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = &0x4Bu8.bits::<BigEndian>()[.. 2];
	/// let mut iter = bits.iter();
	/// assert_eq!(iter.size_hint(), (2, Some(2)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (1, Some(1)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		(len, Some(len))
	}

	/// Counts how many bits are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of bits remaining in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert_eq!(bits.iter().count(), 8);
	/// ```
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` bits, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of bits to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// bits.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 2u8.bits::<BigEndian>();
	/// let mut iter = bits.iter();
	/// assert!(iter.nth(6).unwrap());
	/// assert!(!iter.nth(0).unwrap());
	/// assert!(iter.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		if n >= self.len() {
			self.inner = BitSlice::empty();
			return None;
		}
		self.inner = &self.inner[n ..];
		self.next()
	}

	/// Consumes the iterator, returning only the final bit.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last bit in the iterator slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert!(bits.iter().last().unwrap());
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for reverse chunked iteration over a `BitSlice`.

# Type Parameters

- `C: Cursor`: The bit-order type of the underlying `BitSlice`.
- `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Clone, Debug)]
pub struct RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	pub(super) inner: &'a BitSlice<C, T>,
	/// The width of the chunks.
	pub(super) width: usize,
}

impl<'a, C, T> DoubleEndedIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the front of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.bits::<BigEndian>();
	/// let mut rchunks = bits.rchunks(5);
	/// assert_eq!(rchunks.next_back(), Some(&bits[.. 3]));
	/// assert_eq!(rchunks.next_back(), Some(&bits[3 ..]));
	/// assert!(rchunks.next_back().is_none());
	/// ```
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let len = self.inner.len();
		let rem = len % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let (head, tail) = self.inner.split_at(size);
		self.inner = tail;
		Some(head)
	}
}

/// Mark that the iterator has an exact size.
impl<'a, C, T> ExactSizeIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/// Mark that the iterator will not resume after halting.
impl<'a, C, T> FusedIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.bits::<LittleEndian>();
	/// let mut rchunks = bits.rchunks(5);
	/// assert_eq!(rchunks.next(), Some(&bits[3 ..]));
	/// assert_eq!(rchunks.next(), Some(&bits[.. 3]));
	/// assert!(rchunks.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		use core::cmp::min;
		if self.inner.is_empty() {
			return None;
		}
		let len = self.inner.len();
		let size = min(len, self.width);
		let (head, tail) = self.inner.split_at(len - size);
		self.inner = head;
		Some(tail)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// let mut rchunks = bits.rchunks(5);
	/// assert_eq!(rchunks.size_hint(), (2, Some(2)));
	/// rchunks.next();
	/// assert_eq!(rchunks.size_hint(), (1, Some(1)));
	/// rchunks.next();
	/// assert_eq!(rchunks.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.inner.is_empty() {
			return (0, Some(0));
		}
		let len = self.inner.len();
		let (len, rem) = (len / self.width, len % self.width);
		let len = len + (rem > 0) as usize;
		(len, Some(len))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert_eq!(bits.rchunks(3).count(), 3);
	/// ```
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 2u8.bits::<BigEndian>();
	/// let mut rchunks = bits.rchunks(3);
	/// assert_eq!(rchunks.nth(2), Some(&bits[0 .. 2]));
	/// assert!(rchunks.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		if end >= self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		// Can't underflow because of the check above
		let end = self.inner.len() - end;
		let start = end.checked_sub(self.width).unwrap_or(0);
		let nth = &self.inner[start .. end];
		self.inner = &self.inner[.. start];
		Some(nth)
	}

	/// Consumes the iterator, returning only the final chunk.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last chunk in the iterator slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert_eq!(bits.rchunks(3).last(), Some(&bits[.. 2]));
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for mutable reverse chunked iteration over a `BitSlice`.

# Type Parameters

- `C: Cursor`: The bit-order type of the underlying `BitSlice`.
- `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Debug)]
pub struct RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	pub(super) inner: &'a mut BitSlice<C, T>,
	/// The width of the chunks.
	pub(super) width: usize,
}

impl<'a, C, T> DoubleEndedIterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the front of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let rem = self.inner.len() % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(size);
		self.inner = tail;
		Some(head)
	}
}

impl<'a, C, T> ExactSizeIterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	fn next(&mut self) -> Option<Self::Item> {
		use core::cmp::min;
		if self.inner.is_empty() {
			return None;
		}
		let size = min(self.inner.len(), self.width);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let tlen = tmp.len();
		let (head, tail) = tmp.split_at_mut(tlen - size);
		self.inner = head;
		Some(tail)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.inner.is_empty() {
			return (0, Some(0));
		}
		let len = self.inner.len();
		let (len, rem) = (len / self.width, len % self.width);
		let len = len + (rem > 0) as usize;
		(len, Some(len))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		if end >= self.inner.len() || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		// Can't underflow because of the check above
		let end = self.inner.len() - end;
		let start = end.checked_sub(self.width).unwrap_or(0);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(start);
		let (nth, _) = tail.split_at_mut(end - start);
		self.inner = head;
		Some(nth)
	}

	/// Consumes the iterator, returning only the final chunk.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last chunk in the iterator slice, if any.
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for reverse exact iteration over a `BitSlice`.

# Type Parameters

- `C: Cursor`: The bit-order type of the underlying `BitSlice`.
- `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Clone, Debug)]
pub struct RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	pub(super) inner: &'a BitSlice<C, T>,
	/// The excess of the original `BitSlice`, which is not iterated.
	pub(super) extra: &'a BitSlice<C, T>,
	/// The width of the chunks.
	pub(super) width: usize,
}

impl<'a, C, T> RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the remainder of the original slice, which will not be included
	/// in the iteration.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The remaining slice that the iteration will not include.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// let rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.remainder(), &bits[.. 2]);
	/// ```
	pub fn remainder(&self) -> &'a BitSlice<C, T> {
		self.extra
	}
}

impl<'a, C, T> DoubleEndedIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the front of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.bits::<BigEndian>();
	/// let mut rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.next_back(), Some(&bits[2 .. 5]));
	/// assert_eq!(rchunks_exact.next_back(), Some(&bits[5 .. 8]));
	/// assert!(rchunks_exact.next_back().is_none());
	/// ```
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, tail) = self.inner.split_at(self.width);
		self.inner = tail;
		Some(head)
	}
}

/// Mark that the iterator has an exact size.
impl<'a, C, T> ExactSizeIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/// Mark that the iterator will not resume after halting.
impl<'a, C, T> FusedIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.bits::<LittleEndian>();
	/// let mut rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.next(), Some(&bits[5 .. 8]));
	/// assert_eq!(rchunks_exact.next(), Some(&bits[2 .. 5]));
	/// assert!(rchunks_exact.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, tail) = self.inner.split_at(self.inner.len() - self.width);
		self.inner = head;
		Some(tail)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// let mut rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.size_hint(), (2, Some(2)));
	/// rchunks_exact.next();
	/// assert_eq!(rchunks_exact.size_hint(), (1, Some(1)));
	/// rchunks_exact.next();
	/// assert_eq!(rchunks_exact.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		let n = self.inner.len() / self.width;
		(n, Some(n))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert_eq!(bits.rchunks_exact(3).count(), 2);
	/// ```
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// let mut rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.nth(1), Some(&bits[2 .. 5]));
	/// assert!(rchunks_exact.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		if end >= self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, _) = self.inner.split_at(self.inner.len() - end);
		self.inner = head;
		self.next()
	}

	/// Consumes the iterator, returning only the final bit.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last bit in the iterator slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert!(bits.iter().last().unwrap());
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for mutable reverse exact chunked iteration over a `BitSlice`.

# Type Parameters

- `C: Cursor`: The bit-order type of the underlying `BitSlice`.
- `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Debug)]
pub struct RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	pub(super) inner: &'a mut BitSlice<C, T>,
	/// The excess of the original `BitSlice`, which is not iterated.
	pub(super) extra: &'a mut BitSlice<C, T>,
	/// The width of the chunks.
	pub(super) width: usize,
}

impl<'a, C, T> RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the remainder of the original slice, which will not be included
	/// in the iteration.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The remaining slice that iteration will not include.
	pub fn into_remainder(self) -> &'a mut BitSlice<C, T> {
		self.extra
	}
}

impl<'a, C, T> DoubleEndedIterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the front of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(self.width);
		self.inner = tail;
		Some(head)
	}
}

impl<'a, C, T> ExactSizeIterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let tlen = tmp.len();
		let (head, tail) = tmp.split_at_mut(tlen - self.width);
		self.inner = head;
		Some(tail)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	fn size_hint(&self) -> (usize, Option<usize>) {
		let n = self.inner.len() / self.width;
		(n, Some(n))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		if end >= self.inner.len() || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let tlen = tmp.len();
		let (head, _) = tmp.split_at_mut(tlen - end);
		self.inner = head;
		self.next()
	}

	/// Consumes the iterator, returning only the final bit.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last bit in the iterator slice, if any.
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for sliding-window iteration over a `BitSlice`.

# Type Parameters

- `C: Cursor`: The bit-order type of the underlying `BitSlice`.
- `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Clone, Debug)]
pub struct Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	pub(super) inner: &'a BitSlice<C, T>,
	/// The width of the windows.
	pub(super) width: usize,
}

impl<'a, C, T> DoubleEndedIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next window from the back of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last window in the slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let store: &[u8] = &[0b0010_1101];
	/// let bits: &BitSlice = store.into();
	/// let mut windows = bits[2 .. 7].windows(3);
	/// assert_eq!(windows.next_back(), Some(&bits[4 .. 7]));
	/// assert_eq!(windows.next_back(), Some(&bits[3 .. 6]));
	/// assert_eq!(windows.next_back(), Some(&bits[2 .. 5]));
	/// assert!(windows.next_back().is_none());
	/// ```
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() || self.width > self.inner.len() {
			self.inner = BitSlice::empty();
			return None;
		}
		let len = self.inner.len();
		let out = &self.inner[len - self.width ..];
		self.inner = &self.inner[.. len - 1];
		Some(out)
	}
}

/// Mark that the iterator has an exact size.
impl<'a, C, T> ExactSizeIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/// Mark that the iterator will not resume after halting.
impl<'a, C, T> FusedIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	/// Advances the iterator by one, returning the first window in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading window in the iterator, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = &1u8.bits::<LittleEndian>()[.. 2];
	/// let mut iter = bits.iter();
	/// assert!(iter.next().unwrap());
	/// assert!(!iter.next().unwrap());
	/// assert!(iter.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		if self.width > self.inner.len() {
			self.inner = BitSlice::empty();
			None
		}
		else {
			let out = &self.inner[.. self.width];
			self.inner = &self.inner[1 ..];
			Some(out)
		}
	}

	/// Hints at the number of windows remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum windows remaining.
	/// - `Option<usize>`: The maximum windows remaining.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = &0x4Bu8.bits::<BigEndian>()[.. 2];
	/// let mut iter = bits.iter();
	/// assert_eq!(iter.size_hint(), (2, Some(2)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (1, Some(1)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		if self.width > len {
			(0, Some(0))
		}
		else {
			let len = len - self.width + 1;
			(len, Some(len))
		}
	}

	/// Counts how many windows are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of windows remaining in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert_eq!(bits.iter().count(), 8);
	/// ```
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` windows, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of windows to skip, before producing the next bit
	///   after the skips. If this overshoots the iterator’s remaining length,
	///   then the iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// windows.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 2u8.bits::<BigEndian>();
	/// let mut iter = bits.iter();
	/// assert!(iter.nth(6).unwrap());
	/// assert!(!iter.nth(0).unwrap());
	/// assert!(iter.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_add(self.width);
		if end > self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let out = &self.inner[n .. end];
		self.inner = &self.inner[n + 1 ..];
		Some(out)
	}

	/// Consumes the iterator, returning only the final window.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last window in the iterator slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert_eq!(bits.windows(3).last(), Some(&bits[5 ..]));
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}
