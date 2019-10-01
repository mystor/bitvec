/*! `BitSlice` iterator implementations.

The implementations in this module (and its cousin type/iter.rs modules)
override the default provided methods where it is possible to provide a more
efficient function body.

- `Iterator::size_hint` always returns `(0, None)`; these iterators know their
  exact size.
- `Iterator::count` drains the iterator in a loop; these iterators know their
  exact size.
- `Iterator::last` drains the iterator in a loop; these iterators know their
  reverse end.
- `Iterator::nth` drains the iterator in a loop; these iterators know how to
  skip forward.
!*/

use super::BitSlice;

use crate::{
	cursor::Cursor,
	store::BitStore,
};

use core::{
	cmp,
	iter::FusedIterator,
	mem,
};

#[cfg(feature = "alloc")]
use crate::pointer::BitPtr;

impl<'a, C, T> IntoIterator for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = bool;
	type IntoIter = Iter<'a, C, T>;

	fn into_iter(self) -> Self::IntoIter {
		Iter {
			inner: self
		}
	}
}

/// State keeper for chunked iteration over a `BitSlice`.
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
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let len = self.inner.len();
		let rem = len % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let (rest, tail) = self.inner.split_at(len - size);
		self.inner = rest;
		Some(tail)
	}
}

impl<'a, C, T> ExactSizeIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let size = cmp::min(self.inner.len(), self.width);
		let (head, rest) = self.inner.split_at(size);
		self.inner = rest;
		Some(head)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.inner.is_empty() {
			return (0, Some(0));
		}
		let len = self.inner.len();
		let (n, r) = (len / self.width, len % self.width);
		let len = n + (r > 0) as usize;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.width);
		let len = self.inner.len();
		if start >= len || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let (_, rest) = self.inner.split_at(start);
		self.inner = rest;
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for mutable chunked iteration over a `BitSlice`.
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
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let len = self.inner.len();
		let rem = len % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (rest, tail) = tmp.split_at_mut(len - size);
		self.inner = rest;
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

	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let size = cmp::min(self.inner.len(), self.width);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, rest) = tmp.split_at_mut(size);
		self.inner = rest;
		Some(head)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.inner.is_empty() {
			return (0, Some(0));
		}
		let len = self.inner.len();
		let (n, r) = (len / self.width, len % self.width);
		let len = n + (r > 0) as usize;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.width);
		let len = self.inner.len();
		if start >= len || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (_, rest) = tmp.split_at_mut(start);
		self.inner = rest;
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for exact chunked iteration over a `BitSlice`.
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
	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (rest, tail) = self.inner.split_at(len - self.width);
		self.inner = rest;
		Some(tail)
	}
}

impl<'a, C, T> ExactSizeIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, rest) = self.inner.split_at(self.width);
		self.inner = rest;
		Some(head)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.width;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.width);
		if start >= self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let (_, rest) = self.inner.split_at(start);
		self.inner = rest;
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for mutable exact chunked iteration over a `BitSlice`.
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
	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (rest, tail) = tmp.split_at_mut(len - self.width);
		self.inner = rest;
		Some(tail)
	}
}

impl<'a, C, T> ExactSizeIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, rest) = tmp.split_at_mut(self.width);
		self.inner = rest;
		Some(head)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.width;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.width);
		if start >= self.inner.len() || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (_, rest) = tmp.split_at_mut(start);
		self.inner = rest;
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for iteration over a `BitSlice`.
#[derive(Clone, Debug)]
pub struct Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	pub(super) inner: &'a BitSlice<C, T>,
}

impl<'a, C, T> Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Accesses the `BitPtr` representation of the slice.
	#[cfg(feature = "alloc")]
	pub(crate) fn bitptr(&self) -> BitPtr<T> {
		self.inner.bitptr()
	}
}

impl<'a, C, T> DoubleEndedIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.inner.split_last().map(|(b, r)| {
			self.inner = r;
			b
		})
	}
}

impl<'a, C, T> ExactSizeIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		self.inner.split_first().map(|(b, r)| {
			self.inner = r;
			b
		})
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		if n >= self.len() {
			self.inner = BitSlice::empty();
			return None;
		}
		self.inner = &self.inner[n ..];
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for reverse chunked iteration over a `BitSlice`.
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
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let len = self.inner.len();
		let rem = len % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let (head, rest) = self.inner.split_at(size);
		self.inner = rest;
		Some(head)
	}
}

impl<'a, C, T> ExactSizeIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let len = self.inner.len();
		let size = cmp::min(len, self.width);
		let (rest, tail) = self.inner.split_at(len - size);
		self.inner = rest;
		Some(tail)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.inner.is_empty() {
			return (0, Some(0));
		}
		let len = self.inner.len();
		let (len, rem) = (len / self.width, len % self.width);
		let len = len + (rem > 0) as usize;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		if end >= self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		//  Can’t underflow because of the check above
		let end = self.inner.len() - end;
		let start = end.checked_sub(self.width).unwrap_or(0);
		let nth = &self.inner[start .. end];
		self.inner = &self.inner[.. start];
		Some(nth)
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for mutable reverse chunked iteration over a `BitSlice`.
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
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let rem = self.inner.len() % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, rest) = tmp.split_at_mut(size);
		self.inner = rest;
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

	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let size = cmp::min(self.inner.len(), self.width);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let tlen = tmp.len();
		let (rest, tail) = tmp.split_at_mut(tlen - size);
		self.inner = rest;
		Some(tail)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.inner.is_empty() {
			return (0, Some(0));
		}
		let len = self.inner.len();
		let (len, rem) = (len / self.width, len % self.width);
		let len = len + (rem > 0) as usize;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		if end >= self.inner.len() || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		//  Can’t underflow because of the check above
		let end = self.inner.len() - end;
		let start = end.checked_sub(self.width).unwrap_or(0);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (rest, tail) = tmp.split_at_mut(start);
		let (nth, _) = tail.split_at_mut(end - start);
		self.inner = rest;
		Some(nth)
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for reverse exact iteration over a `BitSlice`.
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
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, rest) = self.inner.split_at(self.width);
		self.inner = rest;
		Some(head)
	}
}

impl<'a, C, T> ExactSizeIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (rest, tail) = self.inner.split_at(self.inner.len() - self.width);
		self.inner = rest;
		Some(tail)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let n = self.inner.len() / self.width;
		(n, Some(n))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		if end >= self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let (rest, _) = self.inner.split_at(self.inner.len() - end);
		self.inner = rest;
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for mutable reverse exact chunked iteration over a `BitSlice`.
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
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, rest) = tmp.split_at_mut(self.width);
		self.inner = rest;
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

	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let tlen = tmp.len();
		let (rest, tail) = tmp.split_at_mut(tlen - self.width);
		self.inner = rest;
		Some(tail)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let n = self.inner.len() / self.width;
		(n, Some(n))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		if end >= self.inner.len() || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let tlen = tmp.len();
		let (rest, _) = tmp.split_at_mut(tlen - end);
		self.inner = rest;
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for sliding-window iteration over a `BitSlice`.
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

impl<'a, C, T> ExactSizeIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

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

	fn count(self) -> usize {
		self.len()
	}

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

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

#[cfg(test)]
mod tests {
	use crate::{
		bits::{
			Bits,
			BitsMut,
		},
		cursor::{
			BigEndian,
			LittleEndian,
		},
		slice::BitSlice,
	};

	#[test]
	fn iter() {
		let src = 0x0FC3u16;
		let bits = src.bits::<BigEndian>();
		let mut iter = bits.into_iter();

		assert_eq!(ExactSizeIterator::len(&iter), 16);
		assert_eq!(iter.next(), Some(false));
		assert_eq!(iter.next_back(), Some(true));
		assert_eq!(iter.nth(3), Some(true));
		assert_eq!(iter.size_hint(), (10, Some(10)));
		assert_eq!(iter.count(), 10);

		assert!(bits.into_iter().nth(16).is_none());
		assert_eq!(bits.into_iter().last(), Some(true));
	}

	#[test]
	fn chunks() {
		let src = 0xA53Cu16;
		let bits = src.bits::<BigEndian>();
		let mut chunks = bits.chunks(5);

		//  [0 .. 5], [5 .. 10], [10 .. 15], [15 .. 16]
		assert_eq!(ExactSizeIterator::len(&chunks), 4);
		assert_eq!(chunks.next(), Some(&bits[.. 5]));
		assert_eq!(chunks.next_back(), Some(&bits[15 ..]));
		assert_eq!(chunks.next_back(), Some(&bits[10 .. 15]));
		assert_eq!(chunks.nth(0), Some(&bits[5 .. 10]));
		assert_eq!(chunks.size_hint(), (0, Some(0)));
		assert!(chunks.next().is_none());

		assert_eq!(bits.chunks(2).count(), 8);
		assert!(bits.chunks(4).nth(5).is_none());
		assert_eq!(bits.chunks(3).last(), Some(&bits[15 .. 16]));

		let empty = BitSlice::<BigEndian, u32>::empty();
		assert!(empty.chunks(1).next_back().is_none());
	}

	#[test]
	fn chunks_mut() {
		let mut raw = 0xC53Au16;
		let mut src = raw;
		let bits = src.bits_mut::<BigEndian>();
		let mut chunks = bits.chunks_mut(5);

		//  [0 .. 5], [5 .. 10], [10 .. 15], [15 .. 16]
		assert_eq!(ExactSizeIterator::len(&chunks), 4);
		assert_eq!(chunks.next(), Some(&mut raw.bits_mut::<BigEndian>()[.. 5]));
		let tmp = chunks.nth(0).unwrap();
		assert!(!tmp[1]);
		*tmp.at(1) = true;
		assert!(tmp[1]);
		assert_eq!(chunks.next_back(), Some(&mut raw.bits_mut::<BigEndian>()[15 ..]));
		assert_eq!(chunks.size_hint(), (1, Some(1)));

		assert_eq!(bits.chunks_mut(2).count(), 8);
		assert!(bits.chunks_mut(4).nth(5).is_none());
		assert_eq!(bits.chunks_mut(3).last(), Some(&mut raw.bits_mut::<BigEndian>()[15 ..]));

		let empty = BitSlice::<BigEndian, u32>::empty_mut();
		assert!(empty.chunks_mut(1).next_back().is_none());
		assert!(empty.chunks_mut(1).next().is_none());
		assert_eq!(empty.chunks_mut(1).size_hint(), (0, Some(0)));
	}

	#[test]
	fn chunks_exact() {
		let src = 0xA53Cu16;
		let bits = src.bits::<BigEndian>();
		let mut chunks = bits.chunks_exact(5);

		//  [0 .. 5], [5 .. 10], [10 .. 15] // [15 .. 16]
		assert_eq!(ExactSizeIterator::len(&chunks), 3);
		assert_eq!(chunks.next(), Some(&bits[.. 5]));
		assert_eq!(chunks.next_back(), Some(&bits[10 .. 15]));
		assert_eq!(chunks.nth(0), Some(&bits[5 .. 10]));
		assert_eq!(chunks.size_hint(), (0, Some(0)));

		assert_eq!(chunks.remainder(), &bits[15 ..]);

		assert!(chunks.next().is_none());
		assert!(chunks.next_back().is_none());
		assert!(chunks.nth(0).is_none());
		assert_eq!(chunks.clone().count(), 0);
		assert!(chunks.last().is_none());
	}

	#[test]
	fn chunks_exact_mut() {
		let mut raw = 0x0123u16;
		let mut src = raw;
		let bits = src.bits_mut::<BigEndian>();
		let mut chunks = bits.chunks_exact_mut(5);

		//  [0 .. 5], [5 .. 10], [10 .. 15] // [15 .. 16]
		assert_eq!(ExactSizeIterator::len(&chunks), 3);
		assert_eq!(chunks.next(), Some(&mut raw.bits_mut::<BigEndian>()[.. 5]));
		assert_eq!(chunks.next_back(), Some(&mut raw.bits_mut::<BigEndian>()[10 .. 15]));
		assert_eq!(chunks.nth(0), Some(&mut raw.bits_mut::<BigEndian>()[5 .. 10]));
		assert_eq!(chunks.size_hint(), (0, Some(0)));

		assert_eq!(chunks.into_remainder(), &mut raw.bits_mut::<BigEndian>()[15 ..]);

		let empty = BitSlice::<LittleEndian, u32>::empty_mut();
		let mut chunks = empty.chunks_exact_mut(1);
		assert!(chunks.next().is_none());
		assert!(chunks.next_back().is_none());
		assert!(chunks.nth(0).is_none());
		assert!(chunks.last().is_none());
		assert_eq!(empty.chunks_exact_mut(1).count(), 0);
	}

	#[test]
	fn rchunks() {
		let src = 0xFEDCu16;
		let bits = src.bits::<LittleEndian>();
		let mut rchunks = bits.rchunks(5);

		//  [11 .. 16], [6 .. 11], [1 .. 6], [0 .. 1]
		assert_eq!(ExactSizeIterator::len(&rchunks), 4);
		assert_eq!(rchunks.next(), Some(&bits[11 ..]));
		assert_eq!(rchunks.next_back(), Some(&bits[.. 1]));
		assert_eq!(rchunks.next_back(), Some(&bits[1 .. 6]));
		assert_eq!(rchunks.nth(0), Some(&bits[6 .. 11]));
		assert_eq!(rchunks.size_hint(), (0, Some(0)));

		assert!(rchunks.next().is_none());
		assert!(rchunks.next_back().is_none());
		assert_eq!(rchunks.count(), 0);

		assert!(bits.rchunks(5).nth(5).is_none());
		let empty = BitSlice::<LittleEndian, u32>::empty();
		assert!(empty.rchunks(1).last().is_none());
	}

	#[test]
	fn rchunks_mut() {
		let mut raw = 0xBA98u16;
		let mut src = raw;
		let bits = src.bits_mut::<LittleEndian>();
		let mut rchunks = bits.rchunks_mut(5);

		//  [11 .. 16], [6 .. 11], [1 .. 6], [0 .. 1]
		assert_eq!(ExactSizeIterator::len(&rchunks), 4);
		assert_eq!(rchunks.next(), Some(&mut raw.bits_mut::<LittleEndian>()[11 ..]));
		let tmp = rchunks.nth(0).unwrap();
		assert!(!tmp[2]);
		*tmp.at(2) = true;
		assert!(tmp[2]);
		assert_eq!(rchunks.next_back(), Some(&mut raw.bits_mut::<LittleEndian>()[.. 1]));
		assert_eq!(rchunks.size_hint(), (1, Some(1)));

		assert_eq!(bits.rchunks_mut(2).count(), 8);
		assert!(bits.rchunks_mut(4).nth(5).is_none());
		assert_eq!(bits.rchunks_mut(3).last(), Some(&mut raw.bits_mut::<LittleEndian>()[.. 1]));

		let empty = BitSlice::<LittleEndian, u32>::empty_mut();
		assert!(empty.rchunks_mut(1).next_back().is_none());
		assert!(empty.rchunks_mut(1).next().is_none());
		assert_eq!(empty.rchunks_mut(1).size_hint(), (0, Some(0)));
	}

	#[test]
	fn rchunks_exact() {
		let src = 0x7654u16;
		let bits = src.bits::<LittleEndian>();
		let mut rchunks = bits.rchunks_exact(5);

		//  [11 .. 16], [6 .. 11], [1 .. 6] // [0 .. 1]
		assert_eq!(ExactSizeIterator::len(&rchunks), 3);
		assert_eq!(rchunks.next(), Some(&bits[11 ..]));
		assert_eq!(rchunks.next_back(), Some(&bits[1 .. 6]));
		assert_eq!(rchunks.nth(0), Some(&bits[6 .. 11]));
		assert_eq!(rchunks.size_hint(), (0, Some(0)));

		assert_eq!(rchunks.remainder(), &bits[.. 1]);

		assert!(rchunks.next().is_none());
		assert!(rchunks.next_back().is_none());
		assert!(rchunks.nth(0).is_none());
		assert_eq!(rchunks.clone().count(), 0);
		assert!(rchunks.last().is_none());
	}

	#[test]
	fn rchunks_exact_mut() {
		let mut raw = 0x0123u16;
		let mut src = raw;
		let bits = src.bits_mut::<LittleEndian>();
		let mut rchunks = bits.rchunks_exact_mut(5);

		//  [11 .. 16], [6 .. 11], [1 .. 6] // [0 .. 1]
		assert_eq!(ExactSizeIterator::len(&rchunks), 3);
		assert_eq!(rchunks.next(), Some(&mut raw.bits_mut::<LittleEndian>()[11 ..]));
		assert_eq!(rchunks.next_back(), Some(&mut raw.bits_mut::<LittleEndian>()[1 .. 6]));
		assert_eq!(rchunks.nth(0), Some(&mut raw.bits_mut::<LittleEndian>()[6 .. 11]));
		assert_eq!(rchunks.size_hint(), (0, Some(0)));

		assert_eq!(rchunks.into_remainder(), &mut raw.bits_mut::<LittleEndian>()[.. 1]);

		let empty = BitSlice::<BigEndian, u32>::empty_mut();
		let mut rchunks = empty.rchunks_exact_mut(1);
		assert!(rchunks.next().is_none());
		assert!(rchunks.next_back().is_none());
		assert!(rchunks.nth(0).is_none());
		assert!(rchunks.last().is_none());
		assert_eq!(empty.rchunks_exact_mut(1).count(), 0);
	}

	#[test]
	fn windows() {
		let src = 0xA5A5u16;
		let bits = src.bits::<BigEndian>();
		let mut windows = bits.windows(9);

		//  [0 .. 9], …, [7 .. 16]
		assert_eq!(ExactSizeIterator::len(&windows), 8);
		assert_eq!(windows.next(), Some(&bits[.. 9]));
		assert_eq!(windows.next_back(), Some(&bits[7 ..]));
		assert_eq!(windows.nth(3), Some(&bits[4 .. 13]));
		assert_eq!(windows.size_hint(), (2, Some(2)));
		assert_eq!(windows.clone().count(), 2);

		windows.nth(2);
		assert!(windows.next_back().is_none());
		assert!(windows.next().is_none());
		assert_eq!(windows.size_hint(), (0, Some(0)));
		assert!(windows.last().is_none());
	}
}
