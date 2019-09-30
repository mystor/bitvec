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
		let (head, tail) = self.inner.split_at(len - size);
		self.inner = head;
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
		use core::cmp::min;
		if self.inner.is_empty() {
			return None;
		}
		let size = min(self.inner.len(), self.width);
		let (head, tail) = self.inner.split_at(size);
		self.inner = tail;
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
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, tail) = self.inner.split_at(self.inner.len() - self.width);
		self.inner = head;
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
		let (head, tail) = self.inner.split_at(self.width);
		self.inner = tail;
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
		let (_, tail) = self.inner.split_at(start);
		self.inner = tail;
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
		let (_, tail) = tmp.split_at_mut(start);
		self.inner = tail;
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
		let (head, tail) = self.inner.split_at(size);
		self.inner = tail;
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
		let size = min(len, self.width);
		let (head, tail) = self.inner.split_at(len - size);
		self.inner = head;
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
		// Can't underflow because of the check above
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

	fn next(&mut self) -> Option<Self::Item> {
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
		// Can't underflow because of the check above
		let end = self.inner.len() - end;
		let start = end.checked_sub(self.width).unwrap_or(0);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(start);
		let (nth, _) = tail.split_at_mut(end - start);
		self.inner = head;
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
		let (head, tail) = self.inner.split_at(self.width);
		self.inner = tail;
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
		let (head, tail) = self.inner.split_at(self.inner.len() - self.width);
		self.inner = head;
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
		let (head, _) = self.inner.split_at(self.inner.len() - end);
		self.inner = head;
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
		let (head, _) = tmp.split_at_mut(tlen - end);
		self.inner = head;
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
