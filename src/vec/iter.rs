//! `BitVec` iterator implementations.

use super::BitVec;

use crate::{
	cursor::Cursor,
	pointer::BitPtr,
	store::BitStore,
	slice::BitSlice,
};

use core::{
	iter::{
		FromIterator,
		FusedIterator,
	},
	ptr::NonNull,
};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

impl<C, T> Extend<bool> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn extend<I: IntoIterator<Item=bool>>(&mut self, src: I) {
		let iter = src.into_iter();
		match iter.size_hint() {
			(_, Some(hi)) => self.reserve(hi),
			(lo, None) => self.reserve(lo),
		}
		iter.for_each(|b| self.push(b));
	}
}

impl<C, T> FromIterator<bool> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn from_iter<I: IntoIterator<Item=bool>>(src: I) -> Self {
		let iter = src.into_iter();
		let mut bv = match iter.size_hint() {
			| (_, Some(len))
			| (len, _)
			=> Self::with_capacity(len),
		};
		for bit in iter {
			bv.push(bit);
		}
		bv
	}
}

impl<C, T> IntoIterator for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Item = bool;
	type IntoIter = IntoIter<C, T>;

	fn into_iter(self) -> Self::IntoIter {
		IntoIter {
			region: self.bitptr,
			bitvec: self,
		}
	}
}

impl<'a, C, T> IntoIterator for &'a BitVec<C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = bool;
	type IntoIter = <&'a BitSlice<C, T> as IntoIterator>::IntoIter;

	fn into_iter(self) -> Self::IntoIter {
		<&'a BitSlice<C, T> as IntoIterator>::into_iter(self)
	}
}

/// State keeper for draining iteration.
pub struct Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Pointer to the `BitVec` being drained.
	pub(super) bitvec: NonNull<BitVec<C, T>>,
	/// Current remaining range to remove.
	pub(super) iter: crate::slice::Iter<'a, C, T>,
	/// Index of the original vector tail to preserve.
	pub(super) tail_start: usize,
	/// Length of the tail.
	pub(super) tail_len: usize,
}

impl<'a, C, T> Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Fills the drain span with another iterator.
	///
	/// If the source exhausts before the drain is filled, then the tail
	/// elements move downwards; otherwise, the tail stays put and the drain is
	/// filled.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `stream`: The source of bits to fill into the drain.
	///
	/// # Returns
	///
	/// - `true` if the drain was filled before the `stream` exhausted.
	/// - `false` if the `stream` exhausted early, and the tail was moved down.
	///
	/// # Type Parameters
	///
	/// - `I`: Any provider of bits.
	fn fill<I>(&mut self, stream: &mut I) -> bool
	where I: Iterator<Item = bool> {
		let bv = unsafe { self.bitvec.as_mut() };
		let drain_from = bv.len();
		let drain_upto = self.tail_start;

		for n in drain_from .. drain_upto {
			if let Some(bit) = stream.next() {
				bv.push(bit);
				continue;
			}
			//  The source has exhausted; move the tail region downwards.
			for (to, from) in (n .. n + self.tail_len).zip(drain_upto ..) {
				unsafe { bv.copy(from, to); }
			}
			self.tail_start = n;
			return false;
		}
		true
	}

	/// Moves the tail span farther back in the vector.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `by`: The amount by which to move the tail span.
	fn move_tail(&mut self, by: usize) {
		let bv = unsafe { self.bitvec.as_mut() };
		bv.reserve(by);
		let new_tail = self.tail_start + by;
		let old_len = bv.len();
		let new_len = self.tail_start + self.tail_len + by;

		unsafe { bv.set_len(new_len); }
		//  Move the bits backward to put them in the new tail region.
		for n in (0 .. self.tail_len).rev() {
			unsafe { bv.copy(self.tail_start + n, new_tail + n); }
		}
		unsafe { bv.set_len(old_len); }

		self.tail_start = new_tail;
	}
}

impl<'a, C, T> DoubleEndedIterator for Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.iter.next_back()
	}
}

impl<'a, C, T> ExactSizeIterator for Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		self.iter.next()
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iter.size_hint()
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		self.iter.nth(n)
	}

	fn last(mut self) -> Option<Self::Item> {
		self.iter.next_back()
	}
}

impl<'a, C, T> Drop for Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn drop(&mut self) { unsafe {
		let bv: &mut BitVec<C, T> = self.bitvec.as_mut();
		//  Get the start of the drained span.
		let start = bv.len();
		//  Get the start of the remnant span.
		let tail = self.tail_start;
		let tail_len = self.tail_len;
		//  Get the full length of the vector,
		let full_len = tail + tail_len;
		//  And the length of the vector after the drain.
		let end_len = start + tail_len;
		//  Inflate the vector to include the remnant span,
		bv.set_len(full_len);
		//  Swap the remnant span down into the drained span,
		for (from, to) in (tail .. full_len).zip(start .. end_len) {
			bv.copy(from, to);
		}
		//  And deflate the vector to fit.
		bv.set_len(end_len);
	} }
}

/// A consuming iterator for `BitVec`.
#[repr(C)]
pub struct IntoIter<C, T>
where C: Cursor, T: BitStore {
	/// Owning descriptor for the allocation. This is not modified by iteration.
	pub(super) bitvec: BitVec<C, T>,
	/// Descriptor for the live portion of the vector as iteration proceeds.
	pub(super) region: BitPtr<T>,
}

impl<C, T> IntoIter<C, T>
where C: Cursor, T: BitStore {
	fn iterator(&self) -> <&BitSlice<C, T> as IntoIterator>::IntoIter {
		self.region.into_bitslice().into_iter()
	}
}

impl<C, T> DoubleEndedIterator for IntoIter<C, T>
where C: Cursor, T: BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let mut slice_iter = self.iterator();
		let out = slice_iter.next_back();
		self.region = slice_iter.bitptr();
		out
	}
}

impl<C, T> ExactSizeIterator for IntoIter<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> FusedIterator for IntoIter<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> Iterator for IntoIter<C, T>
where C: Cursor, T: BitStore {
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		let mut slice_iter = self.iterator();
		let out = slice_iter.next();
		self.region = slice_iter.bitptr();
		out
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iterator().size_hint()
	}

	fn count(self) -> usize {
		self.bitvec.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let mut slice_iter = self.iterator();
		let out = slice_iter.nth(n);
		self.region = slice_iter.bitptr();
		out
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** A splicing iterator for `BitVec`.

This removes a segment from the vector and inserts another bitstream into its
spot. Any bits from the original `BitVec` after the removed segment are kept,
after the inserted bitstream.

Only the removed segment is available for iteration.

# Type Parameters

- `I: Iterator<Item=bool>`: Any bitstream. This will be used to fill the
  removed span.
**/
pub struct Splice<'a, C, T, I>
where C: Cursor, T: 'a + BitStore, I: Iterator<Item=bool> {
	/// Manager for the region to be drained from the vector.
	pub(super) drain: Drain<'a, C, T>,
	/// Bit stream to insert into the drain region.
	pub(super) splice: I,
}

impl<'a, C, T, I> DoubleEndedIterator for Splice<'a, C, T, I>
where C: Cursor, T: 'a + BitStore, I: Iterator<Item=bool> {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.drain.next_back()
	}
}

impl<'a, C, T, I> ExactSizeIterator for Splice<'a, C, T, I>
where C: Cursor, T: 'a + BitStore, I: Iterator<Item=bool> {}

impl<'a, C, T, I> FusedIterator for Splice<'a, C, T, I>
where C: Cursor, T: 'a + BitStore, I: Iterator<Item=bool> {}

//  Forward iteration to the interior drain
impl<'a, C, T, I> Iterator for Splice<'a, C, T, I>
where C: Cursor, T: 'a + BitStore, I: Iterator<Item=bool> {
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		//  If the drain produced a bit, then try to pull a bit from the
		//  replacement. If the replacement produced a bit, push it into the
		//  `BitVec` that the drain is managing. This works because the `Drain`
		//  type truncates the `BitVec` to the front of the region being
		//  drained, then tracks the remainder of the memory.
		self.drain.next().map(|bit| {
			if let Some(new_bit) = self.splice.next() {
				unsafe { self.drain.bitvec.as_mut() }.push(new_bit);
			}
			bit
		})
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.drain.size_hint()
	}

	fn count(self) -> usize {
		self.drain.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		self.drain.nth(n)
	}

	fn last(mut self) -> Option<Self::Item> {
		self.drain.next_back()
	}
}

impl<'a, C, T, I> Drop for Splice<'a, C, T, I>
where C: Cursor, T: 'a + BitStore, I: Iterator<Item=bool> {
	fn drop(&mut self) { unsafe {
		if self.drain.tail_len == 0 {
			self.drain.bitvec.as_mut().extend(self.splice.by_ref());
			return;
		}

		//  Fill the drained span from the splice. If this exhausts the splice,
		//  exit. Note that `Drain::fill` runs from the current `BitVec.len`
		//  value, so the fact that `Splice::next` attempts to push onto the
		//  vector is not a problem here.
		if !self.drain.fill(&mut self.splice) {
			return;
		}

		let (lower, _) = self.splice.size_hint();

		//  If the splice still has data, move the tail to make room for it and
		//  fill.
		if lower > 0 {
			self.drain.move_tail(lower);
			if !self.drain.fill(&mut self.splice) {
				return;
			}
		}

		let mut remnant = self.splice.by_ref().collect::<Vec<_>>().into_iter();
		if remnant.len() > 0 {
			self.drain.move_tail(remnant.len());
			self.drain.fill(&mut remnant);
		}
		//  Drain::drop does the rest
	} }
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		cursor::BigEndian,
	};

	/// This test exists specifically to hit an arm of the `fn extend` match
	/// that is usually missed.
	#[test]
	fn floor_no_ceil() {
		let _ = bitvec![0; 5].extend(lower_only(5));
		let _ = lower_only(10).collect::<BitVec<BigEndian, u32>>();
	}

	#[test]
	fn into_iter() {
		let _ = (&bitvec![0; 10]).into_iter();
	}

	fn lower_only(n: usize) -> LowerOnly<impl Iterator<Item = bool>, bool> {
		LowerOnly {
			inner: core::iter::repeat(true).take(n)
		}
	}

	struct LowerOnly<I, T>
	where I: Iterator<Item = T> {
		inner: I,
	}

	impl<I, T> Iterator for LowerOnly<I, T>
	where I: Iterator<Item = T> {
		type Item = T;
		fn next(&mut self) -> Option<Self::Item> {
			self.inner.next()
		}

		fn size_hint(&self) -> (usize, Option<usize>) {
			(self.inner.size_hint().0, None)
		}
	}
}
