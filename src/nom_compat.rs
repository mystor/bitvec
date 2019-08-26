/*! Implementations of `nom` traits for `BitSlice`.

!*/

#![cfg(feature = "nom")]

use crate::{
	cursor::Cursor,
	slice::BitSlice,
	store::BitStore,
};

use core::{
	iter::FusedIterator,
	mem,
	ops::{
		Range,
		RangeFrom,
		RangeFull,
		RangeInclusive,
		RangeTo,
		RangeToInclusive,
	},
};

use nom::{
	AsBytes,
	Err,
	InputIter,
	InputLength,
	InputTake,
	InputTakeAtPosition,
	Needed,
	Slice,
	Offset,
	error::{
		ErrorKind,
		ParseError,
	},
};

impl<C> AsBytes for BitSlice<C, u8>
where C: Cursor {
	fn as_bytes(&self) -> &[u8] {
		self.as_slice()
	}
}

impl<'a, C, T> InputIter for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = Self;
	type Iter = IdxIter<'a, C, T>;
	type IterElem = Iter<'a, C, T>;

	fn iter_indices(&self) -> Self::Iter {
		IdxIter {
			inner: self,
			cursor: 0,
		}
	}

	fn iter_elements(&self) -> Self::IterElem {
		Iter { inner: self }
	}

	fn position<P>(&self, pred: P) -> Option<usize>
	where P: Fn(Self::Item) -> bool {
		self.iter_indices().find(|(_, bits)| pred(*bits)).map(|(idx, _)| idx)
	}

	fn slice_index(&self, count: usize) -> Option<usize> {
		if count <= self.len() {
			Some(count)
		}
		else {
			None
		}
	}
}

impl<C, T> InputLength for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn input_len(&self) -> usize {
		self.len()
	}
}

impl<C, T> InputTake for &BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn take(&self, count: usize) -> Self {
		&self[.. count]
	}

	fn take_split(&self, count: usize) -> (Self, Self) {
		let (head, rest) = self.split_at(count);
		(rest, head)
	}
}

impl<'a, C, T> InputTakeAtPosition for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn split_at_position<P, E>(&self, pred: P) -> Result<(Self, Self), Err<E>>
	where P: Fn(Self::Item) -> bool, E: ParseError<Self> {
		if let Some(idx) = self.position(pred) {
			return Ok(self.take_split(idx));
		}
		Err(Err::Incomplete(Needed::Size(1)))
	}

	fn split_at_position1<P, E>(
		&self,
		pred: P,
		err: ErrorKind,
	) -> Result<(Self, Self), Err<E>>
	where P: Fn(Self::Item) -> bool, E: ParseError<Self> {
		match self.position(pred) {
			Some(0) => Err(Err::Error(E::from_error_kind(self, err))),
			Some(idx) => Ok(self.take_split(idx)),
			None => Err(Err::Incomplete(Needed::Size(1))),
		}
	}

	fn split_at_position_complete<P, E>(
		&self,
		pred: P
	) -> Result<(Self, Self), Err<E>>
	where P: Fn(Self::Item) -> bool, E: ParseError<Self> {
		self.split_at_position::<P, E>(pred)
			.or_else(|_| Ok((BitSlice::empty(), self)))
	}

	fn split_at_position1_complete<P, E>(
		&self,
		pred: P,
		err: ErrorKind,
	) -> Result<(Self, Self), Err<E>>
	where P: Fn(Self::Item) -> bool, E: ParseError<Self> {
		match self.position(pred) {
			Some(0) => Err(Err::Error(E::from_error_kind(self, err))),
			Some(idx) => Ok(self.take_split(idx)),
			None => Ok((BitSlice::empty(), self))
		}
	}
}

impl<C, T> Offset for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn offset(&self, other: &Self) -> usize {
		self.offset_from(other)
	}
}

impl<'a, C, T> Slice<Range<usize>> for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn slice(&self, range: Range<usize>) -> Self {
		&self[range]
	}
}

impl<'a, C, T> Slice<RangeFrom<usize>> for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn slice(&self, range: RangeFrom<usize>) -> Self {
		&self[range]
	}
}

impl<'a, C, T> Slice<RangeFull> for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn slice(&self, range: RangeFull) -> Self {
		&self[range]
	}
}

impl<'a, C, T> Slice<RangeInclusive<usize>> for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn slice(&self, range: RangeInclusive<usize>) -> Self {
		&self[range]
	}
}

impl<'a, C, T> Slice<RangeTo<usize>> for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn slice(&self, range: RangeTo<usize>) -> Self {
		&self[range]
	}
}

impl<'a, C, T> Slice<RangeToInclusive<usize>> for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn slice(&self, range: RangeToInclusive<usize>) -> Self {
		&self[range]
	}
}

/** Produces an iterator over the remnant of the input.

The first call to `.next()` yields the slice as it was input into the iterator;
each call after that removes one more bit from the head of the slice, until the
input is drained.

This behavior is chosen since inspecting only one bit at a time provides
essentially no information, and it is expected that the consumer will be looking
for a bit pattern.
**/
pub struct IdxIter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	inner: &'a BitSlice<C, T>,
	cursor: usize,
}

impl<'a, C, T> ExactSizeIterator for IdxIter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for IdxIter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for IdxIter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = (usize, &'a BitSlice<C, T>);

	fn next(&mut self) -> Option<Self::Item> {
		let out = (self.cursor, self.inner);
		self.cursor += 1;
		let (_, rest) = self.inner.split_first()?;
		self.inner = rest;
		Some(out)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.inner.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		if n >= self.inner.len() {
			self.inner = BitSlice::empty();
			self.cursor = usize::max_value();
			return None;
		}
		self.inner = &self.inner[n ..];
		self.cursor += n;
		self.next()
	}

	fn last(self) -> Option<Self::Item> {
		match self.inner.len() {
			0 => None,
			len => Some((self.cursor + len - 1, &self.inner[len - 1 ..])),
		}
	}
}

pub struct Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	inner: &'a BitSlice<C, T>,
}

impl<'a, C, T> ExactSizeIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		let (_, rest) = self.inner.split_first()?;
		mem::replace(&mut self.inner, rest).into()
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.inner.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		if n >= self.inner.len() {
			self.inner = BitSlice::empty();
			return None;
		}
		self.inner = &self.inner[n ..];
		self.next()
	}

	fn last(self) -> Option<Self::Item> {
		match self.inner.len() {
			0 => None,
			len => Some(&self.inner[len - 1 ..])
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
}
