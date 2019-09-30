//! `BitBox` iterator implementations.

use super::BitBox;

use crate::{
	cursor::Cursor,
	store::BitStore,
	slice::BitSlice,
	vec::BitVec,
};

/// Use `BitVec` iteration.
impl<C, T> IntoIterator for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Item = bool;
	type IntoIter = <BitVec<C, T> as IntoIterator>::IntoIter;

	fn into_iter(self) -> Self::IntoIter {
		BitVec::from_boxed_bitslice(self).into_iter()
	}
}

impl<'a, C, T> IntoIterator for &'a BitBox<C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = bool;
	type IntoIter = <&'a BitSlice<C, T> as IntoIterator>::IntoIter;

	fn into_iter(self) -> Self::IntoIter {
		self.as_bits().into_iter()
	}
}
