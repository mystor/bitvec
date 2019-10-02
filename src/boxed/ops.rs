//! `BitBox` operator trait implementations.

use super::BitBox;

use crate::{
	cursor::Cursor,
	store::BitStore,
	slice::BitSlice,
};

use core::{
	ops::{
		Add,
		AddAssign,
		BitAnd,
		BitAndAssign,
		BitOr,
		BitOrAssign,
		BitXor,
		BitXorAssign,
		Deref,
		DerefMut,
		Index,
		IndexMut,
		Range,
		RangeFrom,
		RangeFull,
		RangeInclusive,
		RangeTo,
		RangeToInclusive,
		Neg,
		Not,
		Shl,
		ShlAssign,
		Shr,
		ShrAssign,
	},
};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

impl<C, T> Add<Self> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn add(mut self, addend: Self) -> Self::Output {
		self += addend;
		self
	}
}

impl<C, T> AddAssign for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn add_assign(&mut self, addend: Self) {
		self.as_bits_mut().add_assign(addend.as_bits())
	}
}

impl<C, T, I> BitAnd<I> for BitBox<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	fn bitand(mut self, rhs: I) -> Self::Output {
		self &= rhs;
		self
	}
}

impl<C, T, I> BitAndAssign<I> for BitBox<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	fn bitand_assign(&mut self, rhs: I) {
		self.as_bits_mut().bitand_assign(rhs);
	}
}

impl<C, T, I> BitOr<I> for BitBox<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	fn bitor(mut self, rhs: I) -> Self::Output {
		self |= rhs;
		self
	}
}

impl<C, T, I> BitOrAssign<I> for BitBox<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	fn bitor_assign(&mut self, rhs: I) {
		self.as_bits_mut().bitor_assign(rhs);
	}
}

impl<C, T, I> BitXor<I> for BitBox<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	fn bitxor(mut self, rhs: I) -> Self::Output {
		self ^= rhs;
		self
	}
}

impl<C, T, I> BitXorAssign<I> for BitBox<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	fn bitxor_assign(&mut self, rhs: I) {
		self.as_bits_mut().bitxor_assign(rhs);
	}
}

impl<C, T> Deref for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Target = BitSlice<C, T>;

	fn deref(&self) -> &Self::Target {
		self.as_bits()
	}
}

impl<C, T> DerefMut for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.as_bits_mut()
	}
}

impl<C, T> Drop for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn drop(&mut self) {
		let ptr = self.as_mut_slice().as_mut_ptr();
		let len = self.as_slice().len();
		//  Run the `Box<[T]>` destructor.
		drop(unsafe { Vec::from_raw_parts(ptr, 0, len) }.into_boxed_slice());
	}
}

impl<C, T> Index<usize> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = bool;

	fn index(&self, index: usize) -> &Self::Output {
		&self.as_bits()[index]
	}
}

impl<C, T> Index<Range<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: Range<usize>) -> &Self::Output {
		&self.as_bits()[range]
	}
}

impl<C, T> IndexMut<Range<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: Range<usize>) -> &mut Self::Output {
		&mut self.as_bits_mut()[range]
	}
}

impl<C, T> Index<RangeFrom<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: RangeFrom<usize>) -> &Self::Output {
		&self.as_bits()[range]
	}
}

impl<C, T> IndexMut<RangeFrom<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: RangeFrom<usize>) -> &mut Self::Output {
		&mut self.as_bits_mut()[range]
	}
}

impl<C, T> Index<RangeFull> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, _: RangeFull) -> &Self::Output {
		self.as_bits()
	}
}

impl<C, T> IndexMut<RangeFull> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
		self.as_bits_mut()
	}
}

impl<C, T> Index<RangeInclusive<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: RangeInclusive<usize>) -> &Self::Output {
		&self.as_bits()[range]
	}
}

impl<C, T> IndexMut<RangeInclusive<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: RangeInclusive<usize>) -> &mut Self::Output {
		&mut self.as_bits_mut()[range]
	}
}

impl<C, T> Index<RangeTo<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: RangeTo<usize>) -> &Self::Output {
		&self.as_bits()[range]
	}
}

impl<C, T> IndexMut<RangeTo<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: RangeTo<usize>) -> &mut Self::Output {
		&mut self.as_bits_mut()[range]
	}
}

impl<C, T> Index<RangeToInclusive<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: RangeToInclusive<usize>) -> &Self::Output {
		&self.as_bits()[range]
	}
}

impl<C, T> IndexMut<RangeToInclusive<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(
		&mut self,
		range: RangeToInclusive<usize>,
	) -> &mut Self::Output {
		&mut self.as_bits_mut()[range]
	}
}

impl<C, T> Neg for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn neg(mut self) -> Self::Output {
		let _ = self.as_bits_mut().neg();
		self
	}
}

impl<C, T> Not for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn not(mut self) -> Self::Output {
		let _ = self.as_bits_mut().not();
		self
	}
}

impl<C, T> Shl<usize> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn shl(mut self, shamt: usize) -> Self::Output {
		self <<= shamt;
		self
	}
}

impl<C, T> ShlAssign<usize> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn shl_assign(&mut self, shamt: usize) {
		self.as_bits_mut().shl_assign(shamt);
	}
}

impl<C, T> Shr<usize> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn shr(mut self, shamt: usize) -> Self::Output {
		self >>= shamt;
		self
	}
}

impl<C, T> ShrAssign<usize> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn shr_assign(&mut self, shamt: usize) {
		self.as_bits_mut().shr_assign(shamt);
	}
}

#[cfg(test)]
mod tests {
	use crate::prelude::*;

	#[test]
	fn arith() {
		let a = bitbox![0, 1, 1, 0];

		assert_eq!(a.clone() + bitbox![1, 0, 0, 1], bitbox![1; 4]);

		assert_eq!(-bitbox![1; 4], bitbox![0, 0, 0, 1]);

		assert_eq!(a.clone() << 1, bitbox![1, 1, 0, 0]);
		assert_eq!(a.clone() >> 1, bitbox![0, 0, 1, 1]);
	}

	#[test]
	fn bit_arith() {
		let a = bitbox![0, 1, 0, 1];
		let b = bitbox![0, 0, 1, 1];

		assert_eq!(a.clone() & b.clone(), bitbox![0, 0, 0, 1]);
		assert_eq!(a.clone() | b.clone(), bitbox![0, 1, 1, 1]);
		assert_eq!(a.clone() ^ b.clone(), bitbox![0, 1, 1, 0]);
		assert_eq!(!a, bitbox![1, 0, 1, 0]);
	}

	#[test]
	fn index() {
		let mut bits = bitbox![0, 0, 1, 0, 0];

		assert!(bits[2]);

		assert_eq!(bits[1 .. 4], bitbox![0, 1, 0]);
		assert_eq!(&mut bits[1 .. 4], &mut bitbox![0, 1, 0]);

		assert_eq!(bits[2 ..], bitbox![1, 0, 0]);
		assert_eq!(&mut bits[2 ..], &mut bitbox![1, 0, 0]);

		assert_eq!(bits[..], bitbox![0, 0, 1, 0, 0]);
		assert_eq!(&mut bits[..], &mut bitbox![0, 0, 1, 0, 0]);

		assert_eq!(bits[1 ..= 3], bitbox![0, 1, 0]);
		assert_eq!(&mut bits[1 ..= 3], &mut bitbox![0, 1, 0]);

		assert_eq!(bits[.. 3], bitbox![0, 0, 1]);
		assert_eq!(&mut bits[.. 3], &mut bitbox![0, 0, 1]);

		assert_eq!(bits[..= 2], bitbox![0, 0, 1]);
		assert_eq!(&mut bits[..= 2], &mut bitbox![0, 0, 1]);
	}
}
