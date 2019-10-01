//! `BitBox` miscellaneous trait implementations.

use super::BitBox;

use crate::{
	cursor::Cursor,
	pointer::BitPtr,
	store::BitStore,
	slice::BitSlice,
	vec::BitVec,
};

use core::{
	any::type_name,
	cmp::Ordering,
	fmt::{
		self,
		Debug,
		Display,
		Formatter,
	},
	hash::{
		Hash,
		Hasher,
	},
	marker::PhantomData,
};

#[cfg(feature = "alloc")]
use alloc::{
	borrow::{
		Borrow,
		BorrowMut,
		ToOwned,
	},
	boxed::Box,
};

impl<C, T> Borrow<BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn borrow(&self) -> &BitSlice<C, T> {
		self.as_bits()
	}
}

impl<C, T> BorrowMut<BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn borrow_mut(&mut self) -> &mut BitSlice<C, T> {
		self.as_bits_mut()
	}
}

impl<C, T> Clone for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn clone(&self) -> Self {
		self.as_bits().to_owned().into_boxed_bitslice()
	}
}

impl<C, T> Eq for BitBox<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> Ord for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn cmp(&self, rhs: &Self) -> Ordering {
		self.as_bits().cmp(rhs.as_bits())
	}
}

impl<A, B, C, D> PartialEq<BitBox<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitBox<C, D>) -> bool {
		self.as_bits().eq(rhs.as_bits())
	}
}

impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		self.as_bits().eq(rhs)
	}
}

impl<A, B, C, D> PartialEq<&BitSlice<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &&BitSlice<C, D>) -> bool {
		self.as_bits().eq(&**rhs)
	}
}

impl<A, B, C, D> PartialEq<BitBox<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitBox<C, D>) -> bool {
		self.eq(rhs.as_bits())
	}
}

impl<A, B, C, D> PartialOrd<BitBox<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitBox<C, D>) -> Option<Ordering> {
		self.as_bits().partial_cmp(rhs.as_bits())
	}
}

impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<Ordering> {
		self.as_bits().partial_cmp(rhs)
	}
}

impl<A, B, C, D> PartialOrd<&BitSlice<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &&BitSlice<C, D>) -> Option<Ordering> {
		self.as_bits().partial_cmp(&**rhs)
	}
}

impl<A, B, C, D> PartialOrd<BitBox<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitBox<C, D>) -> Option<Ordering> {
		self.partial_cmp(rhs.as_bits())
	}
}

impl<C, T> AsMut<BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn as_mut(&mut self) -> &mut BitSlice<C, T> {
		self.as_bits_mut()
	}
}

impl<C, T> AsMut<[T]> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn as_mut(&mut self) -> &mut [T] {
		self.as_bits_mut().as_mut()
	}
}

impl<C, T> AsRef<BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn as_ref(&self) -> &BitSlice<C, T> {
		self.as_bits()
	}
}

impl<C, T> AsRef<[T]> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn as_ref(&self) -> &[T] {
		self.as_bits().as_ref()
	}
}

impl<C, T> From<&BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn from(src: &BitSlice<C, T>) -> Self {
		Self::from_bitslice(src)
	}
}

impl<C, T> From<&[T]> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn from(src: &[T]) -> Self {
		Self::from_slice(src)
	}
}

impl<C, T> From<BitVec<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn from(src: BitVec<C, T>) -> Self {
		src.into_boxed_bitslice()
	}
}

impl<C, T> From<Box<[T]>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn from(src: Box<[T]>) -> Self {
		Self::from_boxed_slice(src)
	}
}

impl<C, T> Into<Box<[T]>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn into(self) -> Box<[T]> {
		self.into_boxed_slice()
	}
}

impl<C, T> Default for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn default() -> Self {
		Self {
			_cursor: PhantomData,
			bitptr: BitPtr::default(),
		}
	}
}

impl<C, T> Debug for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		f.write_str("BitBox<")?;
		f.write_str(type_name::<C>())?;
		f.write_str(", ")?;
		f.write_str(type_name::<T>())?;
		f.write_str("> ")?;
		Display::fmt(self.as_bits(), f)
	}
}

impl<C, T> Display for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		Display::fmt(self.as_bits(), f)
	}
}

impl<C, T> Hash for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn hash<H>(&self, hasher: &mut H)
	where H: Hasher {
		self.as_bits().hash(hasher)
	}
}

/// `BitBox` is safe to move across thread boundaries, as is `&mut BitBox`.
unsafe impl<C, T> Send for BitBox<C, T>
where C: Cursor, T: BitStore {}

/// `&BitBox` is safe to move across thread boundaries.
unsafe impl<C, T> Sync for BitBox<C, T>
where C: Cursor, T: BitStore {}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::prelude::*;

	#[test]
	fn borrow() {
		let mut bits = bitbox![1; 4];
		assert_eq!(
			Borrow::<BitSlice::<_, _>>::borrow(&bits),
			&15u8.bits::<LittleEndian>()[.. 4],
		);
		assert_eq!(
			BorrowMut::<BitSlice::<_, _>>::borrow_mut(&mut bits),
			&mut 15u8.bits_mut::<BigEndian>()[4 ..],
		);
	}

	#[test]
	fn cmp() {
		let a = bitbox![0, 0, 1];
		let b = bitbox![0, 1, 0];
		let c = bitbox![0, 1, 0];

		assert!(a < b);
		assert!(b <= c);
		assert!(b == c);
		assert!(c >= b);
		assert!(b > a);
		assert!(c != a.as_bits());

		assert_eq!(Ord::cmp(&a, &b), Ordering::Less);
		assert_eq!(PartialOrd::partial_cmp(&a, &&*b), Some(Ordering::Less));
		assert_eq!(PartialOrd::partial_cmp(&a, &b), Some(Ordering::Less));
		assert!(!PartialEq::eq(&a, &&*b));
	}

	#[test]
	fn as_ref() {
		let mut a = bitbox![BigEndian, u8; 0, 0, 0, 1, 0, 0, 0, 1];
		assert_eq!(
			AsMut::<BitSlice<BigEndian, u8>>::as_mut(&mut a),
			0x11u8.bits_mut::<BigEndian>(),
		);
		assert_eq!(
			AsRef::<BitSlice<BigEndian, u8>>::as_ref(&a),
			0x11u8.bits::<BigEndian>(),
		);
		assert_eq!(AsMut::<[u8]>::as_mut(&mut a), &mut [0x11u8]);
		assert_eq!(AsRef::<[u8]>::as_ref(&a), &[0x11u8]);
	}

	#[test]
	fn from() {
		let src_bits = 0xA5u8.bits::<LittleEndian>();
		let src = [0x5Au8];

		let _: BitBox<_, _> = src_bits.into();
		let _: BitBox<BigEndian, _> = (&src[..]).into();
		let _: BitBox<BigEndian, u8> = bitvec![0; 10].into();
		let _: BitBox<LittleEndian, _> = vec![0x5Au8].into_boxed_slice().into();

		let _: Box<[u8]> = bitbox![LittleEndian, u8; 1; 10].into();

		let _ = BitBox::<BigEndian, u8>::default();
	}

	#[test]
	fn fmt() {
		let bits = bitbox![1; 10];
		assert_eq!(format!("{}", bits), "[11111111, 11]");
		assert_eq!(format!("{:?}", bits), "BitBox<bitvec::cursor::BigEndian, u8> [11111111, 11]");
	}

	#[test]
	#[allow(deprecated)]
	fn hash() {
		let mut hasher = core::hash::SipHasher::new();
		let _ = bitbox![1; 10].hash(&mut hasher);
	}
}
