//! `BitVec` miscellaneous trait implementations.

use super::BitVec;

use crate::{
	boxed::BitBox,
	cursor::Cursor,
	slice::BitSlice,
	store::BitStore,
};

use alloc::borrow::{
	Borrow,
	BorrowMut,
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
	mem,
};

#[cfg(feature = "alloc")]
use alloc::{
	borrow::ToOwned,
	boxed::Box,
	vec::Vec,
};

#[cfg(feature = "std")]
use {
	crate::pointer::BitPtr,
	std::io::{
		self,
		Write,
	},
};

impl<C, T> Borrow<BitSlice<C, T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn borrow(&self) -> &BitSlice<C, T> {
		self.as_bits()
	}
}

impl<C, T> BorrowMut<BitSlice<C, T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn borrow_mut(&mut self) -> &mut BitSlice<C, T> {
		self.as_bits_mut()
	}
}

impl<C, T> Clone for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn clone(&self) -> Self {
		let new_vec = self.as_slice().to_owned();
		let capacity = new_vec.capacity();
		let mut bitptr = self.bitptr;
		unsafe { bitptr.set_pointer(new_vec.as_ptr()); }
		mem::forget(new_vec);
		Self {
			bitptr,
			capacity,
			_cursor: PhantomData,
		}
	}

	fn clone_from(&mut self, other: &Self) {
		//  Ensure that `self` has capacity to receive `other`.
		self.clear();
		let olen = other.len();
		self.reserve(olen);
		unsafe { self.set_len(olen); }

		//  Copy over the backing memory buffer.
		self.as_mut_slice().copy_from_slice(other.as_slice());

		//  Set local head to the source head.
		unsafe { self.bitptr.set_head(other.bitptr.head()); }
	}
}

impl<C, T> Eq for BitVec<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> Ord for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn cmp(&self, rhs: &Self) -> Ordering {
		self.as_bits().cmp(rhs.as_bits())
	}
}

impl<A, B, C, D> PartialEq<BitVec<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		self.as_bits().eq(rhs.as_bits())
	}
}

impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		self.as_bits().eq(rhs)
	}
}

impl<A, B, C, D> PartialEq<&BitSlice<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &&BitSlice<C, D>) -> bool {
		self.as_bits().eq(*rhs)
	}
}

impl<A, B, C, D> PartialOrd<BitVec<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
		self.as_bits().partial_cmp(rhs.as_bits())
	}
}

impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<Ordering> {
		self.as_bits().partial_cmp(rhs)
	}
}

impl<A, B, C, D> PartialOrd<&BitSlice<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &&BitSlice<C, D>) -> Option<Ordering> {
		self.as_bits().partial_cmp(*rhs)
	}
}

impl<C, T> AsMut<BitSlice<C, T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn as_mut(&mut self) -> &mut BitSlice<C, T> {
		self.as_bits_mut()
	}
}

impl<C, T> AsMut<[T]> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn as_mut(&mut self) -> &mut [T] {
		self.as_mut_slice()
	}
}

impl<C, T> AsRef<BitSlice<C, T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn as_ref(&self) -> &BitSlice<C, T> {
		self.as_bits()
	}
}

impl<C, T> AsRef<[T]> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn as_ref(&self) -> &[T] {
		self.as_slice()
	}
}

impl<C, T> From<&BitSlice<C, T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn from(src: &BitSlice<C, T>) -> Self {
		Self::from_bitslice(src)
	}
}

impl<C, T> From<&[bool]> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn from(src: &[bool]) -> Self {
		src.iter().cloned().collect()
	}
}

impl<C, T> From<BitBox<C, T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn from(src: BitBox<C, T>) -> Self {
		Self::from_boxed_bitslice(src)
	}
}

impl<C, T> From<&[T]> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn from(src: &[T]) -> Self {
		Self::from_slice(src)
	}
}

impl<C, T> From<Box<[T]>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn from(src: Box<[T]>) -> Self {
		Self::from_boxed_bitslice(BitBox::from_boxed_slice(src))
	}
}

impl<C, T> Into<Box<[T]>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn into(self) -> Box<[T]> {
		self.into_boxed_slice()
	}
}

impl<C, T> From<Vec<T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn from(src: Vec<T>) -> Self {
		Self::from_vec(src)
	}
}

impl<C, T> Into<Vec<T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn into(self) -> Vec<T> {
		self.into_vec()
	}
}

impl<C, T> Default for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn default() -> Self {
		Self::new()
	}
}

impl<C, T> Debug for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		f.write_str("BitVec<")?;
		f.write_str(type_name::<C>())?;
		f.write_str(", ")?;
		f.write_str(type_name::<T>())?;
		f.write_str("> ")?;
		Display::fmt(&**self, f)
	}
}

impl<C, T> Display for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		Display::fmt(&**self, f)
	}
}

impl<C, T> Hash for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn hash<H>(&self, hasher: &mut H)
	where H: Hasher {
		<BitSlice<C, T> as Hash>::hash(self, hasher)
	}
}

#[cfg(feature = "std")]
impl<C, T> Write for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
		let amt = core::cmp::min(buf.len(), (BitPtr::<T>::MAX_BITS - self.len()) >> 3);
		self.extend(<&BitSlice<C, u8>>::from(buf));
		Ok(amt)
	}

	fn flush(&mut self) -> io::Result<()> { Ok(()) }
}

/// `BitVec` is safe to move across thread boundaries, as is `&mut BitVec`.
unsafe impl<C, T> Send for BitVec<C, T>
where C: Cursor, T: BitStore {}

/// `&BitVec` is safe to move across thread boundaries.
unsafe impl<C, T> Sync for BitVec<C, T>
where C: Cursor, T: BitStore {}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::prelude::*;

	#[test]
	fn borrow() {
		let mut a = bitvec![1; 10];
		Borrow::<BitSlice<BigEndian, u8>>::borrow(&a);
		BorrowMut::<BitSlice<BigEndian, u8>>::borrow_mut(&mut a);
	}

	#[test]
	fn clone() {
		let a = bitvec![1; 10];
		let mut b = bitvec![];
		b.clone_from(&a);

		assert_eq!(a, b);
	}

	#[test]
	fn cmp() {
		let a = bitvec![0, 0, 1];
		let b = bitvec![0, 0, 1, 0];
		let c = b.clone();
		let d = bitvec![0, 1, 0, 0];

		assert!(a < b);
		assert!(b <= c);
		assert!(b == c);
		assert!(c < d);
		assert!(c != d.as_bits());

		assert_eq!(a.cmp(&b), Ordering::Less);
		assert!(!a.eq(b.as_bits()));
		assert_eq!(b.partial_cmp(c.as_bits()), Some(Ordering::Equal));
		assert_eq!(c.partial_cmp(&d.as_bits()), Some(Ordering::Less));
	}

	#[test]
	fn conv() {
		let mut bv = bitvec![1; 10];

		AsMut::<BitSlice<_, _>>::as_mut(&mut bv).set(0, false);
		AsMut::<[_]>::as_mut(&mut bv)[1] = 255;
		assert_eq!(AsRef::<BitSlice<_, _>>::as_ref(&bv).get(0), Some(false));
		assert_eq!(AsRef::<[_]>::as_ref(&bv)[1], 255);

		assert_eq!(BitVec::from(0xA5u8.bits::<BigEndian>()).len(), 8);
		assert_eq!(BitVec::<BigEndian, u16>::from(&[true, false][..]).len(), 2);
		assert_eq!(BitVec::<BigEndian, _>::from(&[1u8, 2][..]).len(), 16);
		assert_eq!(BitVec::<BigEndian, _>::from(vec![1u8, 2].into_boxed_slice()).len(), 16);
		assert_eq!(Into::<Box<[_]>>::into(bitvec![1; 16]).len(), 2);
		assert_eq!(BitVec::<LittleEndian, _>::from(vec![1u8, 2]).len(), 16);
		assert_eq!(Into::<Vec<_>>::into(bitvec![1; 16]).len(), 2);
		assert!(BitVec::<LittleEndian, u32>::default().is_empty());
	}

	#[test]
	fn fmt() {
		let bv = bitvec![1; 12];
		assert_eq!(format!("{}", bv), "[11111111, 1111]");
		assert_eq!(format!("{:?}", bv), "BitVec<bitvec::cursor::BigEndian, u8> [11111111, 1111]");
	}

	#[test]
	fn hash() {
		let mut hasher = std::collections::hash_map::DefaultHasher::new();
		let _ = bitvec![1; 10].hash(&mut hasher);
	}

	#[cfg(feature = "std")]
	#[test]
	fn write() {
		let mut bv = BitVec::<LittleEndian, u32>::new();
		let res = bv.write(b"Saluton, mondo!\r\n");
		assert_eq!(res.unwrap(), 17);
	}
}
