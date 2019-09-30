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
		self.reserve(other.len());

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
		use std::cmp;
		let amt = cmp::min(buf.len(), BitPtr::<T>::MAX_BITS - self.len());
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
