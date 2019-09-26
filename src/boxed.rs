/*! `BitBox` structure

This module holds the type for an owned but ungrowable bit sequence. `BitVec` is
the more appropriate and useful type for most collections.
!*/

#![cfg(any(feature = "alloc", feature = "std"))]

use crate::{
	cursor::{
		BigEndian,
		Cursor,
	},
	pointer::BitPtr,
	slice::BitSlice,
	store::BitStore,
	vec::BitVec,
};

#[cfg(feature = "alloc")]
use alloc::boxed::Box;

use core::{
	marker::PhantomData,
	mem,
};

/** A pointer type for owned bit sequences.

This type is essentially a `&BitSlice` that owns its own memory. It can change
the contents of its domain, but it cannot change its own domain like `BitVec`
can. It is useful for fixed-size collections without lifetime tracking.

# Type Parameters

- `C: Cursor`: An implementor of the [`Cursor`] trait. This type is used to
  convert semantic indices into concrete bit positions in elements, and store or
  retrieve bit values from the storage type.
- `T: BitStore`: An implementor of the [`BitStore`] trait: `u8`, `u16`, `u32`,
  or `u64` (64-bit systems only). This is the actual type in memory that the box
  will use to store data.

# Safety

The `BitBox` handle has the same *size* as standard Rust `Box<[T]>` handles, but
it is ***extremely binary incompatible*** with them. Attempting to treat
`BitBox<_, T>` as `Box<[T]>` in any manner except through the provided APIs is
***catastrophically*** unsafe and unsound.

# Trait Implementations

`BitBox<C, T>` implements all the traits that `BitSlice<C, T>` does, by
deferring to the `BitSlice` implementation. It also implements conversion traits
to and from `BitSlice`, and to/from `BitVec`.
**/
#[repr(C)]
pub struct BitBox<C = BigEndian, T = u8>
where C: Cursor, T: BitStore {
	bitptr: BitPtr<T>,
	_cursor: PhantomData<C>,
}

impl<C, T> BitBox<C, T>
where C: Cursor, T: BitStore {
	/// Constructs an empty boxed bitslice.
	///
	/// # Returns
	///
	/// An empty `BitBox` at an arbitrary location.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bb: BitBox = BitBox::empty();
	/// assert!(bb.is_empty());
	/// ```
	pub fn empty() -> Self {
		Self {
			_cursor: PhantomData,
			bitptr: BitPtr::empty(),
		}
	}

	/// Produces a `BitBox` from a single element.
	///
	/// # Parameters
	///
	/// - `elt`: The source element from which to make the `BitBox`.
	///
	/// # Returns
	///
	/// A `BitBox` containing the provided element.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bb: BitBox<BigEndian, u16> = BitBox::from_element(!0);
	/// assert!(bb.all());
	/// ```
	pub fn from_element(elt: T) -> Self {
		BitSlice::<C, T>::from_element(&elt).into()
	}

	/// Builds a `BitBox` from a borrowed slice of elements.
	///
	/// # Parameters
	///
	/// - `slice`: The source slice from which to make the `BitBox`.
	///
	/// # Returns
	///
	/// A `BitBox` containing the (cloned) provided slice.
	///
	/// # Panics
	///
	/// This function may panic if the provided slice is longer than the
	/// `BitBox` can support.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [5, 10];
	/// let bb: BitBox = BitBox::from_slice(&src[..]);
	/// assert!(bb[5]);
	/// assert!(bb[7]);
	/// assert!(bb[12]);
	/// assert!(bb[14]);
	/// ```
	pub fn from_slice(slice: &[T]) -> Self {
		BitVec::from_slice(slice).into_boxed_bitslice()
	}

	/// Clones a `&BitSlice` into a `BitBox`.
	///
	/// Note: this routes through [`BitVec::from_bitslice`], which permits
	/// misaligned slices to be carried through without incident. As such, the
	/// memory behind this box may contain a misaligned slice, whose live data
	/// region does not begin at the `0` index.
	///
	/// This method does not force alignment. If you are boxing a bitslice and
	/// require that the memory is aligned, use the following sequence:
	///
	/// 1. Use `BitVec::from_bitslice` or an equivalent function
	///   (`BitSlice::to_owned`, `BitSlice::into`, `BitVec::from`) to create a
	///   bit vector.
	/// 1. Use [`BitVec::force_align`] to ensure alignment to the zero index.
	/// 1. Use `BitVec::into_boxed_bitslice` or an equivalent function.
	///
	/// # Parameters
	///
	/// - `slice`: The bit slice to clone into a bit box.
	///
	/// # Returns
	///
	/// A `BitBox` containing the same bits as the source slice.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [0u8, !0];
	/// let bb = BitBox::<BigEndian, _>::from_bitslice(src.bits());
	/// assert_eq!(bb.len(), 16);
	/// assert!(bb.some());
	/// ```
	///
	/// [`BitVec::from_bitslice`]: ../vec/struct.BitVec.html#method.from_bitslice
	/// [`BitVec::force_align`]: ../vec/struct.BitVec.html#method.force_align
	pub fn from_bitslice(slice: &BitSlice<C, T>) -> Self {
		BitVec::from_bitslice(slice).into_boxed_bitslice()
	}

	/// Produces a `BitBox` from an owned slice of elements.
	///
	/// # Parameters
	///
	/// - `slice`: The source boxed slice from which to make the `BitBox`.
	///
	/// # Returns
	///
	/// A `BitBox` governing the same slice that was passed in. This function
	/// does not reallocate.
	///
	/// # Panics
	///
	/// This function may panic if the provided slice is longer than the
	/// `BitBox` can support.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let slice: Box<[u16]> = vec![0, !0].into_boxed_slice();
	/// let bb = BitBox::<LittleEndian, _>::from_boxed_slice(slice);
	/// assert!(bb.some());
	/// assert_eq!(bb.len(), 32);
	/// ```
	pub fn from_boxed_slice(boxed: Box<[T]>) -> Self {
		let len = boxed.len();
		assert!(
			len <= BitPtr::<T>::MAX_ELTS,
			"BitBox cannot address {} elements",
			len,
		);

		let bs = BitSlice::<C, T>::from_slice(&boxed[..]);
		let bitptr = bs.bitptr();
		let out = Self {
			_cursor: PhantomData,
			bitptr,
		};
		mem::forget(boxed);
		out
	}

	/// Removes the `BitBox` wrapper from a `Box<[T]>`.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The `Box<[T]>` underneath `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let slice: Box<[u16]> = vec![0, !0].into_boxed_slice();
	/// let bb = BitBox::<LittleEndian, _>::from_boxed_slice(slice);
	/// assert_eq!(bb.len(), 32);
	/// let slice = bb.into_boxed_slice();
	/// assert_eq!(slice.len(), 2);
	/// ```
	pub fn into_boxed_slice(self) -> Box<[T]> {
		BitVec::<C, T>::from(self)
			.into_vec()
			.into_boxed_slice()
	}

	/// Constructs a `BitBox` from a raw `BitPtr`.
	///
	/// After calling this function, the raw pointer is owned by the resulting
	/// `BitBox`. The `BitBox` will deallocate the memory region it describes.
	///
	/// # Parameters
	///
	/// - `bitptr`: A `BitPtr<T>` describing a region of owned memory. This must
	///   have previously produced by `BitBox` constructors; it is unsound to
	///   even pass in `BitPtr<T>` values taken from `BitVec<C, T>` handles.
	///
	/// # Returns
	///
	/// An owned `BitBox` over the given pointer.
	///
	/// # Safety
	///
	/// Because Rust does not specify the allocation scheme used, the only
	/// valid pointer to pass into this function is one that had previously been
	/// produced by `BitBox` constructors and extracted by [`BitBox::into_raw`].
	///
	/// This function is unsafe because improper use can lead to double-free
	/// errors (constructing multiple `BitBox`es from the same `BitPtr`) or
	/// allocator inconsistencies (arbitrary pointers).
	///
	/// [`BitBox::into_raw`]: #method.into_raw
	pub unsafe fn from_raw(bitptr: BitPtr<T>) -> Self {
		Self {
			_cursor: PhantomData,
			bitptr,
		}
	}

	/// Consumes the `BitBox`, returning the wrapped `BitPtr` directly.
	///
	/// After calling this function, the caller is responsible for the memory
	/// previously managed by the `BitBox`. In particular, the caller must
	/// properly release the memory region to which the `BitPtr` refers.
	/// The proper way to do so is to convert the `BitPtr` back into a `BitBox`
	/// with the [`BitBox::from_raw`] function.
	///
	/// [`BitBox::from_raw`]: #method.from_raw
	pub unsafe fn into_raw(self) -> BitPtr<T> {
		let out = self.bitptr;
		mem::forget(self);
		out
	}

	/// Consumes and leaks the `BitBox`, returning a mutable reference,
	/// `&'a mut BitSlice<C, T>`. Note that the memory region `[T]` must outlive
	/// the chosen lifetime `'a`.
	///
	/// This function is mainly useful for bit regions that live for the
	/// remainder of the program’s life. Dropping the returned reference will
	/// cause a memory leak. If this is not acceptable, the reference should
	/// first be wrapped with the [`Box::from_raw`] function, producing a
	/// `BitBox`. This `BitBox` can then be dropped which will properly
	/// deallocate the memory.
	///
	/// # Parameters
	///
	/// - `b`: The `BitBox` to deconstruct.
	///
	/// # Returns
	///
	/// The slice formerly governed by the `BitBox`, which will never
	/// deallocate.
	///
	/// [`BitBox::from_raw`]: #method.from_raw
	pub fn leak<'a>(self) -> &'a mut BitSlice<C, T> {
		let out = self.bitptr;
		mem::forget(self);
		out.into_bitslice_mut()
	}

	/// Performs “reverse” addition (left to right instead of right to left).
	///
	/// This delegates to `BitSlice::add_assign_reverse`.
	///
	/// # Parameters
	///
	/// - `self`
	/// - `addend: impl IntoIterator<Item=bool>`: A bitstream to add to `self`.
	///
	/// # Returns
	///
	/// The sum of `self` and `addend`.
	pub fn add_reverse<I>(mut self, addend: I) -> Self
	where I: IntoIterator<Item=bool> {
		self.add_assign_reverse(addend);
		self
	}

	/// Changes the cursor on a box handle, without changing the data it
	/// governs.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// An equivalent handle to the same data, with a new cursor parameter.
	pub fn change_cursor<D>(self) -> BitBox<D, T>
	where D: Cursor {
		let bp = self.bitptr;
		mem::forget(self);
		unsafe { BitBox::from_raw(bp) }
	}

	/// Accesses the `BitSlice<C, T>` to which the `BitBox` refers.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The slice of bits behind the box.
	pub fn as_bits(&self) -> &BitSlice<C, T> {
		self.bitptr.into_bitslice()
	}

	/// Alias for `as_bits`.
	#[deprecated(since = "0.16.0", note = "Use `.as_bits` instead")]
	pub fn as_bitslice(&self) -> &BitSlice<C, T> {
		self.bitptr.into_bitslice()
	}

	/// Accesses the `BitSlice<C, T>` to which the `BitBox` refers.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The slice of bits behind the box.
	pub fn as_bits_mut(&mut self) -> &mut BitSlice<C, T> {
		self.bitptr.into_bitslice_mut()
	}

	/// Alias for `as_bits_mut`.
	#[deprecated(since = "0.16.0", note = "Use `.as_bits_mut` instead")]
	pub fn as_mut_bitslice(&mut self) -> &mut BitSlice<C, T> {
		self.bitptr.into_bitslice_mut()
	}
}

mod iter;
mod ops;
mod traits;

pub use iter::*;
