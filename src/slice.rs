/*! `BitSlice` Wide Reference

This module defines semantic operations on `[u1]`, in contrast to the mechanical
operations defined in `BitPtr`.

The `&BitSlice` handle has the same size and general layout as the standard Rust
slice handle `&[T]`. Its binary layout is wholly incompatible with the layout of
Rust slices, and must never be interchanged except through the provided APIs.
!*/

use crate::{
	access::BitAccess,
	cursor::{
		BigEndian,
		Cursor,
	},
	domain::*,
	indices::{
		IntoBitIdx,
	},
	pointer::BitPtr,
	store::BitStore,
};

use core::{
	fmt::Debug,
	marker::PhantomData,
	ptr,
	ops::{
		Deref,
		DerefMut,
	},
};

/** A compact slice of bits, whose cursor and storage types can be customized.

`BitSlice` is a specialized slice type, which can only ever be held by
reference or specialized owning pointers provided by this crate. The value
patterns of its handles are opaque binary structures, which cannot be
meaningfully inspected by user code.

`BitSlice` can only be dynamically allocated by this library. Creation of any
other `BitSlice` collections will result in severely incorrect behavior.

A `BitSlice` reference can be created through the [`bitvec!`] macro, from a
[`BitVec`] collection, or from most common Rust types (fundamentals, slices of
them, and small arrays) using the [`Bits`] and [`BitsMut`] traits.

`BitSlice`s are a view into a block of memory at bit-level resolution. They are
represented by a crate-internal pointer structure that ***cannot*** be used with
other Rust code except through the provided conversion APIs.

```rust
use bitvec::prelude::*;

# #[cfg(feature = "alloc")] {
let bv = bitvec![0, 1, 0, 1];
//  slicing a bitvec
let bslice: &BitSlice = &bv[..];
# }
//  coercing an array to a bitslice
let bslice: &BitSlice = [1u8, 254u8].bits::<BigEndian>();
```

Bit slices are either mutable or shared. The shared slice type is
`&BitSlice<C, T>`, while the mutable slice type is `&mut BitSlice<C, T>`. For
example, you can mutate bits in the memory to which a mutable `BitSlice` points:

```rust
use bitvec::prelude::*;

let mut base = [0u8, 0, 0, 0];
{
 let bs: &mut BitSlice = base.bits_mut::<BigEndian>();
 bs.set(13, true);
 eprintln!("{:?}", bs.as_ref());
 assert!(bs[13]);
}
assert_eq!(base[1], 4);
```

# Type Parameters

- `C: Cursor`: An implementor of the `Cursor` trait. This type is used to
  convert semantic indices into concrete bit positions in elements, and store or
  retrieve bit values from the storage type.
- `T: BitStore`: An implementor of the `BitStore` trait: `u8`, `u16`, `u32`, or
  `u64` (64-bit systems only). This is the actual type in memory that the slice
  will use to store data.

# Safety

The `&BitSlice` reference handle has the same *size* as standard Rust slice
handles, but it is ***extremely binary incompatible*** with them. Attempting to
treat `&BitSlice<_, T>` as `&[T]` in any manner except through the provided APIs
is ***catastrophically*** unsafe and unsound.

[`BitVec`]: ../vec/struct.BitVec.html
[`Bits`]: ../bits/trait.Bits.html
[`BitsMut`]: ../bits/trait.BitsMut.html
[`From`]: https://doc.rust-lang.org/stable/std/convert/trait.From.html
[`bitvec!`]: ../macro.bitvec.html
**/
#[repr(transparent)]
pub struct BitSlice<C = BigEndian, T = u8>
where C: Cursor, T: BitStore {
	/// Cursor type for selecting bits inside an element.
	_kind: PhantomData<C>,
	/// Element type of the slice.
	///
	/// eddyb recommends using `PhantomData<T>` and `[()]` instead of `[T]`
	/// alone.
	_type: PhantomData<T>,
	/// Slice of elements `T` over which the `BitSlice` has usage.
	_elts: [()],
}

impl<C, T> BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Produces the empty slice. This is equivalent to `&[]` for Rust slices.
	///
	/// # Returns
	///
	/// An empty `&BitSlice` handle.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits: &BitSlice = BitSlice::empty();
	/// ```
	pub fn empty<'a>() -> &'a Self {
		BitPtr::empty().into_bitslice()
	}

	/// Produces the empty mutable slice. This is equivalent to `&mut []` for
	/// Rust slices.
	///
	/// # Returns
	///
	/// An empty `&mut BitSlice` handle.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits: &mut BitSlice = BitSlice::empty_mut();
	/// ```
	pub fn empty_mut<'a>() -> &'a mut Self {
		BitPtr::empty().into_bitslice_mut()
	}

	/// Produces an immutable `BitSlice` over a single element.
	///
	/// # Parameters
	///
	/// - `elt`: A reference to an element over which the `BitSlice` will be
	///   created.
	///
	/// # Returns
	///
	/// A `BitSlice` over the provided element.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let elt: u8 = !0;
	/// let bs: &BitSlice = BitSlice::from_element(&elt);
	/// assert!(bs.all());
	/// ```
	pub fn from_element(elt: &T) -> &Self {
		unsafe {
			BitPtr::new_unchecked(elt, 0.idx(), T::BITS as usize)
		}.into_bitslice()
	}

	/// Produces a mutable `BitSlice` over a single element.
	///
	/// # Parameters
	///
	/// - `elt`: A reference to an element over which the `BitSlice` will be
	///   created.
	///
	/// # Returns
	///
	/// A `BitSlice` over the provided element.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut elt: u8 = !0;
	/// let bs: &mut BitSlice = BitSlice::from_element_mut(&mut elt);
	/// bs.set(0, false);
	/// assert!(!bs.all());
	/// ```
	pub fn from_element_mut(elt: &mut T) -> &mut Self {
		unsafe {
			BitPtr::new_unchecked(elt, 0.idx(), T::BITS as usize)
		}.into_bitslice_mut()
	}

	/// Wraps a `&[T: BitStore]` in a `&BitSlice<C: Cursor, T>`. The cursor must
	/// be specified at the call site. The element type cannot be changed.
	///
	/// # Parameters
	///
	/// - `src`: The elements over which the new `BitSlice` will operate.
	///
	/// # Returns
	///
	/// A `BitSlice` representing the original element slice.
	///
	/// # Panics
	///
	/// The source slice must not exceed the maximum number of elements that a
	/// `BitSlice` can contain. This value is documented in [`BitPtr`].
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [1, 2, 3];
	/// let bits = BitSlice::<BigEndian, u8>::from_slice(&src[..]);
	/// assert_eq!(bits.len(), 24);
	/// assert_eq!(bits.as_ref().len(), 3);
	/// assert!(bits[7]);  // src[0] == 0b0000_0001
	/// assert!(bits[14]); // src[1] == 0b0000_0010
	/// assert!(bits[22]); // src[2] == 0b0000_0011
	/// assert!(bits[23]);
	/// ```
	///
	/// [`BitPtr`]: ../pointer/struct.BitPtr.html
	pub fn from_slice(slice: &[T]) -> &Self {
		let len = slice.len();
		assert!(
			len <= BitPtr::<T>::MAX_ELTS,
			"BitSlice cannot address {} elements",
			len,
		);
		let bits = len.checked_mul(T::BITS as usize)
			.expect("Bit length out of range");
		BitPtr::new(slice.as_ptr(), 0.idx(), bits).into_bitslice()
	}

	/// Wraps a `&mut [T: BitStore]` in a `&mut BitSlice<C: Cursor, T>`. The
	/// cursor must be specified by the call site. The element type cannot
	/// be changed.
	///
	/// # Parameters
	///
	/// - `src`: The elements over which the new `BitSlice` will operate.
	///
	/// # Returns
	///
	/// A `BitSlice` representing the original element slice.
	///
	/// # Panics
	///
	/// The source slice must not exceed the maximum number of elements that a
	/// `BitSlice` can contain. This value is documented in [`BitPtr`].
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [1, 2, 3];
	/// let bits = BitSlice::<LittleEndian, u8>::from_slice_mut(&mut src[..]);
	/// //  The first bit is the LSb of the first element.
	/// assert!(bits[0]);
	/// bits.set(0, false);
	/// assert!(!bits[0]);
	/// assert_eq!(bits.as_ref(), &[0, 2, 3]);
	/// ```
	///
	/// [`BitPtr`]: ../pointer/struct.BitPtr.html
	pub fn from_slice_mut(slice: &mut [T]) -> &mut Self {
		Self::from_slice(slice).bitptr().into_bitslice_mut()
	}

	/// Returns the number of bits contained in the `BitSlice`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The number of live bits in the slice domain.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let store = 0u8;
	/// let bs = store.bits::<BigEndian>();
	/// assert_eq!(bs.len(), 8);
	/// ```
	pub fn len(&self) -> usize {
		self.bitptr().len()
	}

	/// Tests if the slice is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Whether the slice has no live bits.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bs = BitSlice::<BigEndian, u8>::empty();
	/// assert!(bs.is_empty());
	/// let bs = 0u8.bits::<BigEndian>();
	/// assert!(!bs.is_empty());
	/// ```
	pub fn is_empty(&self) -> bool {
		self.len() == 0
	}

	/// Gets the first element of the slice, if present.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// `None` if the slice is empty, or `Some(bit)` if it is not.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// assert!(BitSlice::<BigEndian, u8>::empty().first().is_none());
	/// assert!(128u8.bits::<BigEndian>().first().unwrap());
	/// ```
	pub fn first(&self) -> Option<bool> {
		self.get(0)
	}

	/// Returns the first and all the rest of the bits of the slice, or `None`
	/// if it is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// If the slice is empty, this returns `None`, otherwise, it returns `Some`
	/// of:
	///
	/// - the first bit
	/// - a `&BitSlice` of all the rest of the bits (this may be empty)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// assert!(BitSlice::<BigEndian, u8>::empty().split_first().is_none());
	///
	/// let store = 128u8;
	/// let bits = store.bits::<BigEndian>();
	/// let (h, t) = bits.split_first().unwrap();
	/// assert!(h);
	/// assert!(t.not_any());
	///
	/// let (h, t) = bits[0 .. 1].split_first().unwrap();
	/// assert!(h);
	/// assert!(t.is_empty());
	/// ```
	pub fn split_first(&self) -> Option<(bool, &Self)> {
		if self.is_empty() {
			None
		}
		else {
			Some((self[0], &self[1 ..]))
		}
	}

	/// Returns the first and all the rest of the bits of the slice, or `None`
	/// if it is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// If the slice is empty, this returns `None`, otherwise, it returns `Some`
	/// of:
	///
	/// - the first bit
	/// - a `&mut BitSlice` of all the rest of the bits (this may be empty)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut store = 0u8;
	/// let bits = store.bits_mut::<LittleEndian>();
	/// assert!(!bits[0]);
	/// *bits.at(0) = true;
	/// let (h, t) = bits.split_first_mut().unwrap();
	/// assert!(h);
	/// assert_eq!(t.len(), 7);
	/// ```
	pub fn split_first_mut(&mut self) -> Option<(bool, &mut Self)> {
		if self.is_empty() {
			None
		}
		else {
			Some((self[0], &mut self[1 ..]))
		}
	}

	/// Returns the last and all the rest of the bits in the slice, or `None`
	/// if it is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// If the slice is empty, this returns `None`, otherwise, it returns `Some`
	/// of:
	///
	/// - the last bit
	/// - a `&BitSlice` of all the rest of the bits (this may be empty)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// assert!(BitSlice::<BigEndian, u8>::empty().split_last().is_none());
	///
	/// let bits = 1u8.bits::<BigEndian>();
	/// let (t, h) = bits.split_last().unwrap();
	/// assert!(t);
	/// assert!(h.not_any());
	///
	/// let bits = &bits[7 .. 8];
	/// let (t, h) = bits.split_last().unwrap();
	/// assert!(t);
	/// assert!(h.is_empty());
	/// ```
	pub fn split_last(&self) -> Option<(bool, &Self)> {
		if self.is_empty() {
			None
		}
		else {
			let len = self.len();
			Some((self[len - 1], &self[.. len - 1]))
		}
	}

	/// Returns the last and all the rest of the bits in the slice, or `None`
	/// if it is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// If the slice is empty, this returns `None`, otherwise, it returns `Some`
	/// of:
	///
	/// - the last bit
	/// - a `&BitSlice` of all the rest of the bits (this may be empty)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut store = 0u8;
	/// let bits = store.bits_mut::<LittleEndian>();
	/// assert!(!bits[7]);
	/// *bits.at(7) = true;
	/// let (h, t) = bits.split_last_mut().unwrap();
	/// assert!(h);
	/// assert_eq!(t.len(), 7);
	/// ```
	pub fn split_last_mut(&mut self) -> Option<(bool, &mut Self)> {
		if self.is_empty() {
			None
		}
		else {
			let len = self.len();
			Some((self[len - 1], &mut self[.. len - 1]))
		}
	}

	/// Gets the last element of the slice, or `None` if it is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// `None` if the slice is empty, or `Some(bit)` if it is not.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// assert!(BitSlice::<BigEndian, u8>::empty().last().is_none());
	/// assert!(1u8.bits::<BigEndian>().last().unwrap());
	/// ```
	pub fn last(&self) -> Option<bool> {
		if self.is_empty() {
			None
		}
		else {
			Some(self[self.len() - 1])
		}
	}

	/// Gets the bit value at the given position.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `index`: The bit index to retrieve.
	///
	/// # Returns
	///
	/// The bit at the specified index, if any. If `index` is beyond the bounds
	/// of `self`, then `None` is produced.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 8u8.bits::<BigEndian>();
	/// assert!(bits.get(4).unwrap());
	/// assert!(!bits.get(3).unwrap());
	/// assert!(bits.get(10).is_none());
	/// ```
	pub fn get(&self, index: usize) -> Option<bool> {
		if index >= self.len() {
			None
		}
		else {
			Some(unsafe { self.get_unchecked(index) })
		}
	}

	/// Looks up a bit at an index, without doing bounds checking.
	///
	/// This is generally not recommended; use with caution! For a safe
	/// alternative, see [`get`].
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `index`: The bit index to retrieve. This index is *not* checked
	///   against the length of `self`.
	///
	/// # Returns
	///
	/// The bit at the requested index.
	///
	/// # Safety
	///
	/// This method is **not** safe. It performs raw pointer arithmetic to seek
	/// from the start of the slice to the requested index, and look up the bit
	/// there. It does not inspect the length of `self`, and it is free to
	/// perform out-of-bounds memory access.
	///
	/// Use this method **only** when you have already performed the bounds
	/// check, and can guarantee that the call occurs with a safely in-bounds
	/// index.
	///
	/// # Examples
	///
	/// This example uses a bit slice of length 2, and demonstrates
	/// out-of-bounds access to the last bit in the element.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 1u8;
	/// let bits = &src.bits::<BigEndian>()[2 .. 4];
	/// assert_eq!(bits.len(), 2);
	/// assert!(unsafe { bits.get_unchecked(5) });
	/// ```
	///
	/// [`get`]: #method.get
	pub unsafe fn get_unchecked(&self, index: usize) -> bool {
		let bitptr = self.bitptr();
		let (elt, bit) = bitptr.head().offset(index as isize);
		let data_ptr = bitptr.pointer().a();
		(&*data_ptr.offset(elt)).get::<C>(bit)
	}

	/// Sets the bit value at the given position.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `index`: The bit index to set. It must be in the domain
	///   `0 .. self.len()`.
	/// - `value`: The value to be set, `true` for `1` and `false` for `0`.
	///
	/// # Panics
	///
	/// This method panics if `index` is outside the slice domain.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut store = 8u8;
	/// let bits = store.bits_mut::<BigEndian>();
	/// assert!(!bits[3]);
	/// bits.set(3, true);
	/// assert!(bits[3]);
	/// ```
	pub fn set(&mut self, index: usize, value: bool) {
		let len = self.len();
		assert!(index < len, "Index out of range: {} >= {}", index, len);
		unsafe { self.set_unchecked(index, value) };
	}

	/// Sets a bit at an index, without doing bounds checking.
	///
	/// This is generally not recommended; use with caution! For a safe
	/// alternative, see [`set`].
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `index`: The bit index to retrieve. This index is *not* checked
	///   against the length of `self`.
	///
	/// # Effects
	///
	/// The bit at `index` is set to `value`.
	///
	/// # Safety
	///
	/// This method is **not** safe. It performs raw pointer arithmetic to seek
	/// from the start of the slice to the requested index, and set the bit
	/// there. It does not inspect the length of `self`, and it is free to
	/// perform out-of-bounds memory *write* access.
	///
	/// Use this method **only** when you have already performed the bounds
	/// check, and can guarantee that the call occurs with a safely in-bounds
	/// index.
	///
	/// # Examples
	///
	/// This example uses a bit slice of length 2, and demonstrates
	/// out-of-bounds access to the last bit in the element.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// {
	///  let bits = &mut src.bits_mut::<BigEndian>()[2 .. 4];
	///  assert_eq!(bits.len(), 2);
	///  unsafe { bits.set_unchecked(5, true); }
	/// }
	/// assert_eq!(src, 1);
	/// ```
	///
	/// [`set`]: #method.set
	pub unsafe fn set_unchecked(&mut self, index: usize, value: bool) {
		let bitptr = self.bitptr();
		let (elt, bit) = bitptr.head().offset(index as isize);
		let data_ptr = bitptr.pointer().a();
		(&*data_ptr.offset(elt)).set::<C>(bit, value);
	}

	/// Produces a write reference to a single bit in the slice.
	///
	/// The structure returned by this method extends the borrow until it drops,
	/// which precludes parallel use.
	///
	/// The [`split_at_mut`] method allows splitting the borrows of a slice, and
	/// will enable safe parallel use of these write references. The `atomic`
	/// feature guarantees that parallel use does not cause data races when
	/// modifying the underlying slice.
	///
	/// # Lifetimes
	///
	/// - `'a` Propagates the lifetime of the referent slice to the single-bit
	///   reference produced.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `index`: The index of the bit in `self` selected.
	///
	/// # Returns
	///
	/// A write reference to the requested bit. Due to Rust limitations, this is
	/// not a native reference type, but is a custom structure that holds the
	/// address of the requested bit and its value. The produced structure
	/// implements `Deref` and `DerefMut` to its cached bit, and commits the
	/// cached bit to the parent slice on drop.
	///
	/// # Usage
	///
	/// You must use the dereference operator on the `.at()` expression in order
	/// to assign to it. In general, you should prefer immediately using and
	/// discarding the returned value, rather than binding it to a name and
	/// letting it live for more than one statement.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// let bits = src.bits_mut::<BigEndian>();
	///
	/// assert!(!bits[0]);
	/// *bits.at(0) = true;
	/// //  note the leading dereference.
	/// assert!(bits[0]);
	/// ```
	///
	/// This example shows multiple usage by using `split_at_mut`.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// let bits = src.bits_mut::<BigEndian>();
	///
	/// {
	///  let (mut a, rest) = bits.split_at_mut(2);
	///  let (mut b, rest) = rest.split_at_mut(3);
	///  *a.at(0) = true;
	///  *b.at(0) = true;
	///  *rest.at(0) = true;
	/// }
	///
	/// assert_eq!(bits.as_slice()[0], 0b1010_0100);
	/// //                               a b   rest
	/// ```
	///
	/// The above example splits the slice into three (the first, the second,
	/// and the rest) in order to hold multiple write references into the slice.
	///
	/// [`split_at_mut`]: #method.split_at_mut
	pub fn at(&mut self, index: usize) -> BitGuard<C, T> {
		BitGuard {
			_m: PhantomData,
			bit: self[index],
			slot: &mut self[index ..= index],
		}
	}

	/// Retrieves a read pointer to the start of the underlying data slice.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A pointer to the first element, partial or not, in the underlying store.
	///
	/// If `self` is empty, then the null pointer is returned.
	///
	/// # Safety
	///
	/// The caller must ensure that the slice outlives the pointer this function
	/// returns, or else it will dangle and point to garbage.
	///
	/// Modifying the container referenced by this slice may cause its buffer to
	/// reallocate, which would also make any pointers to it invalid.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [0u8; 4];
	/// let bits = src.bits::<BigEndian>();
	/// assert_eq!(src.as_ptr(), bits.as_ptr());
	/// ```
	pub fn as_ptr(&self) -> *const T {
		if self.is_empty() {
			ptr::null()
		}
		else {
			self.bitptr().pointer().r()
		}
	}

	/// Retrieves a write pointer to the start of the underlying data slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A pointer to the first element, partial or not, in the underlying store.
	///
	/// If `self` is empty, then the null pointer is returned.
	///
	/// # Safety
	///
	/// The caller must ensure that the slice outlives the pointer this function
	/// returns, or else it will dangle and point to garbage.
	///
	/// Modifying the container referenced by this slice may cause its buffer to
	/// reallocate, which would also make any pointers to it invalid.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [0u8; 4];
	/// let src_ptr = src.as_mut_ptr();
	/// let bits = src.bits_mut::<BigEndian>();
	/// assert_eq!(src_ptr, bits.as_mut_ptr());
	/// ```
	pub fn as_mut_ptr(&mut self) -> *mut T {
		if self.is_empty() {
			ptr::null_mut()
		}
		else {
			self.bitptr().pointer().w()
		}
	}

	/// Swaps two bits in the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `a`: The first index to be swapped.
	/// - `b`: The second index to be swapped.
	///
	/// # Panics
	///
	/// Panics if either `a` or `b` are out of bounds.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut store = 32u8;
	/// let bits = store.bits_mut::<BigEndian>();
	/// assert!(!bits[0]);
	/// assert!(bits[2]);
	/// bits.swap(0, 2);
	/// assert!(bits[0]);
	/// assert!(!bits[2]);
	/// ```
	pub fn swap(&mut self, a: usize, b: usize) {
		assert!(a < self.len(), "Index {} out of bounds: {}", a, self.len());
		assert!(b < self.len(), "Index {} out of bounds: {}", b, self.len());
		let bit_a = self[a];
		let bit_b = self[b];
		self.set(a, bit_b);
		self.set(b, bit_a);
	}

	/// Reverses the order of bits in the slice, in place.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b1010_1010u8;
	/// {
	///   let bits = src.bits_mut::<BigEndian>();
	///   bits[1 .. 7].reverse();
	/// }
	/// eprintln!("{:b}", src);
	/// assert_eq!(src, 0b1101_0100);
	/// ```
	pub fn reverse(&mut self) {
		//  this is better implemented as a recursive algorithm, but Rust
		//  doesn’t yet flatten recursive tail calls into a loop, so, do it
		//  manually.
		let mut cur: &mut Self = self;
		loop {
			let len = cur.len();
			if len < 2 {
				return;
			}
			//  swap() has two assertions on each call, that reverse() knows it
			//  can bypass
			let (h, t) = (cur[0], cur[len - 1]);
			cur.set(0, t);
			cur.set(len - 1, h);
			cur = &mut cur[1 .. len - 1];
		}
	}

	/// Provides read-only iteration across the slice domain.
	///
	/// The iterator returned from this method implements `ExactSizeIterator`
	/// and `DoubleEndedIterator` just as the consuming `.into_iter()` method’s
	/// iterator does.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// An iterator over all bits in the slice domain, in `C` and `T` ordering.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 64u8;
	/// let bits = src.bits::<BigEndian>();
	/// let mut iter = bits[.. 2].iter();
	/// assert!(!iter.next().unwrap());
	/// assert!(iter.next().unwrap());
	/// assert!(iter.next().is_none());
	/// ```
	pub fn iter(&self) -> Iter<C, T> {
		self.into_iter()
	}

	/// Produces a sliding iterator over consecutive windows in the slice. Each
	/// windows has the width `size`. The windows overlap. If the slice is
	/// shorter than `size`, the produced iterator is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each window.
	///
	/// # Returns
	///
	/// An iterator which yields sliding views into the slice.
	///
	/// # Panics
	///
	/// This function panics if the `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0b0100_1011u8;
	/// let bits = src.bits::<BigEndian>();
	/// let mut windows = bits.windows(4);
	/// assert_eq!(windows.next(), Some(&bits[0 .. 4]));
	/// assert_eq!(windows.next(), Some(&bits[1 .. 5]));
	/// assert_eq!(windows.next(), Some(&bits[2 .. 6]));
	/// assert_eq!(windows.next(), Some(&bits[3 .. 7]));
	/// assert_eq!(windows.next(), Some(&bits[4 .. 8]));
	/// assert!(windows.next().is_none());
	/// ```
	pub fn windows(&self, size: usize) -> Windows<C, T> {
		assert_ne!(size, 0, "Window width cannot be zero");
		Windows {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice. Each
	/// chunk, except possibly the last, has the width `size`. The chunks do not
	/// overlap. If the slice is shorter than `size`, the produced iterator
	/// produces only one chunk.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive chunks of the slice.
	///
	/// # Panics
	///
	/// This function panics if the `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0b0100_1011u8;
	/// let bits = src.bits::<BigEndian>();
	/// let mut chunks = bits.chunks(3);
	/// assert_eq!(chunks.next(), Some(&bits[0 .. 3]));
	/// assert_eq!(chunks.next(), Some(&bits[3 .. 6]));
	/// assert_eq!(chunks.next(), Some(&bits[6 .. 8]));
	/// assert!(chunks.next().is_none());
	/// ```
	pub fn chunks(&self, size: usize) -> Chunks<C, T> {
		assert_ne!(size, 0, "Chunk width cannot be zero");
		Chunks {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice. Each
	/// chunk, except possibly the last, has the width `size`. The chunks do not
	/// overlap. If the slice is shorter than `size`, the produced iterator
	/// produces only one chunk.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive mutable chunks of the slice.
	///
	/// # Panics
	///
	/// This function panics if the `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0100_1011u8;
	/// {
	///  let bits = src.bits_mut::<BigEndian>();
	///  let mut chunks = bits.chunks_mut(3);
	///  chunks.next().unwrap().set(2, true);
	///  chunks.next().unwrap().set(2, true);
	///  chunks.next().unwrap().set(1, false);
	/// }
	/// assert_eq!(src, 0b0110_1110);
	/// ```
	pub fn chunks_mut(&mut self, size: usize) -> ChunksMut<C, T> {
		assert_ne!(size, 0, "Chunk width cannot be zero");
		ChunksMut {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice. Each
	/// chunk has the width `size`. If `size` does not evenly divide the slice,
	/// then the remainder is not part of the iteration, and can be accessed
	/// separately with the `.remainder()` method.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive chunks of the slice.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0b0100_1011u8;
	/// let bits = src.bits::<BigEndian>();
	/// let mut chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.next(), Some(&bits[0 .. 3]));
	/// assert_eq!(chunks_exact.next(), Some(&bits[3 .. 6]));
	/// assert!(chunks_exact.next().is_none());
	/// assert_eq!(chunks_exact.remainder(), &bits[6 .. 8]);
	/// ```
	pub fn chunks_exact(&self, size: usize) -> ChunksExact<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		let rem = self.len() % size;
		let len = self.len() - rem;
		let (inner, extra) = self.split_at(len);
		ChunksExact {
			inner,
			extra,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice. Each
	/// chunk has the width `size`. If `size` does not evenly divide the slice,
	/// then the remainder is not part of the iteration, and can be accessed
	/// separately with the `.remainder()` method.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive mutable chunks of the slice.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0100_1011u8;
	/// {
	///  let bits = src.bits_mut::<BigEndian>();
	///  let mut chunks_exact = bits.chunks_exact_mut(3);
	///  chunks_exact.next().unwrap().set(2, true);
	///  chunks_exact.next().unwrap().set(2, true);
	///  assert!(chunks_exact.next().is_none());
	/// }
	/// assert_eq!(src, 0b0110_1111);
	/// ```
	pub fn chunks_exact_mut(&mut self, size: usize) -> ChunksExactMut<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		let rem = self.len() % size;
		let len = self.len() - rem;
		let (inner, extra) = self.split_at_mut(len);
		ChunksExactMut {
			inner,
			extra,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice, from
	/// the back to the front. Each chunk, except possibly the front, has the
	/// width `size`. The chunks do not overlap. If the slice is shorter than
	/// `size`, then the iterator produces one item.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive chunks of the slice, from the back
	/// to the front.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0b0100_1011u8;
	/// let bits = src.bits::<BigEndian>();
	/// let mut rchunks = bits.rchunks(3);
	/// assert_eq!(rchunks.next(), Some(&bits[5 .. 8]));
	/// assert_eq!(rchunks.next(), Some(&bits[2 .. 5]));
	/// assert_eq!(rchunks.next(), Some(&bits[0 .. 2]));
	/// assert!(rchunks.next().is_none());
	/// ```
	pub fn rchunks(&self, size: usize) -> RChunks<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		RChunks {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice, from
	/// the back to the front. Each chunk, except possibly the front, has the
	/// width `size`. The chunks do not overlap. If the slice is shorter than
	/// `size`, then the iterator produces one item.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive mutable chunks of the slice, from
	/// the back to the front.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0100_1011u8;
	/// {
	///  let bits = src.bits_mut::<BigEndian>();
	///  let mut rchunks = bits.rchunks_mut(3);
	///  rchunks.next().unwrap().set(0, true);
	///  rchunks.next().unwrap().set(2, false);
	///  rchunks.next().unwrap().set(1, false);
	///  assert!(rchunks.next().is_none());
	/// }
	/// assert_eq!(src, 0b0000_0111);
	/// ```
	pub fn rchunks_mut(&mut self, size: usize) -> RChunksMut<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		RChunksMut {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice, from
	/// the back to the front. Each chunk has the width `size`. If `size` does
	/// not evenly divide the slice, then the remainder is not part of the
	/// iteration, and can be accessed separately with the `.remainder()`
	/// method.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive chunks of the slice, from the back
	/// to the front.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let store: &[u8] = &[0b0100_1011];
	/// let bits: &BitSlice = store.into();
	/// let mut rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.next(), Some(&bits[5 .. 8]));
	/// assert_eq!(rchunks_exact.next(), Some(&bits[2 .. 5]));
	/// assert!(rchunks_exact.next().is_none());
	/// assert_eq!(rchunks_exact.remainder(), &bits[0 .. 2]);
	/// ```
	pub fn rchunks_exact(&self, size: usize) -> RChunksExact<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		let (extra, inner) = self.split_at(self.len() % size);
		RChunksExact {
			inner,
			extra,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice, from
	/// the back to the front. Each chunk has the width `size`. If `size` does
	/// not evenly divide the slice, then the remainder is not part of the
	/// iteration, and can be accessed separately with the `.remainder()`
	/// method.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive mutable chunks of the slice, from
	/// the back to the front.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0100_1011u8;
	/// {
	///  let bits = src.bits_mut::<BigEndian>();
	///  let mut rchunks_exact = bits.rchunks_exact_mut(3);
	///  rchunks_exact.next().unwrap().set(0, true);
	///  rchunks_exact.next().unwrap().set(2, false);
	///  assert!(rchunks_exact.next().is_none());
	/// }
	/// assert_eq!(src, 0b0100_0111);
	/// ```
	pub fn rchunks_exact_mut(&mut self, size: usize) -> RChunksExactMut<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		let (extra, inner) = self.split_at_mut(self.len() % size);
		RChunksExactMut {
			inner,
			extra,
			width: size,
		}
	}

	/// Divides one slice into two at an index.
	///
	/// The first will contain all indices from `[0, mid)` (excluding the index
	/// `mid` itself) and the second will contain all indices from `[mid, len)`
	/// (excluding the index `len` itself).
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `mid`: The index at which to split
	///
	/// # Returns
	///
	/// - The bits up to but not including `mid`.
	/// - The bits from mid onwards.
	///
	/// # Panics
	///
	/// Panics if `mid > self.len()`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 15u8.bits::<BigEndian>();
	///
	/// let (l, r) = bits.split_at(0);
	/// assert!(l.is_empty());
	/// assert_eq!(r, bits);
	///
	/// let (l, r) = bits.split_at(4);
	/// assert_eq!(l, &bits[0 .. 4]);
	/// assert_eq!(r, &bits[4 .. 8]);
	///
	/// let (l, r) = bits.split_at(8);
	/// assert_eq!(l, bits);
	/// assert!(r.is_empty());
	/// ```
	pub fn split_at(&self, mid: usize) -> (&Self, &Self) {
		let len = self.len();
		assert!(mid <= len, "Index {} out of bounds: {}", mid, len);
		if mid == len {
			(&self, Self::empty())
		}
		else {
			(&self[.. mid], &self[mid ..])
		}
	}

	/// Divides one slice into two at an index.
	///
	/// The first will contain all indices from `[0, mid)` (excluding the index
	/// `mid` itself) and the second will contain all indices from `[mid, len)`
	/// (excluding the index `len` itself).
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `mid`: The index at which to split
	///
	/// # Returns
	///
	/// - The bits up to but not including `mid`.
	/// - The bits from mid onwards.
	///
	/// # Panics
	///
	/// Panics if `mid > self.len()`.
	pub fn split_at_mut(&mut self, mid: usize) -> (&mut Self, &mut Self) {
		let (head, tail) = self.split_at(mid);
		(head.bitptr().into_bitslice_mut(), tail.bitptr().into_bitslice_mut())
	}

	/// Tests if the slice begins with the given prefix.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `prefix`: Any `BitSlice` against which `self` is tested. This is not
	///   required to have the same cursor or storage types as `self`.
	///
	/// # Returns
	///
	/// Whether `self` begins with `prefix`. This is true only if `self` is at
	/// least as long as `prefix` and their bits are semantically equal.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0xA6u8.bits::<BigEndian>();
	/// assert!(bits.starts_with(&bits[.. 3]));
	/// assert!(!bits.starts_with(&bits[3 ..]));
	/// ```
	pub fn starts_with<D, U>(&self, prefix: &BitSlice<D, U>) -> bool
	where D: Cursor, U: BitStore {
		let plen = prefix.len();
		self.len() >= plen && prefix == self[.. plen]
	}

	/// Tests if the slice ends with the given suffix.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `suffix`: Any `BitSlice` against which `self` is tested. This is not
	///   required to have the same cursor or storage types as `self`.
	///
	/// # Returns
	///
	/// Whether `self` ends with `suffix`. This is true only if `self` is at
	/// least as long as `suffix` and their bits are semantically equal.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0xA6u8.bits::<BigEndian>();
	/// assert!(bits.ends_with(&bits[5 ..]));
	/// assert!(!bits.ends_with(&bits[.. 5]));
	/// ```
	pub fn ends_with<D, U>(&self, suffix: &BitSlice<D, U>) -> bool
	where D: Cursor, U: BitStore {
		let slen = suffix.len();
		let len = self.len();
		len >= slen && suffix == self[len - slen ..]
	}

	/// Rotates the slice, in place, to the left.
	///
	/// After calling this method, the bits from `[.. by]` will be at the back
	/// of the slice, and the bits from `[by ..]` will be at the front. This
	/// operates fully in-place.
	///
	/// In-place rotation of bits requires this method to take `O(k × n)` time.
	/// It is impossible to use machine intrinsics to perform galloping rotation
	/// on bits.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `by`: The number of bits by which to rotate left. This must be in the
	///   range `0 ..= self.len()`. If it is `0` or `self.len()`, then this
	///   method is a no-op.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0xF0u8;
	/// let bits = src.bits_mut::<BigEndian>();
	/// bits.rotate_left(2);
	/// assert_eq!(bits.as_ref()[0], 0xC3);
	/// ```
	pub fn rotate_left(&mut self, by: usize) {
		let len = self.len();
		assert!(by <= len, "Slices cannot be rotated by more than their length");
		if by == 0 || by == len {
			return;
		}

		for _ in 0 .. by {
			let tmp = self[0];
			for n in 1 .. len {
				let bit = self[n];
				self.set(n - 1, bit);
			}
			self.set(len - 1, tmp);
		}
	}

	/// Rotates the slice, in place, to the right.
	///
	/// After calling this method, the bits from `[self.len() - by ..]` will be
	/// at the front of the slice, and the bits from `[.. self.len() - by]` will
	/// be at the back. This operates fully in-place.
	///
	/// In-place rotation of bits requires this method to take `O(k × n)` time.
	/// It is impossible to use machine intrinsics to perform galloping rotation
	/// on bits.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `by`: The number of bits by which to rotate right. This must be in the
	///   range `0 ..= self.len()`. If it is `0` or `self.len`, then this method
	///   is a no-op.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0xF0u8;
	/// let bits = src.bits_mut::<BigEndian>();
	/// bits.rotate_right(2);
	/// assert_eq!(bits.as_ref()[0], 0x3C);
	/// ```
	pub fn rotate_right(&mut self, by: usize) {
		let len = self.len();
		assert!(by <= len, "Slices cannot be rotated by more than their length");
		if by == len {
			return;
		}

		//  Perform `by` repetitions,
		for _ in 0 .. by {
			let tmp = self[len - 1];
			//  of `len` steps
			for n in (0 .. len - 1).rev() {
				let bit = self[n];
				self.set(n + 1, bit);
			}
			self.set(0, tmp);
		}
	}

	/// Tests if *all* bits in the slice domain are set (logical `∧`).
	///
	/// # Truth Table
	///
	/// ```text
	/// 0 0 => 0
	/// 0 1 => 0
	/// 1 0 => 0
	/// 1 1 => 1
	/// ```
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Whether all bits in the slice domain are set. The empty slice returns
	/// `true`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0xFDu8.bits::<BigEndian>();
	/// assert!(bits[.. 4].all());
	/// assert!(!bits[4 ..].all());
	/// ```
	pub fn all(&self) -> bool {
		match self.bitptr().domain() {
			BitDomain::Empty => {},
			BitDomain::Minor(head, elt, tail) => {
				for n in *head .. *tail {
					if !elt.get::<C>(n.idx()) {
						return false;
					}
				}
			},
			BitDomain::Major(h, head, body, tail, t) => {
				for n in *h .. T::BITS {
					if !head.get::<C>(n.idx()) {
						return false;
					}
				}
				for n in 0 .. *t {
					if !tail.get::<C>(n.idx()) {
						return false;
					}
				}
				return body.iter().all(|e| *e == T::bits(true));
			},
			BitDomain::PartialHead(h, head, body) => {
				for n in *h .. T::BITS {
					if !head.get::<C>(n.idx()) {
						return false;
					}
				}
				return body.iter().all(|e| *e == T::bits(true));
			},
			BitDomain::PartialTail(body, tail, t) => {
				for n in 0 .. *t {
					if !tail.get::<C>(n.idx()) {
						return false;
					}
				}
				return body.iter().all(|e| *e == T::bits(true));
			},
			BitDomain::Spanning(body) => {
				return body.iter().all(|e| *e == T::bits(true));
			},
		}
		true
	}

	/// Tests if *any* bit in the slice is set (logical `∨`).
	///
	/// # Truth Table
	///
	/// ```text
	/// 0 0 => 0
	/// 0 1 => 1
	/// 1 0 => 1
	/// 1 1 => 1
	/// ```
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Whether any bit in the slice domain is set. The empty slice returns
	/// `false`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x40u8.bits::<BigEndian>();
	/// assert!(bits[.. 4].any());
	/// assert!(!bits[4 ..].any());
	/// ```
	pub fn any(&self) -> bool {
		match self.bitptr().domain() {
			BitDomain::Empty => {},
			BitDomain::Minor(head, elt, tail) => {
				for n in *head .. *tail {
					if elt.get::<C>(n.idx()) {
						return true;
					}
				}
			},
			BitDomain::Major(h, head, body, tail, t) => {
				for n in *h .. T::BITS {
					if head.get::<C>(n.idx()) {
						return true;
					}
				}
				for n in 0 .. *t {
					if tail.get::<C>(n.idx()) {
						return true;
					}
				}
				return body.iter().any(|e| *e != T::bits(false));
			},
			BitDomain::PartialHead(h, head, body) => {
				for n in *h .. T::BITS {
					if head.get::<C>(n.idx()) {
						return true;
					}
				}
				return body.iter().any(|e| *e != T::bits(false));
			},
			BitDomain::PartialTail(body, tail, t) => {
				for n in 0 .. *t {
					if tail.get::<C>(n.idx()) {
						return true;
					}
				}
				return body.iter().any(|e| *e != T::bits(false));
			},
			BitDomain::Spanning(body) => {
				return body.iter().any(|e| *e != T::bits(false));
			},
		}
		false
	}

	/// Tests if *any* bit in the slice is clear (logical `¬∧`).
	///
	/// # Truth Table
	///
	/// ```text
	/// 0 0 => 1
	/// 0 1 => 1
	/// 1 0 => 1
	/// 1 1 => 0
	/// ```
	///
	/// # Parameters
	///
	/// - `&self
	///
	/// # Returns
	///
	/// Whether any bit in the slice domain is clear.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0xFDu8.bits::<BigEndian>();
	/// assert!(!bits[.. 4].not_all());
	/// assert!(bits[4 ..].not_all());
	/// ```
	pub fn not_all(&self) -> bool {
		!self.all()
	}

	/// Tests if *all* bits in the slice are clear (logical `¬∨`).
	///
	/// # Truth Table
	///
	/// ```text
	/// 0 0 => 1
	/// 0 1 => 0
	/// 1 0 => 0
	/// 1 1 => 0
	/// ```
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Whether all bits in the slice domain are clear.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x40u8.bits::<BigEndian>();
	/// assert!(!bits[.. 4].not_any());
	/// assert!(bits[4 ..].not_any());
	/// ```
	pub fn not_any(&self) -> bool {
		!self.any()
	}

	/// Tests whether the slice has some, but not all, bits set and some, but
	/// not all, bits clear.
	///
	/// This is `false` if either `all()` or `not_any()` are `true`.
	///
	/// # Truth Table
	///
	/// ```text
	/// 0 0 => 0
	/// 0 1 => 1
	/// 1 0 => 1
	/// 1 1 => 0
	/// ```
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Whether the slice domain has mixed content. The empty slice returns
	/// `false`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0b111_000_10u8.bits::<BigEndian>();
	/// assert!(!bits[0 .. 3].some());
	/// assert!(!bits[3 .. 6].some());
	/// assert!(bits[6 ..].some());
	/// ```
	pub fn some(&self) -> bool {
		self.any() && self.not_all()
	}

	/// Counts how many bits are set high.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The number of high bits in the slice domain.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = [0xFDu8, 0x25].bits::<BigEndian>();
	/// assert_eq!(bits.count_ones(), 10);
	/// ```
	pub fn count_ones(&self) -> usize {
		match self.bitptr().domain() {
			BitDomain::Empty => 0,
			BitDomain::Minor(head, elt, tail) => {
				(*head .. *tail)
					.map(|n| elt.get::<C>(n.idx()))
					.filter(|b| *b)
					.count()
			},
			BitDomain::Major(h, head, body, tail, t) => {
				(*h .. T::BITS)
					.map(|n| head.get::<C>(n.idx()))
					.filter(|b| *b)
					.count() +
				body.iter()
					.map(T::count_ones)
					.sum::<usize>() +
				(0 .. *t)
					.map(|n| tail.get::<C>(n.idx()))
					.filter(|b| *b)
					.count()
			},
			BitDomain::PartialHead(h, head, body) => {
				(*h .. T::BITS)
					.map(|n| head.get::<C>(n.idx()))
					.filter(|b| *b)
					.count() +
				body.iter()
					.map(T::count_ones)
					.sum::<usize>()
			},
			BitDomain::PartialTail(body, tail, t) => {
				body.iter()
					.map(T::count_ones)
					.sum::<usize>() +
				(0 .. *t)
					.map(|n| tail.get::<C>(n.idx()))
					.filter(|b| *b)
					.count()
			},
			BitDomain::Spanning(body) => {
				body.iter()
					.map(T::count_ones)
					.sum::<usize>()
			}
		}
	}

	/// Counts how many bits are set low.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The number of low bits in the slice domain.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = [0xFDu8, 0x25].bits::<BigEndian>();
	/// assert_eq!(bits.count_zeros(), 6);
	/// ```
	pub fn count_zeros(&self) -> usize {
		match self.bitptr().domain() {
			BitDomain::Empty => 0,
			BitDomain::Minor(head, elt, tail) => {
				(*head .. *tail)
					.map(|n| !elt.get::<C>(n.idx()))
					.filter(|b| !*b)
					.count()
			},
			BitDomain::Major(h, head, body, tail, t) => {
				(*h .. T::BITS)
					.map(|n| head.get::<C>(n.idx()))
					.filter(|b| !*b)
					.count() +
				body.iter()
					.map(T::count_zeros)
					.sum::<usize>() +
				(0 .. *t)
					.map(|n| tail.get::<C>(n.idx()))
					.filter(|b| !*b)
					.count()
			},
			BitDomain::PartialHead(h, head, body) => {
				(*h .. T::BITS)
					.map(|n| head.get::<C>(n.idx()))
					.filter(|b| !*b)
					.count() +
				body.iter()
					.map(T::count_zeros)
					.sum::<usize>()
			},
			BitDomain::PartialTail(body, tail, t) => {
				body.iter()
					.map(T::count_zeros)
					.sum::<usize>() +
				(0 .. *t)
					.map(|n| tail.get::<C>(n.idx()))
					.filter(|b| !*b)
					.count()
			},
			BitDomain::Spanning(body) => {
				body.iter()
					.map(T::count_zeros)
					.sum::<usize>()
			},
		}
	}

	/// Set all bits in the slice to a value.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `value`: The bit value to which all bits in the slice will be set.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// let bits = src.bits_mut::<BigEndian>();
	/// bits[2 .. 6].set_all(true);
	/// assert_eq!(bits.as_ref(), &[0b0011_1100]);
	/// bits[3 .. 5].set_all(false);
	/// assert_eq!(bits.as_ref(), &[0b0010_0100]);
	/// bits[.. 1].set_all(true);
	/// assert_eq!(bits.as_ref(), &[0b1010_0100]);
	/// ```
	pub fn set_all(&mut self, value: bool) {
		match self.bitptr().domain_mut() {
			BitDomainMut::Empty => {},
			BitDomainMut::Minor(head, elt, tail) => {
				for n in *head .. *tail {
					elt.set::<C>(n.idx(), value);
				}
			},
			BitDomainMut::Major(h, head, body, tail, t) => {
				for n in *h .. T::BITS {
					head.set::<C>(n.idx(), value);
				}
				for elt in body {
					*elt = T::bits(value);
				}
				for n in 0 .. *t {
					tail.set::<C>(n.idx(), value);
				}
			},
			BitDomainMut::PartialHead(h, head, body) => {
				for n in *h .. T::BITS {
					head.set::<C>(n.idx(), value);
				}
				for elt in body {
					*elt = T::bits(value);
				}
			},
			BitDomainMut::PartialTail(body, tail, t) => {
				for elt in body {
					*elt = T::bits(value);
				}
				for n in 0 .. *t {
					tail.set::<C>(n.idx(), value);
				}
			},
			BitDomainMut::Spanning(body) => {
				for elt in body {
					*elt = T::bits(value);
				}
			},
		}
	}

	/// Provides mutable traversal of the collection.
	///
	/// It is impossible to implement `IndexMut` on `BitSlice`, because bits do
	/// not have addresses, so there can be no `&mut u1`. This method allows the
	/// client to receive an enumerated bit, and provide a new bit to set at
	/// each index.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `func`: A function which receives a `(usize, bool)` pair of index and
	///   value, and returns a bool. It receives the bit at each position, and
	///   the return value is written back at that position.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// {
	///  let bits = src.bits_mut::<BigEndian>();
	///  bits.for_each(|idx, _bit| idx % 3 == 0);
	/// }
	/// assert_eq!(src, 0b1001_0010);
	/// ```
	pub fn for_each<F>(&mut self, func: F)
	where F: Fn(usize, bool) -> bool {
		for idx in 0 .. self.len() {
			let tmp = self[idx];
			self.set(idx, func(idx, tmp));
		}
	}

	/// Performs “reverse” addition (left to right instead of right to left).
	///
	/// This addition interprets the slice, and the other addend, as having its
	/// least significant bits first in the order and its most significant bits
	/// last. This is most likely to be numerically useful under a
	/// `LittleEndian` `Cursor` type.
	///
	/// # Parameters
	///
	/// - `&mut self`: The addition uses `self` as one addend, and writes the
	///   sum back into `self`.
	/// - `addend: impl IntoIterator<Item=bool>`: A stream of bits. When this is
	///   another `BitSlice`, iteration proceeds from left to right.
	///
	/// # Return
	///
	/// The final carry bit is returned
	///
	/// # Effects
	///
	/// Starting from index `0` and proceeding upwards until either `self` or
	/// `addend` expires, the carry-propagated addition of `self[i]` and
	/// `addend[i]` is written to `self[i]`.
	///
	/// ```text
	///   101111
	/// + 0010__ (the two missing bits are logically zero)
	/// --------
	///   100000 1 (the carry-out is returned)
	/// ```
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut a = 0b0000_1010u8;
	/// let     b = 0b0000_1100u8;
	/// //      s =      1 0110
	/// let ab = &mut a.bits_mut::<LittleEndian>()[.. 4];
	/// let bb = &    b.bits::<LittleEndian>()[.. 4];
	/// let c = ab.add_assign_reverse(bb);
	/// assert!(c);
	/// assert_eq!(a, 0b0000_0110u8);
	/// ```
	///
	/// # Performance Notes
	///
	/// When using `LittleEndian` `Cursor` types, this can be accelerated by
	/// delegating the addition to the underlying types. This is a software
	/// implementation of the [ripple-carry adder], which has `O(n)` runtime in
	/// the number of bits. The CPU is much faster, as it has access to
	/// element-wise or vectorized addition operations.
	///
	/// If your use case sincerely needs binary-integer arithmetic operations on
	/// bit sets
	///
	/// [ripple-carry adder]: https://en.wikipedia.org/wiki/Ripple-carry_adder
	pub fn add_assign_reverse<I>(&mut self, addend: I) -> bool
	where I: IntoIterator<Item=bool> {
		//  See AddAssign::add_assign for algorithm details
		let mut c = false;
		let len = self.len();
		let zero = core::iter::repeat(false);
		for (i, b) in addend.into_iter().chain(zero).enumerate().take(len) {
			//  The iterator is clamped to the upper bound of `self`.
			let a = unsafe { self.get_unchecked(i) };
			let (y, z) = crate::rca1(a, b, c);
			//  Write the sum into `self`
			unsafe { self.set_unchecked(i, y); }
			//  Propagate the carry
			c = z;
		}
		c
	}

	/// Accesses the backing storage of the `BitSlice` as a slice of its
	/// elements.
	///
	/// Note that this does *not* include any partial elements of the `BitSlice`
	/// in the produced element slice. `BitSlice` regions are permitted to be
	/// adjacent and to occupy different parts of the same element; as such,
	/// using them to obtain a view of the entire element beyond their
	/// boundaries is a memory safety violation.
	///
	/// Heuristically, this restriction is not considered likely to be a serious
	/// detriment in practice. If you need to view the underlying elements of a
	/// `BitSlice`, you likely also do not have a region with partial elements.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A slice of all the full elements that the `BitSlice` uses for storage.
	/// Partial elements at either edge are not included.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [1u8, 66];
	/// let bits = src.bits::<BigEndian>();
	///
	/// let accum = bits.as_slice()
	///   .iter()
	///   .map(|elt| elt.count_ones())
	///   .sum::<usize>();
	/// assert_eq!(accum, 3);
	/// ```
	///
	/// This demonstrates that the partial edges are not in the output slice.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [0u8; 3];
	/// let bits = &src.bits::<BigEndian>()[4 .. 20];
	/// assert_eq!(bits.as_slice().len(), 1);
	/// ```
	pub fn as_slice(&self) -> &[T] {
		match self.bitptr().domain() {
			| BitDomain::Empty
			| BitDomain::Minor(..) => &[],
			| BitDomain::Major(_, _, s, _, _)
			| BitDomain::PartialHead(_, _, s)
			| BitDomain::PartialTail(s, _, _)
			| BitDomain::Spanning(s)=> s,
		}
	}

	/// Accesses the underlying element store, including partial elements.
	///
	/// # Safety
	///
	/// This function is marked `unsafe` because it will access the entirety of
	/// elements to which the `BitSlice` handle does not necessarily have
	/// complete access. Two adjacent `BitSlice` handles that do not consider
	/// themselves aliasing because they govern different *bits* can
	/// nevertheless produce element slices that do alias the same element.
	///
	/// While this immutable references are free to alias each other, Rust
	/// forbids the construction of an immutable reference that aliases a
	/// mutable reference. This function is permitted to do so, and thus must be
	/// marked unsafe.
	///
	/// Note that constructing aliasing mutable references is undefined
	/// behavior, and the compiler is permitted to miscompile your crate if it
	/// can prove that you are doing so.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A slice of all elements, full and partial, in the `BitSlice`’s domain.
	pub unsafe fn as_total_slice(&self) -> &[T] {
		self.bitptr().as_slice()
	}

	/// Accesses the underlying store.
	///
	/// Note that this does *not* include any partial elements of the `BitSlice`
	/// in the produced element slice. `BitSlice` regions are permitted to be
	/// adjacent and to occupy different parts of the same element; as such,
	/// using them to obtain a view of the entire element beyond their
	/// boundaries is a memory safety violation.
	///
	/// Heuristically, this restriction is not considered likely to be a serious
	/// detriment in practice. If you need to view the underlying elements of a
	/// `BitSlice`, you likely also do not have a region with partial elements.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [1u8, 64];
	/// let bits = src.bits_mut::<BigEndian>();
	/// for elt in bits.as_mut_slice() {
	///   *elt |= 2;
	/// }
	/// assert_eq!(&[3, 66], bits.as_slice());
	/// ```
	pub fn as_mut_slice(&mut self) -> &mut [T] {
		match self.bitptr().domain_mut() {
			| BitDomainMut::Empty
			| BitDomainMut::Minor(..) => &mut [],
			| BitDomainMut::Major(_, _, s, _, _)
			| BitDomainMut::PartialHead(_, _, s)
			| BitDomainMut::PartialTail(s, _, _)
			| BitDomainMut::Spanning(s) => s
		}
	}

	/// Accesses the underlying element store, including partial elements.
	///
	/// # Safety
	///
	/// This function is marked `unsafe` because it will access the entirety of
	/// elements to which the `BitSlice` handle does not necessarily have
	/// complete access. Two adjacent `BitSlice` handles that do not consider
	/// themselves aliasing because they govern different *bits* can
	/// nevertheless produce element slices that do alias the same element.
	///
	/// Mutable references are never allowed to alias any other reference, but
	/// this function may create an aliased mutable reference if used
	/// improperly.
	///
	/// Note that constructing aliasing mutable references is undefined
	/// behavior, and the compiler is permitted to miscompile your crate if it
	/// can prove that you are doing so.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A slice of all elements, full and partial, in the `BitSlice`’s domain.
	pub unsafe fn as_total_mut_slice(&mut self) -> &mut [T] {
		self.bitptr().as_mut_slice()
	}

	/// Changes the cursor type of the slice handle.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// An equivalent slice handle with a new cursor type.
	///
	/// # Type Parameters
	///
	/// - `D: Cursor` The new cursor type to use for the handle.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 2u8;
	/// let bits = src.bits::<BigEndian>();
	/// assert!(bits[6]);
	/// let bits = bits.change_cursor::<LittleEndian>();
	/// assert!(bits[1]);
	/// ```
	pub fn change_cursor<D>(&self) -> &BitSlice<D, T>
	where D: Cursor {
		self.bitptr().into_bitslice()
	}

	/// Changes the cursor type of the slice handle.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// An equivalent slice handle with a new cursor type.
	///
	/// # Type Parameters
	///
	/// - `D: Cursor` The new cursor type to use for the handle.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// *src.bits_mut::<BigEndian>().at(1) = true;
	/// assert_eq!(src, 64);
	/// src.bits_mut::<BigEndian>()
	///    .change_cursor_mut::<LittleEndian>()
	///    .set(1, true);
	/// assert_eq!(src, 66);
	/// ```
	pub fn change_cursor_mut<D>(&mut self) -> &mut BitSlice<D, T>
	where D: Cursor {
		self.bitptr().into_bitslice_mut()
	}

	/// Unconditionally copies a bit from one index to another.
	///
	/// This is equivalent to `self[to] = self[from]`.
	///
	/// # Safety
	///
	/// This function performs no bounds checks. It must only be called from
	/// within a checked context.
	///
	/// # Parameters
	///
	/// -`&mut self`
	/// - `from`: The index at which a bit will be unconditionally fetched.
	/// - `to`: The index at which the fetched bit will be unconditionally set.
	#[inline]
	pub(crate) unsafe fn copy(&mut self, from: usize, to: usize) {
		let bit = self.get_unchecked(from);
		self.set_unchecked(to, bit);
	}

	/// Accesses the underlying pointer structure.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The [`BitPtr`] structure of the slice handle.
	///
	/// [`BitPtr`]: ../pointer/struct.BitPtr.html
	pub fn bitptr(&self) -> BitPtr<T> {
		BitPtr::from_bitslice(self)
	}
}

/** Write reference to a single bit.

Rust requires that `DerefMut` produce the plain address of a value which can be
written with a `memcpy`, so, there is no way to make plain write assignments
work nicely in Rust. This reference structure is the second best option.

It contains a write reference to a single-bit slice, and a local cache `bool`.
This structure `Deref`s to the local cache, and commits the cache to the slice
on drop. This allows writing to the guard with `=` assignment.
**/
#[derive(Debug)]
pub struct BitGuard<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	slot: &'a mut BitSlice<C, T>,
	bit: bool,
	_m: PhantomData<*mut T>,
}

/// Read from the local cache.
impl<'a, C, T> Deref for BitGuard<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Target = bool;

	fn deref(&self) -> &Self::Target {
		&self.bit
	}
}

/// Write to the local cache.
impl<'a, C, T> DerefMut for BitGuard<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.bit
	}
}

/// Commit the local cache to the backing slice.
impl<'a, C, T> Drop for BitGuard<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn drop(&mut self) {
		self.slot.set(0, self.bit);
	}
}

/// This type is a mutable reference with extra steps, so, it should be moveable
/// but not shareable.
#[cfg(feature = "atomic")]
unsafe impl<'a, C, T> Send for BitGuard<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

mod iter;
mod ops;
mod traits;

pub use iter::*;
