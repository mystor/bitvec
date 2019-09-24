/*! Bit management

The `BitStore` trait defines constants and associated functions suitable for
managing the bit patterns of a fundamental, and is the constraint for the
storage type of the data structures of the rest of the crate.

The other types in this module provide stronger rules about how indices map to
concrete bits in fundamental elements. They are implementation details, and are
not exported in the prelude.
!*/

use crate::{
	cursor::Cursor,
	indices::*,
};

use core::{
	cmp::Eq,
	convert::From,
	fmt::{
		Binary,
		Debug,
		Display,
		LowerHex,
		UpperHex,
	},
	mem::size_of,
	ops::{
		BitAnd,
		BitAndAssign,
		BitOrAssign,
		Not,
		Shl,
		ShlAssign,
		Shr,
		ShrAssign,
	},
};

#[cfg(feature = "atomic")]
use crate::atomic::Atomic;

#[cfg(feature = "atomic")]
use core::sync::atomic;

/** Generalizes over the fundamental types for use in `bitvec` data structures.

This trait must only be implemented on unsigned integer primitives with full
alignment. It cannot be implemented on `u128` on any architecture, or on `u64`
on 32-bit systems.

The `Sealed` supertrait ensures that this can only be implemented locally, and
will never be implemented by downstream crates on new types.
**/
pub trait BitStore:
	//  Forbid external implementation
	Sealed
	+ Binary
	//  Element-wise binary manipulation
	+ BitAnd<Self, Output=Self>
	+ BitAndAssign<Self>
	+ BitOrAssign<Self>
	//  Permit indexing into a generic array
	+ Copy
	+ Debug
	+ Display
	//  Permit testing a value against 1 in `get()`.
	+ Eq
	//  Rust treats numeric literals in code as vaguely typed and does not make
	//  them concrete until long after trait expansion, so this enables building
	//  a concrete Self value from a numeric literal.
	+ From<u8>
	//  Permit extending into a `u64`.
	+ Into<u64>
	+ LowerHex
	+ Not<Output=Self>
	+ Send
	+ Shl<u8, Output=Self>
	+ ShlAssign<u8>
	+ Shr<u8, Output=Self>
	+ ShrAssign<u8>
	//  Allow direct access to a concrete implementor type.
	+ Sized
	+ Sync
	+ UpperHex
{
	/// The width, in bits, of this type.
	const BITS: u8 = size_of::<Self>() as u8 * 8;

	/// The number of bits required to index a bit inside the type. This is
	/// always log<sub>2</sub> of the type’s bit width.
	const INDX: u8 = Self::BITS.trailing_zeros() as u8;

	/// The bitmask to turn an arbitrary number into a bit index. Bit indices
	/// are always stored in the lowest bits of an index value.
	const MASK: u8 = Self::BITS - 1;

	/// Name of the implementing type. This is only necessary until the compiler
	/// stabilizes `type_name()`.
	const TYPENAME: &'static str;

	/// Atomic version of the storage type, to have properly fenced access.
	#[cfg(feature = "atomic")]
	#[doc(hidden)]
	type Atom: Atomic<Self>;

	/// Performs a synchronized load on the underlying element.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The element referred to by the `self` reference, loaded synchronously
	/// after any in-progress accesses have concluded.
	#[cfg(feature = "atomic")]
	#[inline(always)]
	fn load(&self) -> Self {
		let aptr = self as *const Self as *const Self::Atom;
		unsafe { &*aptr }.get()
	}

	/// Performs an unsynchronized load on the underlying element.
	///
	/// As atomic operations are unavailable, this is a standard dereference.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The referent element.
	#[cfg(not(feature = "atomic"))]
	#[inline(always)]
	fn load(&self) -> Self {
		*self
	}

	/// Sets a specific bit in an element to a given value.
	///
	/// # Parameters
	///
	/// - `place`: A bit index in the element, from `0` to `Self::MASK`. The bit
	///   under this index will be set according to `value`.
	/// - `value`: A Boolean value, which sets the bit on `true` and unsets it
	///   on `false`.
	///
	/// # Type Parameters
	///
	/// - `C: Cursor`: A `Cursor` implementation to translate the index into a
	///   position.
	///
	/// # Panics
	///
	/// This function panics if `place` is not less than `T::BITS`, in order to
	/// avoid index out of range errors.
	#[inline(always)]
	fn set<C>(&mut self, place: BitIdx<Self>, value: bool)
	where C: Cursor {
		self.set_at(C::at::<Self>(place), value)
	}

	/// Sets a specific bit in an element to a given value.
	///
	/// # Parameters
	///
	/// - `place`: A bit *position* in the element, where `0` is the LSbit and
	///   `Self::MASK` is the MSbit.
	/// - `value`: A Boolean value, which sets the bit high on `true` and unsets
	///   it low on `false`.
	///
	/// # Panics
	///
	/// This function panics if `place` is not less than `T::BITS`, in order to
	/// avoid index out of range errors.
	fn set_at(&mut self, place: BitPos<Self>, value: bool) {
		#[cfg(feature = "atomic")] {
			let aptr = self as *const Self as *const Self::Atom;
			if value {
				unsafe { &*aptr }.set(place);
			}
			else {
				unsafe { &*aptr }.clear(place);
			}
		}
		#[cfg(not(feature = "atomic"))] {
			if value {
				*self |= Self::mask_at(place);
			}
			else {
				*self &= !Self::mask_at(place);
			}
		}
	}

	/// Gets a specific bit in an element.
	///
	/// # Parameters
	///
	/// - `place`: A bit index in the element, from `0` to `Self::MASK`. The bit
	///   under this index will be retrieved as a `bool`.
	///
	/// # Returns
	///
	/// The value of the bit under `place`, as a `bool`.
	///
	/// # Type Parameters
	///
	/// - `C: Cursor`: A `Cursor` implementation to translate the index into a
	///   position.
	///
	/// # Panics
	///
	/// This function panics if `place` is not less than `T::BITS`, in order to
	/// avoid index out of range errors.
	fn get<C>(&self, place: BitIdx<Self>) -> bool
	where C: Cursor {
		self.get_at(C::at::<Self>(place))
	}

	/// Gets a specific bit in an element.
	///
	/// # Parameters
	///
	/// - `place`: A bit *position* in the element, from `0` at LSbit to
	///   `Self::MASK` at MSbit. The bit under this position will be retrieved
	///   as a `bool`.
	///
	/// # Returns
	///
	/// The value of the bit under `place`, as a `bool`.
	///
	/// # Panics
	///
	/// This function panics if `place` is not less than `T::BITS`, in order to
	/// avoid index out of range errors.
	fn get_at(&self, place: BitPos<Self>) -> bool {
		self.load() & Self::mask_at(place) != Self::from(0u8)
	}

	/// Produces the bit mask which selects only the bit at the requested
	/// position.
	///
	/// This mask must be inverted in order to clear the bit.
	///
	/// # Parameters
	///
	/// - `place`: The bit position for which to create a bitmask.
	///
	/// # Returns
	///
	/// The one-hot encoding of the bit position index.
	///
	/// # Panics
	///
	/// This function panics if `place` is not less than `T::BITS`, in order to
	/// avoid index out of range errors.
	#[inline(always)]
	fn mask_at(place: BitPos<Self>) -> Self {
		//  Pad 1 to the correct width, then shift up to the correct bit place.
		Self::from(1u8) << *place
	}

	/// Counts how many bits in `self` are set to `1`.
	///
	/// This zero-extends `self` to `u64`, and uses the [`u64::count_ones`]
	/// inherent method.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The number of bits in `self` set to `1`. This is a `usize` instead of a
	/// `u32` in order to ease arithmetic throughout the crate.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::BitStore;
	/// assert_eq!(BitStore::count_ones(&0u8), 0);
	/// assert_eq!(BitStore::count_ones(&128u8), 1);
	/// assert_eq!(BitStore::count_ones(&192u8), 2);
	/// assert_eq!(BitStore::count_ones(&224u8), 3);
	/// assert_eq!(BitStore::count_ones(&240u8), 4);
	/// assert_eq!(BitStore::count_ones(&248u8), 5);
	/// assert_eq!(BitStore::count_ones(&252u8), 6);
	/// assert_eq!(BitStore::count_ones(&254u8), 7);
	/// assert_eq!(BitStore::count_ones(&255u8), 8);
	/// ```
	///
	/// [`u64::count_ones`]: https://doc.rust-lang.org/stable/std/primitive.u64.html#method.count_ones
	#[inline(always)]
	fn count_ones(&self) -> usize {
		u64::count_ones((self.load()).into()) as usize
	}

	/// Counts how many bits in `self` are set to `0`.
	///
	/// This inverts `self`, so all `0` bits are `1` and all `1` bits are `0`,
	/// then zero-extends `self` to `u64` and uses the [`u64::count_ones`]
	/// inherent method.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The number of bits in `self` set to `0`. This is a `usize` instead of a
	/// `u32` in order to ease arithmetic throughout the crate.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::BitStore;
	/// assert_eq!(BitStore::count_zeros(&0u8), 8);
	/// assert_eq!(BitStore::count_zeros(&1u8), 7);
	/// assert_eq!(BitStore::count_zeros(&3u8), 6);
	/// assert_eq!(BitStore::count_zeros(&7u8), 5);
	/// assert_eq!(BitStore::count_zeros(&15u8), 4);
	/// assert_eq!(BitStore::count_zeros(&31u8), 3);
	/// assert_eq!(BitStore::count_zeros(&63u8), 2);
	/// assert_eq!(BitStore::count_zeros(&127u8), 1);
	/// assert_eq!(BitStore::count_zeros(&255u8), 0);
	/// ```
	///
	/// [`u64::count_ones`]: https://doc.rust-lang.org/stable/std/primitive.u64.html#method.count_ones
	#[inline(always)]
	fn count_zeros(&self) -> usize {
		//  invert (0 becomes 1, 1 becomes 0), zero-extend, count ones
		u64::count_ones((!self.load()).into()) as usize
	}

	/// Extends a single bit to fill the entire element.
	///
	/// # Parameters
	///
	/// - `bit`: The bit to extend.
	///
	/// # Returns
	///
	/// An element with all bits set to the input.
	#[inline]
	fn bits(bit: bool) -> Self {
		if bit {
			!Self::from(0)
		}
		else {
			Self::from(0)
		}
	}
}

impl BitStore for u8 {
	const TYPENAME: &'static str = "u8";

	#[cfg(feature = "atomic")]
	type Atom = atomic::AtomicU8;
}

impl BitStore for u16 {
	const TYPENAME: &'static str = "u16";

	#[cfg(feature = "atomic")]
	type Atom = atomic::AtomicU16;
}

impl BitStore for u32 {
	const TYPENAME: &'static str = "u32";

	#[cfg(feature = "atomic")]
	type Atom = atomic::AtomicU32;
}

#[cfg(target_pointer_width = "64")]
impl BitStore for u64 {
	const TYPENAME: &'static str = "u64";

	#[cfg(feature = "atomic")]
	type Atom = atomic::AtomicU64;
}

/// Marker trait to seal `BitStore` against downstream implementation.
///
/// This trait is public in the module, so that other modules in the crate can
/// use it, but so long as it is not exported by the crate root and this module
/// is private, this trait effectively forbids downstream implementation of the
/// `BitStore` trait.
#[doc(hidden)]
pub trait Sealed {}

impl Sealed for u8 {}
impl Sealed for u16 {}
impl Sealed for u32 {}

#[cfg(target_pointer_width = "64")]
impl Sealed for u64 {}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn jump_far_up() {
		//  isize::max_value() is 0x7f...ff, so the result bit will be one less
		//  than the start bit.
		for n in 1 .. 8 {
			let (elt, bit) = n.idx::<u8>().offset(isize::max_value());
			assert_eq!(elt, (isize::max_value() >> u8::INDX) + 1);
			assert_eq!(*bit, n - 1);
		}
		let (elt, bit) = 0.idx::<u8>().offset(isize::max_value());
		assert_eq!(elt, isize::max_value() >> u8::INDX);
		assert_eq!(*bit, 7);
	}

	#[test]
	fn jump_far_down() {
		//  isize::min_value() is 0x80...00, so the result bit will be equal to
		//  the start bit
		for n in 0 .. 8 {
			let (elt, bit) = n.idx::<u8>().offset(isize::min_value());
			assert_eq!(elt, isize::min_value() >> u8::INDX);
			assert_eq!(*bit, n);
		}
	}

	#[test]
	fn bits() {
		assert_eq!(u8::bits(false), 0);
		assert_eq!(u8::bits(true), u8::max_value());

		assert_eq!(u16::bits(false), 0);
		assert_eq!(u16::bits(true), u16::max_value());

		assert_eq!(u32::bits(false), 0);
		assert_eq!(u32::bits(true), u32::max_value());

		#[cfg(target_pointer_width = "64")]
		assert_eq!(u64::bits(false), 0);
		#[cfg(target_pointer_width = "64")]
		assert_eq!(u64::bits(true), u64::max_value());
	}
}
