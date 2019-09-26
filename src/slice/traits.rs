//! `BitSlice` miscellaneous trait implementations.

use super::BitSlice;

use crate::{
	access::BitAccess,
	cursor::Cursor,
	domain::BitDomain,
	indices::IntoBitIdx,
	store::BitStore,
};

use core::{
	any::type_name,
	cmp::Ordering,
	fmt::{
		self,
		Debug,
		DebugList,
		Display,
		Formatter,
	},
	hash::{
		Hash,
		Hasher,
	},
	str,
};

#[cfg(feature = "alloc")]
use {
	crate::vec::BitVec,
	alloc::borrow::ToOwned,
};

/// Creates an owned `BitVec<C, T>` from a borrowed `BitSlice<C, T>`.
#[cfg(feature = "alloc")]
impl<C, T> ToOwned for BitSlice<C, T>
where C: Cursor, T: BitStore {
	type Owned = BitVec<C, T>;

	/// Clones a borrowed `BitSlice` into an owned `BitVec`.
	///
	/// # Examples
	///
	/// ```rust
	/// # #[cfg(feature = "alloc")] {
	/// use bitvec::prelude::*;
	///
	/// let store = [0u8, 2];
	/// let src = store.bits::<LittleEndian>();
	/// let dst = src.to_owned();
	/// assert_eq!(src, dst);
	/// # }
	/// ```
	fn to_owned(&self) -> Self::Owned {
		Self::Owned::from_bitslice(self)
	}
}

impl<C, T> Eq for BitSlice<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> Ord for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn cmp(&self, rhs: &Self) -> Ordering {
		self.partial_cmp(rhs)
			.unwrap_or_else(|| unreachable!("`BitSlice` has a total ordering"))
	}
}

/** Tests if two `BitSlice`s are semantically — not bitwise — equal.

It is valid to compare two slices of different cursor or element types.

The equality condition requires that they have the same number of total bits and
that each pair of bits in semantic order are identical.
**/
impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	/// Performas a comparison by `==`.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `rhs`: Another `BitSlice` against which to compare. This slice can
	///   have different cursor or storage types.
	///
	/// # Returns
	///
	/// If the two slices are equal, by comparing the lengths and bit values at
	/// each semantic index.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let lsrc = [8u8, 16, 32, 0];
	/// let rsrc = [0x10_08_04_00u32];
	/// let lbits = lsrc.bits::<LittleEndian>();
	/// let rbits = rsrc.bits::<BigEndian>();
	///
	/// assert_eq!(lbits, rbits);
	/// ```
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		if self.len() != rhs.len() {
			return false;
		}
		self.iter().zip(rhs.iter()).all(|(l, r)| l == r)
	}
}

impl<A, B, C, D> PartialEq<BitSlice<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		(*self).eq(rhs)
	}
}

/// Allow comparison against the allocated form.
#[cfg(feature = "alloc")]
impl<A, B, C, D> PartialEq<BitVec<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		self.eq(rhs.as_bits())
	}
}

#[cfg(feature = "alloc")]
impl<A, B, C, D> PartialEq<BitVec<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		self.eq(rhs.as_bits())
	}
}

/** Compares two `BitSlice`s by semantic — not bitwise — ordering.

The comparison sorts by testing each index for one slice to have a set bit where
the other has a clear bit. If the slices are different, the slice with the set
bit sorts greater than the slice with the clear bit.

If one of the slices is exhausted before they differ, the longer slice is
greater.
**/
impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	/// Performs a comparison by `<` or `>`.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `rhs`: Another `BitSlice` against which to compare. This slice can
	///   have different cursor or storage types.
	///
	/// # Returns
	///
	/// The relative ordering of `self` against `rhs`. `self` is greater if it
	/// has a `true` bit at an index where `rhs` has a `false`; `self` is lesser
	/// if it has a `false` bit at an index where `rhs` has a `true`; if the two
	/// slices do not disagree then they are compared by length.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0x45u8;
	/// let bits = src.bits::<BigEndian>();
	/// let a = &bits[0 .. 3]; // 010
	/// let b = &bits[0 .. 4]; // 0100
	/// let c = &bits[0 .. 5]; // 01000
	/// let d = &bits[4 .. 8]; // 0101
	///
	/// assert!(a < b);
	/// assert!(b < c);
	/// assert!(c < d);
	/// ```
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<Ordering> {
		for (l, r) in self.iter().zip(rhs.iter()) {
			match (l, r) {
				(true, false) => return Some(Ordering::Greater),
				(false, true) => return Some(Ordering::Less),
				_ => continue,
			}
		}
		self.len().partial_cmp(&rhs.len())
	}
}

impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<Ordering> {
		(*self).partial_cmp(rhs)
	}
}

#[cfg(feature = "alloc")]
impl<A, B, C, D> PartialOrd<BitVec<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
		self.partial_cmp(rhs.as_bits())
	}
}

#[cfg(feature = "alloc")]
impl<A, B, C, D> PartialOrd<BitVec<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
		(*self).partial_cmp(rhs.as_bits())
	}
}

/// Provides write access to all elements in the underlying storage, including
/// the partial head and tail elements if present.
impl<C, T> AsMut<[T]> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Accesses the underlying store.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A mutable slice of all storage elements.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [0u8, 128];
	/// let bits = src.bits_mut::<BigEndian>();
	///
	/// for elt in bits.as_mut() {
	///   *elt += 2;
	/// }
	///
	/// assert_eq!(&[2, 130], bits.as_ref());
	/// ```
	fn as_mut(&mut self) -> &mut [T] {
		self.as_mut_slice()
	}
}

/// Provides read access to all elements in the underlying storage, including
/// the partial head and tail elements if present.
impl<C, T> AsRef<[T]> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Accesses the underlying store.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// An immutable slice of all storage elements.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [0u8, 128];
	/// let bits = src.bits::<BigEndian>();
	/// assert_eq!(&[0, 128], bits.as_ref());
	/// ```
	fn as_ref(&self) -> &[T] {
		self.as_slice()
	}
}

impl<'a, C, T> From<&'a T> for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn from(src: &'a T) -> Self {
		BitSlice::<C, T>::from_element(src)
	}
}

impl<'a, C, T> From<&'a [T]> for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn from(src: &'a [T]) -> Self {
		BitSlice::<C, T>::from_slice(src)
	}
}

impl<'a, C, T> From<&'a mut T> for &'a mut BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn from(src: &'a mut T) -> Self {
		BitSlice::<C, T>::from_element_mut(src)
	}
}

impl<'a, C, T> From<&'a mut [T]> for &'a mut BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn from(src: &'a mut [T]) -> Self {
		BitSlice::<C, T>::from_slice_mut(src)
	}
}

impl<'a, C, T> Default for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn default() -> Self {
		BitSlice::empty()
	}
}

impl<'a, C, T> Default for &'a mut BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn default() -> Self {
		BitSlice::empty_mut()
	}
}

/** Prints the `BitSlice` for debugging.

The output is of the form `BitSlice<C, T> [ELT, *]` where `<C, T>` is the cursor
and element type, with square brackets on each end of the bits and all the
elements of the array printed in binary. The printout is always in semantic
order, and may not reflect the underlying buffer. To see the underlying buffer,
use `.as_ref()`.

The alternate character `{:#?}` prints each element on its own line, rather than
having all elements on the same line.
**/
impl<C, T> Debug for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Renders the `BitSlice` type header and contents for debug.
	///
	/// # Examples
	///
	/// ```rust
	/// # #[cfg(feature = "alloc")] {
	/// use bitvec::prelude::*;
	///
	/// let src = [0b0101_0000_1111_0101u16, 0b00000000_0000_0010];
	/// let bits = &src.bits::<LittleEndian>()[.. 18];
	/// assert_eq!(
    ///     "BitSlice<bitvec::cursor::LittleEndian, u16> [1010111100001010, 01]",
	///     &format!("{:?}", bits),
	/// );
	/// # }
	/// ```
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		f.write_str("BitSlice<")?;
		f.write_str(type_name::<C>())?;
		f.write_str(", ")?;
		f.write_str(type_name::<T>())?;
		f.write_str("> ")?;
		Display::fmt(self, f)
	}
}

/** Prints the `BitSlice` for displaying.

This prints each element in turn, formatted in binary in semantic order (so the
first bit seen is printed first and the last bit seen is printed last). Each
element of storage is separated by a space for ease of reading.

The alternate character `{:#}` prints each element on its own line.

To see the in-memory representation, use `.as_ref()` to get access to the raw
elements and print that slice instead.
**/
impl<C, T> Display for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Renders the `BitSlice` contents for display.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `f`: The formatter into which `self` is written.
	///
	/// # Returns
	///
	/// The result of the formatting operation.
	///
	/// # Examples
	///
	/// ```rust
	/// # #[cfg(feature = "alloc")] {
	/// use bitvec::prelude::*;
	///
	/// let src = [0b01001011u8, 0b0100_0000];
	/// let bits = &src.bits::<BigEndian>()[.. 10];
	/// assert_eq!("[01001011, 01]", &format!("{}", bits));
	/// # }
	/// ```
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		struct Part<'a>(&'a str);
		impl<'a> Debug for Part<'a> {
			fn fmt(&self, f: &mut Formatter) -> fmt::Result {
				f.write_str(&self.0)
			}
		}

		let mut dbg = f.debug_list();
		if !self.is_empty() {
			//  Unfortunately, `T::BITS` cannot be used as the size for the
			//  array, due to limitations in the type system. As such, set it to
			//  the maximum used size.
			//
			//  This allows the writes to target a static buffer, rather
			//  than a dynamic string, making the formatter usable in
			//  `#![no_std]` contexts.
			let mut w: [u8; 64] = [b'0'; 64];
			fn writer<C, T>(
				l: &mut DebugList,
				w: &mut [u8; 64],
				e: &T,
				from: u8,
				to: u8,
			)
			where C: Cursor, T: BitStore {
				let (from, to) = (from as usize, to as usize);
				for (n, byte) in w.iter_mut().enumerate().take(to).skip(from) {
					*byte = b'0' + (e.get::<C>((n as u8).idx()) as u8);
				}
				l.entry(&Part(unsafe {
					str::from_utf8_unchecked(&w[from .. to])
				}));
			}
			match self.bitptr().domain() {
				BitDomain::Empty => {},
				BitDomain::Minor(head, elt, tail) => {
					writer::<C, T>(&mut dbg, &mut w, &elt.load(), *head, *tail)
				},
				BitDomain::Major(h, head, body, tail, t) => {
					writer::<C, T>(&mut dbg, &mut w, &head.load(), *h, T::BITS);
					for elt in body {
						writer::<C, T>(&mut dbg, &mut w, elt, 0, T::BITS);
					}
					writer::<C, T>(&mut dbg, &mut w, &tail.load(), 0, *t);
				},
				BitDomain::PartialHead(h, head, body) => {
					writer::<C, T>(&mut dbg, &mut w, &head.load(), *h, T::BITS);
					for elt in body {
						writer::<C, T>(&mut dbg, &mut w, elt, 0, T::BITS);
					}
				},
				BitDomain::PartialTail(body, tail, t) => {
					for elt in body {
						writer::<C, T>(&mut dbg, &mut w, elt, 0, T::BITS);
					}
					writer::<C, T>(&mut dbg, &mut w, &tail.load(), 0, *t);
				},
				BitDomain::Spanning(body) => {
					for elt in body {
						writer::<C, T>(&mut dbg, &mut w, elt, 0, T::BITS);
					}
				},
			}
		}
		dbg.finish()
	}
}

/// Writes the contents of the `BitSlice`, in semantic bit order, into a hasher.
impl<C, T> Hash for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Writes each bit of the `BitSlice`, as a full `bool`, into the hasher.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `hasher`: The hashing state into which the slice will be written.
	///
	/// # Type Parameters
	///
	/// - `H: Hasher`: The type of the hashing algorithm which receives the bits
	///   of `self`.
	fn hash<H>(&self, hasher: &mut H)
	where H: Hasher {
		for bit in self {
			hasher.write_u8(bit as u8);
		}
	}
}

/** `BitSlice` is safe to move across thread boundaries, when atomic operations
are enabled.

Consider this (contrived) example:

```rust
# #[cfg(feature = "std")] {
use bitvec::prelude::*;
use std::thread;

static mut SRC: u8 = 0;
# {
let bits = unsafe { SRC.bits_mut::<BigEndian>() };
let (l, r) = bits.split_at_mut(4);

let a = thread::spawn(move || l.set(2, true));
let b = thread::spawn(move || r.set(2, true));
a.join();
b.join();
# }

println!("{:02X}", unsafe { SRC });
# }
```

Without atomic operations, this is logically a data race. It *so happens* that,
on x86, the read/modify/write cycles used in the crate are *basically* atomic by
default, even when not specified as such. This is not necessarily true on other
architectures, however.
**/
#[cfg(feature = "atomic")]
unsafe impl<C, T> Send for BitSlice<C, T>
where C: Cursor, T: BitStore {}

/** Unsynchronized racing reads are undefined behavior.

Because `BitSlice` can create aliasing pointers to the same underlying memory
element, sending a *read* reference to another thread is still a data race in
the event that a `&mut BitSlice` was fractured in a manner that created an
alias condition, one alias was frozen and sent to another thread, and then the
**non**-frozen alias, which remained on the origin thread, was used to write to
the aliased element.

Without enabling bit-granular access analysis in the compiler, this restriction
must remain in place even though *this library* knows that read operations will
never observe racing writes that *change memory*.
**/
#[cfg(feature = "atomic")]
unsafe impl<C, T> Sync for BitSlice<C, T>
where C: Cursor, T: BitStore {}
