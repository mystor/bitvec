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

impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
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

impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
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

/// Provides write access to all fully-owned elements in the underlying storage.
/// This excludes the elements at either edge if they may be aliased by another
/// slice.
impl<C, T> AsMut<[T]> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn as_mut(&mut self) -> &mut [T] {
		self.as_mut_slice()
	}
}

/// Provides read access to all fully-owned elements in the underlying storage.
/// This excludes the elements at either edge if they may be accessed by another
/// slice.
impl<C, T> AsRef<[T]> for BitSlice<C, T>
where C: Cursor, T: BitStore {
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

impl<C, T> Debug for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		f.write_str("BitSlice<")?;
		f.write_str(type_name::<C>())?;
		f.write_str(", ")?;
		f.write_str(type_name::<T>())?;
		f.write_str("> ")?;
		Display::fmt(self, f)
	}
}

impl<C, T> Display for BitSlice<C, T>
where C: Cursor, T: BitStore {
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
