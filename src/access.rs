/*! Safely shared/mutable element access.

This module unifies access to raw memory, which cannot use standard element
references but must use either `Cell` (non-atomic builds) or `AtomicT` (atomic
builds) in order to safely perform any access when the program may hold aliased
accesses.

It is undefined behavior to perform any reads of a memory location which has
aliased write accesses, even if the read only observes stable uncontended bits.
As such, this module must be used for all productions of raw memory accesses,
and the rest of the crate may only produce bare references when the pointers are
known to describe wholly unaliased memory.
!*/

use crate::{
	cursor::Cursor,
	indices::BitIdx,
	store::BitStore,
};

use core::{
	cell::Cell,
	sync::{
		atomic::{
			AtomicU8,
			AtomicU16,
			AtomicU32,
			Ordering,
		},
	},
};

#[cfg(target_pointer_width = "64")]
use core::sync::atomic::AtomicU64;

pub trait BitAccess<T>
where T: BitStore {
	fn clear_bit<C>(&self, place: BitIdx<T>)
	where C: Cursor;

	fn set_bit<C>(&self, place: BitIdx<T>)
	where C: Cursor;

	fn invert_bit<C>(&self, place: BitIdx<T>)
	where C: Cursor;

	fn get<C>(&self, place: BitIdx<T>) -> bool
	where C: Cursor;

	#[inline(always)]
	fn set<C>(&self, place: BitIdx<T>, value: bool)
	where C: Cursor {
		if value {
			self.set_bit::<C>(place);
		}
		else {
			self.clear_bit::<C>(place);
		}
	}

	fn load(&self) -> T;
}

macro_rules! access {
	( $( impl $a:ty , $t:ty $( ; )? )* ) => { $(
		access!( atom $a , $t );
		access!( cell $t );
	)* };

	( atom $a:ty , $t:ty ) => {
		impl BitAccess<$t> for $a {
			#[inline(always)]
			fn clear_bit<C>(&self, place: BitIdx<$t>)
			where C: Cursor {
				self.fetch_and(!*C::mask(place), Ordering::Relaxed);
			}

			#[inline(always)]
			fn set_bit<C>(&self, place: BitIdx<$t>)
			where C: Cursor {
				self.fetch_or(*C::mask(place), Ordering::Relaxed);
			}

			#[inline(always)]
			fn invert_bit<C>(&self, place: BitIdx<$t>)
			where C: Cursor {
				self.fetch_xor(*C::mask(place), Ordering::Relaxed);
			}

			#[inline(always)]
			fn get<C>(&self, place: BitIdx<$t>) -> bool
			where C: Cursor {
				<$a>::load(self, Ordering::Relaxed) & *C::mask(place) != <$t>::from(0u8)
			}

			#[inline(always)]
			fn load(&self) -> $t {
				<$a>::load(self, Ordering::Relaxed)
			}
		}
	};

	( cell $t:ty ) => {
		impl BitAccess<$t> for Cell<$t> {
			#[inline(always)]
			fn clear_bit<C>(&self, place: BitIdx<$t>)
			where C: Cursor {
				self.set(self.get() & !*C::mask(place));
			}

			#[inline(always)]
			fn set_bit<C>(&self, place: BitIdx<$t>)
			where C: Cursor {
				self.set(self.get() | *C::mask(place));
			}

			#[inline(always)]
			fn invert_bit<C>(&self, place: BitIdx<$t>)
			where C: Cursor {
				self.set(self.get() ^ *C::mask(place));
			}

			#[inline(always)]
			fn get<C>(&self, place: BitIdx<$t>) -> bool
			where C: Cursor {
				<Self>::get(self) & *C::mask(place) != <$t>::from(0u8)
			}

			#[inline(always)]
			fn load(&self) -> $t {
				<Self>::get(self)
			}
		}
	};
}

access![
	impl AtomicU8, u8;
	impl AtomicU16, u16;
	impl AtomicU32, u32;
];

#[cfg(target_pointer_width = "64")]
access![impl AtomicU64, u64];
