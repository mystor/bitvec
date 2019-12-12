/*! Check macro syntax and production

This test checks that the syntaxes the macro is expected to provide evaluate to
the correct types and values.
!*/

use bitvec::prelude::*;
use bitvec_macros::bitvec;

static PATTERN: &[bool] = &[true, false, true, true];

#[test]
fn check_bitvec_proc_macro() {
	let bv: BitVec<Local, Word> = bitvec![];
	assert!(bv.is_empty());

	let bv: BitVec<Msb0, Word> = bitvec![Msb0];
	assert!(bv.is_empty());

	let bv: BitVec<Lsb0, Word> = bitvec![Lsb0];
	assert!(bv.is_empty());

	let bv: BitVec<Msb0, u8> = bitvec![Msb0, u8];
	assert!(bv.is_empty());

	let bv: BitVec<Lsb0, u8> = bitvec![Lsb0, u8];
	assert!(bv.is_empty());

	let bv: BitVec<Local, Word> = bitvec![1, 0, 1, 1];
	assert_eq!(bv.len(), 4);
	check(bv.as_bitslice());

	let bv: BitVec<Msb0, Word> = bitvec![Msb0; 1, 0, 1, 1];
	assert_eq!(bv.len(), 4);
	check(bv.as_bitslice());

	let bv: BitVec<Lsb0, Word> = bitvec![Lsb0; 1, 0, 1, 1];
	assert_eq!(bv.len(), 4);
	check(bv.as_bitslice());

	let bv: BitVec<Msb0, u8> = bitvec![Msb0, u8; 1, 0, 1, 1];
	assert_eq!(bv.len(), 4);
	check(bv.as_bitslice());

	let bv: BitVec<Lsb0, u8> = bitvec![Lsb0, u8; 1, 0, 1, 1];
	assert_eq!(bv.len(), 4);
	check(bv.as_bitslice());

	let bv: BitVec<Local, Word> = bitvec![1; 4];
	assert_eq!(bv.len(), 4);
	assert!(bv.all());

	let bv: BitVec<Msb0, Word> = bitvec![Msb0; 1; 4];
	assert_eq!(bv.len(), 4);
	assert!(bv.all());

	let bv: BitVec<Lsb0, Word> = bitvec![Lsb0; 1; 4];
	assert_eq!(bv.len(), 4);
	assert!(bv.all());

	let bv: BitVec<Msb0, u8> = bitvec![Msb0, u8; 1; 4];
	assert_eq!(bv.len(), 4);
	assert!(bv.all());

	let bv: BitVec<Lsb0, u8> = bitvec![Lsb0, u8; 1; 4];
	assert_eq!(bv.len(), 4);
	assert!(bv.all());
}

fn check<O, T>(slice: &BitSlice<O, T>)
where O: BitOrder, T: BitStore {
	for (bit, test) in slice.iter().zip(PATTERN.iter()) {
		assert_eq!(*bit, *test);
	}
}
