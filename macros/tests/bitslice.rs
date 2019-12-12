/*! Check macro syntax and production

This test checks that the syntaxes the macro is expected to provide evaluate to
the correct types and values.
!*/

use bitvec::prelude::*;
use bitvec_macros::bits;

static PATTERN: &[bool] = &[true, false, true, true];

#[test]
fn check_bitslice_proc_macro() {
	let bs: &'static BitSlice<Local, Word> = bits![];
	assert!(bs.is_empty());

	let bs: &'static BitSlice<Msb0, Word> = bits![Msb0];
	assert!(bs.is_empty());

	let bs: &'static BitSlice<Lsb0, Word> = bits![Lsb0];
	assert!(bs.is_empty());

	let bs: &'static BitSlice<Msb0, u8> = bits![Msb0, u8];
	assert_eq!(bs.is_empty());

	let bs: &'static BitSlice<Lsb0, u8> = bits![Lsb0, u8];
	assert_eq!(bs.is_empty());

	let bs: &'static BitSlice<Local, Word> = bits![1, 0, 1, 1];
	assert_eq!(bs.len(), 4);
	check(bs);

	let bs: &'static BitSlice<Msb0, Word> = bits![Msb0; 1, 0, 1, 1];
	assert_eq!(bs.len(), 4);
	check(bs);

	let bs: &'static BitSlice<Lsb0, Word> = bits![Lsb0; 1, 0, 1, 1];
	assert_eq!(bs.len(), 4);
	check(bs);

	let bs: &'static BitSlice<Msb0, u8> = bits![Msb0, u8; 1, 0, 1, 1];
	assert_eq!(bs.len(), 4);
	check(bs);

	let bs: &'static BitSlice<Lsb0, u8> = bits![Lsb0, u8; 1, 0, 1, 1];
	assert_eq!(bs.len(), 4);
	check(bs);

	let bs: &'static BitSlice<Local, Word> = bits![1; 4];
	assert_eq!(bs.len(), 4);
	assert!(bs.all());

	let bs: &'static BitSlice<Msb0, Word> = bits![Msb0; 1; 4];
	assert_eq!(bs.len(), 4);
	assert!(bs.all());

	let bs: &'static BitSlice<Lsb0, Word> = bits![Lsb0; 1; 4];
	assert_eq!(bs.len(), 4);
	assert!(bs.all());

	let bs: &'static BitSlice<Msb0, u8> = bits![Msb0, u8; 1; 4];
	assert_eq!(bs.len(), 4);
	assert!(bs.all());

	let bs: &'static BitSlice<Lsb0, u8> = bits![Lsb0, u8; 1; 4];
	assert_eq!(bs.len(), 4);
	assert!(bs.all());
}

fn check<O, T>(slice: &BitSlice<O, T>)
where O: BitOrder, T: BitStore {
	for (bit, test) in slice.iter().zip(PATTERN.iter()) {
		assert_eq!(*bit, *test);
	}
}
