/*! Constructor macros for `bitvec` types.

!*/

extern crate bitvec;
extern crate proc_macro;
extern crate proc_macro_hack;
extern crate quote;
extern crate syn;

use proc_macro::TokenStream;
use proc_macro_hack::proc_macro_hack;

#[proc_macro_hack]
pub fn bits(input: TokenStream) -> TokenStream {
	unimplemented!("Tracking issue: `bitvec/25`")
}

#[proc_macro_hack]
pub fn bitvec(input: TokenStream) -> TokenStream {
	unimplemented!("Tracking issue: `bitvec/25`")
}

#[proc_macro_hack]
pub fn bitbox(input: TokenStream) -> TokenStream {
	unimplemented!("Tracking issue: `bitvec/25`")
}
