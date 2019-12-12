/*! Constructor macros for `bitvec` types.

!*/

extern crate bitvec;
extern crate proc_macro;
extern crate proc_macro_hack;
extern crate quote;
extern crate syn;

use bitvec::prelude::*;
use proc_macro::TokenStream;
use proc_macro_hack::proc_macro_hack;
use quote::quote;
use std::iter;
use syn::{
	Ident,
	LitInt,
	Token,
	parse::{
		Parse,
		ParseStream,
	},
};

#[proc_macro_hack]
pub fn bits(input: TokenStream) -> TokenStream {
	let Args {
		store,
		order,
		buffer,
	} = syn::parse_macro_input!(input as Args);
	let Buffer(bv) = buffer;
	let len = bv.len();
	let bits = bv.iter().copied();
	match order {
		Order::Local => match store {
			Store::U8 => {
				let bv: BitVec<Local, u8> = bits.collect();
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Local,
						u8,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
			Store::U16 => {
				let bv: BitVec<Local, u16> = bits.collect();
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Local,
						u16,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
			Store::U32 => {
				let bv: BitVec<Local, u32> = bits.collect();
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Local,
						u32,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
			Store::U64 => {
				let bv: BitVec<Local, u64> = bits.collect();
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Local,
						u64,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
			Store::Word => {
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Local,
						::bitvec::store::Word,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
		},
		Order::Lsb0 => match store {
			Store::U8 => {
				let bv: BitVec<Lsb0, u8> = bits.collect();
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Lsb0,
						u8,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
				},
			Store::U16 => {
				let bv: BitVec<Lsb0, u16> = bits.collect();
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Lsb0,
						u16,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
			Store::U32 => {
				let bv: BitVec<Lsb0, u32> = bits.collect();
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Lsb0,
						u32,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
			Store::U64 => {
				let bv: BitVec<Lsb0, u64> = bits.collect();
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Lsb0,
						u64,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
			Store::Word => {
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Lsb0,
						::bitvec::store::Word,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
		},
		Order::Msb0 => match store {
			Store::U8 => {
				let bv: BitVec<Msb0, u8> = bits.collect();
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Msb0,
						u8,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
			Store::U16 => {
				let bv: BitVec<Msb0, u16> = bits.collect();
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Msb0,
						u16,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
			Store::U32 => {
				let bv: BitVec<Msb0, u32> = bits.collect();
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Msb0,
						u32,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
			Store::U64 => {
				let bv: BitVec<Msb0, u64> = bits.collect();
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Msb0,
						u64,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
			Store::Word => {
				let buf = bv.as_slice();
				quote! {
					&::bitvec::slice::BitSlice::<
						::bitvec::order::Msb0,
						::bitvec::store::Word,
					>::from_slice(&[#( #buf ),*])[.. #len]
				}
			},
		},
		Order::Unknown(ident) => syn::Error::new(
			ident.span(),
			"`BitOrder` implementors not provided by `bitvec` cannot be used \
			in `bits!` construction of `&BitSlice`s",
		).to_compile_error()
	}.into()
}

#[proc_macro_hack]
pub fn bitvec(input: TokenStream) -> TokenStream {
	let Args {
		order,
		store,
		buffer,
	} = syn::parse_macro_input!(input as Args);
	let Buffer(bv) = buffer;
	let len = bv.len();
	let bits = bv.iter().copied();
	match order {
		Order::Local => match store {
			Store::U8 => {
				let bv: BitVec<Local, u8> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Local,
						u8,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
			Store::U16 => {
				let bv: BitVec<Local, u16> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Local,
						u16,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
			Store::U32 => {
				let bv: BitVec<Local, u32> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Local,
						u32,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
			Store::U64 => {
				let bv: BitVec<Local, u64> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Local,
						u64,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
			Store::Word => {
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Local,
						::bitvec::store::Word,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
		}
		Order::Lsb0 => match store {
			Store::U8 => {
				let bv: BitVec<Lsb0, u8> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Lsb0,
						u8,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
			Store::U16 => {
				let bv: BitVec<Lsb0, u16> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Lsb0,
						u16,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
			Store::U32 => {
				let bv: BitVec<Lsb0, u32> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Lsb0,
						u32,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
			Store::U64 => {
				let bv: BitVec<Lsb0, u64> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Lsb0,
						u64,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
			Store::Word => {
				let bv: BitVec<Lsb0, Word> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Lsb0,
						::bitvec::store::Word,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
		}
		Order::Msb0 => match store {
			Store::U8 => {
				let bv: BitVec<Msb0, u8> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Msb0,
						u8,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
			Store::U16 => {
				let bv: BitVec<Msb0, u16> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Msb0,
						u16,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
			Store::U32 => {
				let bv: BitVec<Msb0, u32> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Msb0,
						u32,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
			Store::U64 => {
				let bv: BitVec<Msb0, u64> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Msb0,
						u64,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
			Store::Word => {
				let bv: BitVec<Msb0, Word> = bits.collect();
				let buf = bv.as_slice();
				quote! {{
					let mut out = ::bitvec::vec::BitVec::<
						::bitvec::order::Msb0,
						::bitvec::store::Word,
					>::from_slice(&[#( #buf ),*]);
					out.truncate(#len);
					out
				}}
			},
		}
		Order::Unknown(ident) => {
			match store {
				Store::U8 => {
					let bv: BitVec<Local, u8> = bits.collect();
					let buf = bv.as_slice();
					quote! {
						::bitvec::slice::BitSlice::<
							::bitvec::order::Local,
							u8,
						>::from_slice(&[#( #buf ),*])[.. #len]
							.iter()
							.copied()
							.collect::<::bitvec::vec::BitVec::<
								#ident,
								u8,
							>>()
					}
				},
				Store::U16 => {
					let bv: BitVec<Local, u16> = bits.collect();
					let buf = bv.as_slice();
					quote! {
						::bitvec::slice::BitSlice::<
							::bitvec::order::Local,
							u16,
						>::from_slice(&[#( #buf ),*])[.. #len]
							.iter()
							.copied()
							.collect::<::bitvec::vec::BitVec::<
								#ident,
								u16,
							>>()
					}
				},
				Store::U32 => {
					let bv: BitVec<Local, u32> = bits.collect();
					let buf = bv.as_slice();
					quote! {
						::bitvec::slice::BitSlice::<
							::bitvec::order::Local,
							u32,
						>::from_slice(&[#( #buf ),*])[.. #len]
							.iter()
							.copied()
							.collect::<::bitvec::vec::BitVec::<
								#ident,
								u32,
							>>()
					}
				},
				Store::U64 => {
					let bv: BitVec<Local, u64> = bits.collect();
					let buf = bv.as_slice();
					quote! {
						::bitvec::slice::BitSlice::<
							::bitvec::order::Local,
							u64,
						>::from_slice(&[#( #buf ),*])[.. #len]
							.iter()
							.copied()
							.collect::<::bitvec::vec::BitVec::<
								#ident,
								u64,
							>>()
					}
				},
				Store::Word => {
					let bv: BitVec<Local, Word> = bits.collect();
					let buf = bv.as_slice();
					quote! {
						::bitvec::slice::BitSlice::<
							::bitvec::order::Local,
							::bitvec::store::Word,
						>::from_slice(&[#( #buf ),*])[.. #len]
							.iter()
							.copied()
							.collect::<::bitvec::vec::BitVec::<
								#ident,
								::bitvec::store::Word,
							>>()
					}
				},
			}
		},
	}.into()
}

#[proc_macro_hack]
pub fn bitbox(input: TokenStream) -> TokenStream {
	let mut tokens = bitvec(input);
	tokens.extend(TokenStream::from(quote!( .into_boxed_bitslice() )));
	tokens
}

#[derive(Clone, Debug, Default)]
struct Args {
	order: Order,
	store: Store,
	buffer: Buffer,
}

impl Parse for Args {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		let mut out = Self::default();
		//  The first identifier is the `Order`
		if input.peek(Ident) {
			out.order = input.parse()?;
			//  If it is followed by a `, Ident`, that is the `Storage`
			if input.peek(Token![,]) {
				input.parse::<Token![,]>()?;
				out.store = input.parse()?;
			}
			//  If tokens remain after the types, they must begin with a `;`
			if input.peek(Token![;]) {
				input.parse::<Token![;]>()?;
			}
		}
		out.buffer = input.parse().unwrap_or_default();
		Ok(out)
	}
}

#[derive(Clone, Debug)]
enum Order {
	Local,
	Lsb0,
	Msb0,
	Unknown(Ident),
}

impl Default for Order {
	fn default() -> Self {
		Order::Local
	}
}

/** Attempt to parse an `Order` token set from the input.

An `Order` is found when an `Ident(_)` token is followed by a
`Token![,] Ident(_) Token![;]` sequence or a `Token![;]` sequence. It occurs,
optionally, at the beginning of the input argument sequence.
**/
impl Parse for Order {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		let ident = input.parse::<Ident>()?;
		Ok(match ident.to_string().as_str() {
			"Local" => Order::Local,
			"Lsb0" => Order::Lsb0,
			"Msb0" => Order::Msb0,
			_ => Order::Unknown(ident),
		})
	}
}

#[derive(Clone, Debug)]
enum Store {
	U8,
	U16,
	U32,
	U64,
	Word,
}

impl Default for Store {
	fn default() -> Self {
		Store::Word
	}
}

impl Parse for Store {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		let ident = input.parse::<Ident>()?;
		Ok(match ident.to_string().as_str() {
			"u8" => Store::U8,
			"u16" => Store::U16,
			"u32" => Store::U32,
			"u64" => Store::U64,
			"Word" => Store::Word,
			_ => return Err(
				input.error(
					"Storage type must be `Word` or one of the Rust unsigned \
					integer types",
				),
			),
		})
	}
}

#[derive(Clone, Debug, Default)]
struct Buffer(BitVec<Local, Word>);

impl Parse for Buffer {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		if input.is_empty() {
			return Ok(Self::default());
		}
		let first = input.parse::<LitInt>()?.base10_parse::<i32>()?;
		if input.peek(Token![;]) {
			input.parse::<Token![;]>()?;
			let second = input.parse::<LitInt>()?.base10_parse()?;
			return Ok(Buffer(iter::repeat(first != 0).take(second).collect()));
		}
		let mut seq = BitVec::with_capacity(1);
		seq.push(first != 0);
		while !input.is_empty() {
			input.parse::<Token![,]>()?;
			seq.push(input.parse::<LitInt>()?.base10_parse::<i32>()? != 0);
		}
		if input.peek(Token![,]) {
			input.parse::<Token![,]>()?;
		}
		Ok(Buffer(seq))
	}
}
