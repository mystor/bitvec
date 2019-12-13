/*! Constructor macros for `bitvec` types.

This file provides the implementation of the `bits!`, `bitvec!`, and `bitbox!`
constructor macros. These macros compute `BitSlice<O, T>` buffer contents and
inject the buffers into the artifact’s static memory. Handles to those buffers
are constructed at runtime, but this construction is very fast since the buffers
are already initialized.

The grammar for these macros is:

```text
[ $order [ , $store ] ]; [ ( ( 1 | 0 ),* [ , ] ) | ( ( 1 | 0 ) ; $num ) ]
```

If the first token in the call is an *identifier*, then it must be usable as a
`BitOrder` type parameter. `bits!` has the special requirement that this must
be one of the exact identifiers `Msb0`, `Lsb0`, or `Local` in order to produce a
`&BitSlice` immediate value. `bitvec!` and `bitbox!` are able to take any
identifier, as long as it implements `BitOrder`.

If the first identifier is followed by a comma, it must also be followed by a
second identifier. The second identifier **must** be one of `u8`, `u16`, `u32`,
`u64` (only when compiling both *on* a 64-bit host and *for* a 64-bit target),
or `Local`. `Local` is valid only when the host and target systems have the same
CPU pointer width.

If both this header and a data body exist, they must be separated by a
semicolon. If either section (type header, data body) are absent, the semicolon
is not required.

The data body must consist of a sequence of zero or more integer (`i32`
specifically) literals, inter-punctuated by commas. Trailing commas are valid.
Any non-`i32` literal is invalid. These integers are not *required* to be
constrained to `0` and `1`; they will be cast to `bool` by testing `LIT != 0`.

Alternatively, the data body must consist of one integer literal, a semicolon,
and one `usize` literal.

As a summary, the following are valid call grammars:

- `[]`: Empty slice, `<Local, Word>` types

- `[ $ord:ident $( ; )? ]`: Empty slice, `<$ord, Word>` types
- `[ $ord:ident , $typ:ident $( ; )? ]`: Empty slice, `<$ord, $typ>` types

- `[ $( $bit ),* ]` and `[ $( $bit ,)* ]`: Slice with data, `<Local, Word>`
  types
- `[ $ord:ident ; $( $bit ),* ]` and `[ $ord:ident ; $( $bit ,)* ]`: Slice with
  data, `<$ord, Word>` types
- `[ $ord:ident , $typ:ident ; $( $bit ),* ]` and
  `[ $ord:ident , $typ:ident ; $( $bit ,)* ]`: Slice witd data, `<$ord, $typ>`
  types

- `[ $bit:literal ; $rep:literal ]`: Slice of `$rep` counts of `$bit`;
  `<Local, Word>` types
- `[ $ord:ident ; $bit:literal ; $rep:literal ]`: Slice of `$rep` counts of
  `$bit`; `<$ord, Word>` types
- `[ $ord:ident , $typ:ident ; $bit:literal ; $rep:literal ]`: Slice of `$rep`
  counts of `$bit`; `<$ord, $typ>` types
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

/** Produces a `&'static BitSlice<O, T>` reference.

Currently, `&'static mut` production is not supported. This is a future work
item.

If present, the ordering type *must* be one of the types exported by `bitvec`,
without its name changed.

This macro computes the correct buffer values, then tokenizes them and places
them as numeric literals in the output `TokenStream`. This ensures that byte
endianness will match for the target, even if the target system does not match
the host.
**/
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
				let bv: BitVec<Lsb0, u64> = bits.collect();
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
				let bv: BitVec<Msb0, Word> = bits.collect();
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

/** Produces a `BitVec` object.

This macro computes the correct buffer values, then tokenizes them as `BitSlice`
does. If the ordering type is one of `bitvec`’s exports, then the buffer will be
usable as-is; if it is unknown, then the produced `TokenStream` will cause the
stored buffer to be reördered upon evaluation. If the type is known, then the
`TokenStream` will cause the buffer to be loaded into the heap, and then be
immediately ready as a `BitVec`.
**/
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

/// Forwards the arguments to `bitvec!`, then appends `.into_boxed_bitslice()`
/// to the resulting `TokenStream`.
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
			if !input.is_empty() {
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
			_ => return Err(syn::Error::new(
				ident.span(),
				"Storage type must be `Word` or one of the Rust unsigned \
				integer types",
			)),
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
		let look = input.lookahead1();
		let first = if look.peek(LitInt) {
			input.parse::<LitInt>()?.base10_parse::<i32>()?
		}
		else {
			return Err(look.error());
		};
		//  `; LitInt` is the repetition syntax
		if input.peek(Token![;]) {
			input.parse::<Token![;]>()?;
			let second = input.parse::<LitInt>()?.base10_parse()?;
			return Ok(Buffer(iter::repeat(first != 0).take(second).collect()));
		}
		//  Otherwise, this is the sequence syntax
		let mut seq = BitVec::with_capacity(1);
		seq.push(first != 0);
		//  Collect `, LitInt`
		while input.peek(Token![,]) {
			//  Skip the `,` token
			input.parse::<Token![,]>()?;
			//  If the input is now empty (trailing `,`), exit the loop
			if input.is_empty() {
				break;
			}
			//  If the input is non-empty, it must contain an integer literal.
			seq.push(input.parse::<LitInt>()?.base10_parse::<i32>()? != 0);
		}
		Ok(Buffer(seq))
	}
}
