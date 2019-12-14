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
extern crate proc_macro as pm;
extern crate proc_macro2 as pm2;
extern crate proc_macro_hack;
extern crate quote;
extern crate syn;

use bitvec::prelude::{
	BitVec,
	Local,
	Lsb0,
	Msb0,
	Word,
};
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
pub fn bits(input: pm::TokenStream) -> pm::TokenStream {
	bits2(input.into()).unwrap_or_else(|err| err.to_compile_error()).into()
}

fn bits2(tokens: pm2::TokenStream) -> syn::Result<pm2::TokenStream> {
	let Args {
		r#mut,
		store,
		order,
		inner,
	} = syn::parse2(tokens)?;
	Ok(match inner {
		Buffer::Repeated(bit, tokens) => build_rep(r#mut, store, order, bit, tokens),
		Buffer::Sequence(bv) => build_seq(r#mut, store, order, bv),
	})
}

fn build_rep(
	r#mut: bool,
	store: Store,
	order: Order,
	bit: bool,
	tokens: pm2::TokenStream,
) -> pm2::TokenStream {
	let elt = if bit {
		quote!(::TRUE)
	}
	else {
		quote!(::FALSE)
	};
	let func_tokens = func_tokens(r#mut);
	let elt_tokens = iter::once(store.tokens()).chain(iter::once(elt));
	let order_tokens = order.tokens();
	let store_tokens = store.tokens();
	let out = quote! {{
		const BITS: usize = #tokens;

		&::bitvec::slice::BitSlice::<
			#order_tokens,
			#store_tokens,
		> #func_tokens (&[
			#( #elt_tokens )*
			; BITS / 8 + (BITS % 8 != 0) as usize
		])[.. BITS]
	}};
	out.into()
}

fn build_seq(
	r#mut: bool,
	store: Store,
	order: Order,
	bv: BitVec,
) -> pm2::TokenStream {
	let len = bv.len();
	let bits = bv.iter().copied();
	let func_tokens = func_tokens(r#mut);
	let order_tokens = order.tokens();
	let store_tokens = store.tokens();
	let buf_tokens = match store {
		Store::U8 => {
			let buf = match order {
				Order::Local => bits.collect::<BitVec<Local, u8>>()
					.into_boxed_slice(),
				Order::Lsb0 => bits.collect::<BitVec<Lsb0, u8>>()
					.into_boxed_slice(),
				Order::Msb0 => bits.collect::<BitVec<Msb0, u8>>()
					.into_boxed_slice(),
			};
			quote!(#( #buf ),*)
		},
		Store::U16 => {
			let buf = match order {
				Order::Local => bits.collect::<BitVec<Local, u16>>()
					.into_boxed_slice(),
				Order::Lsb0 => bits.collect::<BitVec<Lsb0, u16>>()
					.into_boxed_slice(),
				Order::Msb0 => bits.collect::<BitVec<Msb0, u16>>()
					.into_boxed_slice(),
			};
			quote!(#( #buf ),*)
		},
		Store::U32 => {
			let buf = match order {
				Order::Local => bits.collect::<BitVec<Local, u32>>()
					.into_boxed_slice(),
				Order::Lsb0 => bits.collect::<BitVec<Lsb0, u32>>()
					.into_boxed_slice(),
				Order::Msb0 => bits.collect::<BitVec<Msb0, u32>>()
					.into_boxed_slice(),
			};
			quote!(#( #buf ),*)
		},
		Store::U64 => {
			let buf = match order {
				Order::Local => bits.collect::<BitVec<Local, u64>>()
					.into_boxed_slice(),
				Order::Lsb0 => bits.collect::<BitVec<Lsb0, u64>>()
					.into_boxed_slice(),
				Order::Msb0 => bits.collect::<BitVec<Msb0, u64>>()
					.into_boxed_slice(),
			};
			quote!(#( #buf ),*)
		},
		Store::Word => {
			let buf = match order {
				Order::Local => bits.collect::<BitVec<Local, Word>>()
					.into_boxed_slice(),
				Order::Lsb0 => bits.collect::<BitVec<Lsb0, Word>>()
					.into_boxed_slice(),
				Order::Msb0 => bits.collect::<BitVec<Msb0, Word>>()
					.into_boxed_slice(),
			};
			quote!(#( #buf ),*)
		},
	};
	quote! {
		&::bitvec::slice::BitSlice::<
			#order_tokens,
			#store_tokens,
		> #func_tokens (&[#buf_tokens])[.. #len]
	}
}

fn func_tokens(is_mut: bool) -> pm2::TokenStream {
	if is_mut {
		quote!(::from_slice_mut)
	}
	else {
		quote!(::from_slice)
	}
}

#[derive(Clone, Debug, Default)]
struct Args {
	r#mut: bool,
	order: Order,
	store: Store,
	inner: Buffer,
}

impl Parse for Args {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		let mut out = Self::default();
		//  The first token may be the keyword `mut`
		if input.peek(Token![mut]) {
			out.r#mut = true;
			input.parse::<Token![mut]>()?;
		}
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
		out.inner = input.parse().unwrap_or_default();
		Ok(out)
	}
}

#[derive(Clone, Copy, Debug)]
enum Order {
	Local,
	Lsb0,
	Msb0,
}

impl Order {
	fn tokens(self) -> pm2::TokenStream {
		match self {
			Order::Local => quote!(::bitvec::order::Local),
			Order::Lsb0 => quote!(::bitvec::order::Lsb0),
			Order::Msb0 => quote!(::bitvec::order::Msb0),
		}
	}
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
			_ => return Err(syn::Error::new(
				ident.span(),
				"Ordering type must be one of `Local`, `Lsb0`, or `Msb0`",
			)),
		})
	}
}

#[derive(Clone, Copy, Debug)]
enum Store {
	U8,
	U16,
	U32,
	U64,
	Word,
}

impl Store {
	fn tokens(self) -> pm2::TokenStream {
		match self {
			Store::U8 => quote!(u8),
			Store::U16 => quote!(u16),
			Store::U32 => quote!(u32),
			Store::U64 => quote!(u64),
			Store::Word => quote!(::bitvec::store::Word),
		}
	}
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

#[derive(Clone, Debug)]
enum Buffer {
	Repeated(bool, pm2::TokenStream),
	Sequence(BitVec),
}

impl Default for Buffer {
	fn default() -> Self {
		Buffer::Sequence(BitVec::new())
	}
}

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
			let tokens = input.cursor().token_stream();
			//  Drain the input stream
			let _ = input.step(|c| {
				let mut cur = *c;
				while let Some((_, rest)) = cur.token_tree() {
					cur = rest;
				}
				Ok(((), cur))
			})?;
			return if input.is_empty() {
				Ok(Buffer::Repeated(first != 0, tokens))
			}
			else {
				Err(input.error(
					"The bit repetition syntax `$bit ; $rep` requires that \
					`$rep` be a single expression, with no further tokens in \
					the macro call",
				))
			}
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
		Ok(Buffer::Sequence(seq))
	}
}
