/*! Compile-time construction of `BitSlice` buffers.

This crate exports a procedural macro which runs during compilation in order to
produce well-formed `BitSlice` regions. The call-site of this macro then only
constructs the `&/mut BitSlice` reference descriptor over the region.

This macro can only be used with the `BitOrder` implementations provided by
`bitvec`.
!*/

use proc_macro_hack::proc_macro_hack;

/** Constructor macro for `&'static [mut] BitSlice` objects.

This macro runs at compile-time to create `BitSlice` regions that are stored in
your project’s static data section.
**/
#[proc_macro_hack]
pub use bitvec_macros_impl::bits;
