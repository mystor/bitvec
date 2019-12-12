/*!

!*/

/** Constructor macro for `&'static [mut] BitSlice` objects.

This macro runs at compile-time to create `BitSlice` regions that are stored in
your library’s static data section.
**/
#[proc_macro_hack::proc_macro_hack]
pub use bitvec_macros_impl::bits;

/** Constructor macro for `BitVec` objects.

This macro runs at compile-time to create `BitSlice` regions that are stored in
your library’s static data section, and at runtime can be copied into the heap
and used immediately, with no other initialization cost required.
**/
#[proc_macro_hack::proc_macro_hack]
pub use bitvec_macros_impl::bitvec;

/** Constructor macro for `BitBox` objects.

This macro runs at compile-time to create `BitSlice` regions that are stored in
your library’s static data section, and at runtime can be copied into the heap
and used immediately, with no other initialization cost required.
**/
#[proc_macro_hack::proc_macro_hack]
pub use bitvec_macros_impl::bitbox;
