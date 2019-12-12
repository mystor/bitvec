# `bitvec_macros_impl`

This crate provides the implementations of the proc-macros exported by the
`bitvec` project.

Rust currently does not allow procedural macros to be used in expression
position. In order to circumvent this, `bitvec` uses the `proc-macro-hack` crate
to produce `macro_rules!`-style macros which evaluate to the result of the
procedural macros.

This requires two crates, rather than one: the current crate provides the
proc-macro implementations, and the parent crate reëxports them as
expression-position `macro_rules!` macros.
