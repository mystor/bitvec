# `bitvec_macros`

This crate exports constructor macros `bitvec!` and `bitbox!` which you can use
to create `BitVec` and `BitBox` structures at compile-time.

This crate will be versioned synchronously with `bitvec`. Because the macros
depend on `bitvec` in order to construct their output values, the macros cannot
themselves be reëxported in the `bitvec` façade. If you want to use these
macros, you will need to depend on both `bitvec` and `bitvec_macros`.

## Usage

```toml
# Cargo.toml

[dependencies]
bitvec = "0.17"
bitvec_macros = "0.17"
```

```rust
//  src/lib.rs

use bitvec::prelude::*;
use bitvec_macros::*;

let mut bv = bitvec![Msb0, u8; 0, 0, 1, 0, 1, 0, 1, 1];
assert_eq!(bv.as_slice()[0], 0b0010_1011);
```
