# Bit Patterns

This document describes how bit slices describe memory, and how their pointer
structures are composed.

## Cursor Addressing

Before getting into the details of how this crate constructs pointers to
describe a memory span, we must first cover how memory viewed at bit resolution
works. This crate uses two traits, `Cursor` and `BitStore`, to select a specific
bit ordering pattern for memory. You will need to select the combination of
these two traits that best works for your target machine architecture and use
case.

These tables display the traversal path of each cursor and type pair on both
big- and little- **byte** endian machines. Starting at index `[0]` of a
`BitSlice` and moving up to index `[63]` moves from position `0` in the tables,
following the arrows and jumping from odd numbers to the consecutive even
numbers until reaching position `F`.

The byte and bit ordering follows the common CS conventions that memory byte
addresses increase to the right, but bit positions in a byte increase to the
left.

This table displays the traversal orders on a little-endian machine:

```text
byte  | 00000000 11111111 22222222 33333333 44444444 55555555 66666666 77777777
bit   | 76543210 76543210 76543210 76543210 76543210 76543210 76543210 76543210
------+------------------------------------------------------------------------
LEu__ | 1 <--- 0 3 <--- 2 5 <--- 4 7 <--- 6 9 <--- 8 B <--- A D <--- C F <--- E
BEu64 | E ---> F C ---> D A ---> B 8 ---> 9 6 ---> 7 4 ---> 5 2 ---> 3 0 ---> 1
BEu32 | 6 ---> 7 4 ---> 5 2 ---> 3 0 ---> 1 E ---> F C ---> D A ---> B 8 ---> 9
BEu16 | 2 ---> 3 0 ---> 1 6 ---> 7 4 ---> 5 A ---> B 8 ---> 9 E ---> F C ---> D
BEu8  | 0 ---> 1 2 ---> 3 4 ---> 5 6 ---> 7 8 ---> 9 A ---> B C ---> D E ---> F
```

And this table displays the traversal orders on a big-endian machine:

```text
byte  | 00000000 11111111 22222222 33333333 44444444 55555555 66666666 77777777
bit   | 76543210 76543210 76543210 76543210 76543210 76543210 76543210 76543210
------+------------------------------------------------------------------------
BEu__ | 0 ---> 1 2 ---> 3 4 ---> 5 6 ---> 7 8 ---> 9 A ---> B C ---> D E ---> F
LEu64 | F <--- E D <--- C B <--- A 9 <--- 8 7 <--- 6 5 <--- 4 3 <--- 2 1 <--- 0
LEu32 | 7 <--- 6 5 <--- 4 3 <--- 2 1 <--- 0 F <--- E D <--- C B <--- A 9 <--- 8
LEu16 | 3 <--- 2 1 <--- 0 7 <--- 6 5 <--- 4 B <--- A 9 <--- 8 F <--- E D <--- C
LEu8  | 1 <--- 0 3 <--- 2 5 <--- 4 7 <--- 6 9 <--- 8 B <--- A D <--- C F <--- E
```

There are two behaviors of note here:

1. On a machine of some endianness, the bit cursor of that same endianness will
    always have exactly one behavior, regardless of the underlying fundamental
    type chosen.

1. Any cursor, when applied to `u8`, behaves identically across all machine
    architectures.

## Pointer Representation

The bit pointer type `BitPtr<T>` is the fundamental component of the library. It
is a slice pointer with the capability to refine its concept of start and span
to bit-level granularity, allowing it to “point to” a single bit and count how
many bits after the pointed-to bit are included in the slice span.

The naïve implementation of such a pointer might be

```rust
struct BitPtr<T> {
  //  standard slice
  eltptr: *const T,
  elts: usize,
  //  bit cursors
  first_bit: u8,
  last_bit: u8,
}
```

but this is three words wide, whereas a standard slice pointer is two. It also
has many invalid states, as indices into a slice of any type are traditionally
`usize`, and there only `usize::max_value() / 8` bytes in a fully widened bit
slice.

The next step might be for the struct to count bits, instead of elements, and
compute how many elements are in its domain based on the first live bit in the
slice and the count of all live bits. This eliminates the `last_bit` field,
folding it into `elts` to become `bits`,

```rust
struct BitPtr<T> {
  ptr: *const T,
  bits: usize,
  first_bit: u8,
}
```

but the width problem remains.

The (far too) clever solution is to fold the first-bit counter into the pointer
and length fields. This was not a problem with the last-bit counter, because
doing so brought the `bits` counter to match the indexing `usize` domain rather
than being far too large for it. However, there is not space to hold the
first-bit counter inside the other two elements!

There are two trade-offs here:

1. Preserve range capacity, and force bit regions to align to byte boundaries.
   This permits any slice that exists to store the full range of indices, but
   restricts the possible space of slices that can exist to one-eighth of the
   memory space.
1. Reduce range capacity, and permit bit regions to have any bit alignment. This
   permits a slice to begin anywhere, but restricts the slice maximum size to
   one-eighth of the index space.

Option two is the better choice: how often do you really need to access more
than 2<sup>29</sup> bits on a 32-bit system, or 2<sup>61</sup> on a 64-bit
system? Much less often than you need to divide a bit region at any arbitrary
point.

This means that the pointer will need to be able to have three levels of
granularity. It must point to:

- the first memory element (`u8` through `u64`) of the region
- the first byte within that element
- the first bit within that byte

It so happens that Rust requires that each fundamental be aligned to its width;
that is, an `n`-byte fundamental can only have a starting address that is evenly
divided by `n`.

> This is not *strictly* true; `u64` has alignment of 4 on 32-bit systems. As
> such, `u64` is disallowed for use as the backing store on 32-bit targets. The
> choice of backing element does not affect the bit capacity, only details of
> element access, so this is fine.

Thus, there are always enough unused element-address bits in the least
significant edge of a pointer to any element to select a single byte within the
element. This diagram may help. It shows a span of sixteen bytes in memory, and
all the acceptable placements for fundamental elements in that span.

> ```text
> u64 | [0---------------------][8---------------------]
> u32 | [0---------][4---------][8---------][c---------]
> u16 | [0---][2---][4---][6---][8---][a---][c---][e---]
>  u8 | [0][1][2][3][4][5][6][7][8][9][a][b][c][d][e][f]
> ```

We still need three more bits, to select a starting bit within the starting
byte. These three bits are placed in the length field, rather than the address
field, truncating range by a factor of eight.

> The astute reader who knows far more than is healthy about `x86_64` pointer
> representation may choose this moment to say, “what about the unused high bits
> of a pointer; there are 16 on most processors out today, and 7 on the
> processors of tomorrow, and you only need three”, to which I respond that this
> trick does not work at all on 32-bit systems which the library still supports,
> and that other environments may want to use those bits but there is no need
> for `bitvec` to do so.

The end result of this packing scheme is that bit span pointers have three
logical fields, separated over two CPU words, represented as follows. Rust does
not have bitfield syntax, so I have elected to use C++ syntax as a near cousin.
The ranges in comments are the range of field widths, which may vary by
underlying referent type.

```cpp
template <typename T>
struct BitPtr {
  size_t   ptr_head : __builtin_ctzll(alignof(T)); // 0 ..= 3
  T const* ptr_addr : sizeof(uintptr_t) * 8
                    - __builtin_ctzll(alignof(T)); // 64/32 ..= 61/29

  size_t len_head : 3;
  size_t len_bits : sizeof(size_t) * 8 - 3; // 61/29
};
```

C++ treats bitfields as starting from the significance edge of the element that
matches the byte order of the target. That is, on a little-endian machine,
bitfields start from the least significant edge and move more significant, while
on a big-endian machine, bitfields start from the most significant edge and move
less significant.

The structure above places a byte-selector in the low zero to three bits of a
pointer, then an element pointer in the remaining high bits of a CPU word. It
places a bit-selector in the low three bits of the length counter, then uses the
remaining high bits of the CPU word to count how many bits in the span are live,
starting at the bit selected by the 35- or 67- bit pointer.

## Value Patterns

### Null Value

The null value, `ptr: 0, len: 0` is reserved as an invalid value of `BitPtr<T>`
so that it may be used as `Option<BitPtr<T>>::None`.

### Empty Slices

All pointers whose `bits` counter is zero are considered empty. Empty slices are
not constrained in their `data` or `head` members, but the canonical empty slice
value uses `NonNull::<T>::dangling()` and `0`, respectively.

### Uninhabited Slices

The subset of empty slices with non-dangling `data` members are considered
uninhabited. All pointer structures retain their `data` value for their
lifetime; this allows owning supertypes like `BitBox` or `BitVec` to allocate a
region of storage without immediately beginning to populate it, and allows a
slice which has been shrunk to zero bits to still be considered a subset (by
address) of its parent slice.

### Inhabited Slices

All structures with a non-zero `bits` field are inhabited. The `bits` field may
range from zero (empty/uninhabited) to `!0` (fully extended). Inhabited slices
are required to have a valid pointer in the `data` field, and may have any value
in the `head` field.

## Memory Regions

A `BitPtr<T>` is translated to a `[T]` memory region using the `domain` module.
This module contains all the logic for determining which memory elements under a
`BitPtr<T>` are partially or fully inhabited by that bit slice.
