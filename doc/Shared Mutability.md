# Shared Mutable Memory Access

Machine instruction sets – certain embedded ISAs and x86_64’s BMIS
notwithstanding – do not offer the ability to access memory with bit-precision
granularity, and compilers similarly do not offer single-bit precision of memory
controls. These restrictions are, after all, why `bitvec` exists.

Rust has strict rules that a program must ensure that all typed locations in
memory have either any number of read-only references, or exactly one read/write
reference. A program that permits a typed location to be referenced by a
write-capable reference *and* any other reference, read-only or not, is
malformed.

`bitvec` obeys the spirit of this rule, in that it forbids constructing
`BitSlice` references which alias bits. However, because of the implementation
details of the Rust compiler and the machines on which it runs, `bitvec` does
produce aliased access to memory elements. The production of aliased `&mut`
references, even if they are not used in data-race conditions, is automatically
undefined behavior. As such, `bitvec` takes measures to ensure that it
appropriately marks shared access to mutating elements to satisfy the compiler.

## Memory Typing

`bitvec` uses the Rust fundamentals `u8`, `u16`, `u32`, and `u64` as the basis
types of the underlying memory, because the data structures use the alignment
and width of the underlying memory elements for its work. These fundamental
types, however, do not permit shared-mutable access.

`bitvec` constructors receive either a shared `&T` or unique `&mut T` reference
to memory, and then obey the mutability restrictions on that reference on all
future work. However, all access to memory must be mediated through a
shared-mutable type, in order to ensure that all access is correctly guarded.
There are two type families in the Rust core library that provide this access:
`Cell<T>`, and `AtomicU{8,16,32,64}`. These types are able to use shared
references `&_` (which are free to alias) for both read and write operations.

The `BitStore` trait is implemented only on the fundamental types, as that is
the type that users should provide to the constructors for use. It defines an
associated type which implements an internal trait, `BitAccess`.

`BitAccess` is implemented on either the `AtomicU{8,16,32,64}` types or the
`Cell<T: BitStore>`, depending on whether the `atomic` feature flag is set or
removed. When the `atomic` flag is disabled, `BitSlice` loses its `Send` and
`Sync` implementations so that references can never observe data races. When it
is enabled, all access uses the `Relaxed` ordering because it is impossible for
one thread to change bits that other threads observe, so the least constraint is
sufficient: the order of each atomic access does not matter, only that each
read/modify/write event is atomic in itself.

Access to the underlying always casts the region address to the shared-mutable
type before performing any offset computations and reference taking.

## Single-Threaded Builds

When `atomic` is turned off, `BitSlice` is disallowed to cross thread
boundaries. This means that shared-mutable access to the memory buffer is
mediated by the call stack, and since `BitSlice` disallows stale writes (you can
never read from memory, perform other work, then write the element back), the
buffer is kept consistent. Multiple `BitSlice` references may read the same
memory element, but they are always guaranteed to have sole access at any moment
in the instruction stream and will always observe the up-to-date value.

## Multi-Threaded Builds

When `atomic` is turned on, `BitSlice` is allowed to cross thread boundaries.
Access is always guaranteed to have uninterrupted read/modify/write cycles, and
the modifications are always guaranteed to affect only bits that cannot be
observed by other slice handles. Multiple references may operate on the same
memory element concurrently, and the processor will mediate full access between
them.

I would prefer to be able to use single-bit instructions without
synchronization, but until BMIS has intrinsics in the Rust core library, that
will not happen. RMW cycles are quick enough that element exclusion is not
likely to be a significant bottleneck.

Splitting a `u64` into 64 single-bit slices, putting each on a different thread,
and having each try to write its bit is the worst possible way to implement
parallel bitfield access, so, don’t do that.
