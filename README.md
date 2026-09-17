# Transmog

Transmog provides *verified* fixed-width data representations and compact storage for Lean 4 data types.
At its core, the `transmog` DSL describes how Lean values map to unsigned integer fields and bit slices,
and `derive_layout` constructs byte layouts with round-trip proofs.
`CompactArray` is a drop-in replacement for the Stdlib `Array`, with values stored in a contiguous
`ByteArray` using those layouts.

The library includes little-endian scalar operations for `ByteArray`, bit manipulation
lemmas, and compact arrays with indexing, updates, folds, and standard Lean iterators.

## Build and test

Install Lean through [elan](https://github.com/leanprover/elan) and make `clang++`
available on your `PATH`. The Lean version is pinned in [lean-toolchain](lean-toolchain).
The optional Nix development shell supplies elan and Clang.

```sh
lake build
lake lint
lake test
```

The tests under [TransmogTest/](TransmogTest/) are organised by feature, one module each: the
scalar bit operations, the little-endian byte operations, `CompactArray`, the casts, the proof
automation, the `transmog` command (`Repr/`), the combined forms `transmog enum` and
`transmog struct` (`Decl.lean`), the public names and the DSL words (`Names.lean`), the layout
combinators, algorithm and `derive_layout` (`Layout/`), and the word-backed runtime
representation (`RuntimeRepr/`).  Each module pins the generated declarations, the kernel-computed values, the diagnostics and
the axioms of its feature.  The code of this file lives, with its outputs pinned, in
[Examples/](Examples/).  `lake test` builds the tests and the examples with warnings as errors,
runs the native executable, checks the C generated for the word-backed probes, and builds and
runs the downstream package under [tests/downstream](tests/downstream), which covers both
compiled execution and `#eval`.

GitHub Actions runs the build and tests on Linux and macOS, treating Lean warnings as
errors, and checks the active FFI sources with clang-format 18. To check formatting locally:

```sh
nix shell nixpkgs#llvmPackages_18.clang-tools -c clang-format --dry-run --Werror ffi/*.cpp ffi/*.h
```

Dependency updates are checked every two days and proposed as pull requests when
validation succeeds. Version tags such as `v0.1.0` and `v0.1.0-rc1` create GitHub
releases after CI passes; release candidates are marked as prereleases.

## Usage

```lean
import Transmog

open Transmog

structure Point where
  x : UInt32
  y : UInt32
  deriving Repr

transmog Point as [px : UInt32, py : UInt32] where
  x : UInt32 <= px
  y : UInt32 <= py
derive_layout C packed

def points : CompactArray Point :=
  CompactArray.empty.push { x := 10, y := 20 }

#eval points.toList       -- [{ x := 10, y := 20 }]
#eval points.data.size    -- 8
#eval points.iter.toList  -- [{ x := 10, y := 20 }]
```

[Examples/Points.lean](Examples/Points.lean) runs this block and a few more operations on the array.

The `transmog` clause allows us to declare a list of unsigned integers as the "slab", then we define how we unpack them to recover the Lean values.
Type casting and the correctness proof will be automated by Transmog.
In the above layout, a `Point` is represented in 8 bytes, namely two `UInt32`'s.

The `C packed` layout preserves field order and uses byte alignment.
The mental model of layouts here should be similar to Rust's `#[repr]`, where `C` and `auto` sets the ordering, and `packed N` and `align N` sets the alignment.
Scalar encodings are little-endian, including on targets whose native byte order differs.
Endianness is usually not a concern here because the writer and the reader are both code in this library.
Layouts describe the stored byte representation only, they do not change Lean's ordinary object
layout; the experimental `replace_runtime` clause described below is the one exception.

The native scalar reads and writes use *inline* C implementations.
Scalar pushes use the small C++ library in `ffi/`, which Lake builds and links automatically.
Consumers need no custom include paths or C compiler flags.
Since Lean's compiler does a good job at inlining and simplification, the resulting runtime code is comparative to a hand-written, carefully fine-tuned low-level code.

## A more involved example: BDD nodes

A binary decision diagram (BDD) branches on a Boolean variable at each internal node.
The high edge selects the branch where the variable is true, and the low edge selects it where the variable is false.
Our design distinguishes the terminal from references to internal nodes through an inductive type to save heap lookups.
The `Node` type takes 31-bits, with `0` denoting the terminal `Node.sink` and non-`0` values denoting a pointer `Node.inode p`.

An edge pairs a `Node` with a one-bit complement flag, which, when set, negates the denoted Boolean function.
The entire edge fits in one `UInt32`: bit 0 holds the complement flag, and bits 1–31 hold the representation of `Node`.
The pointer's nonzero constraint distinguishes the two constructors, and its 31-bit bound ensures that packing loses no information.

An `InternalNode` consists of a variable label and two edges, `hi` and `lo`, each occupying one `UInt32`.
The terminal is represented directly in an edge and requires no entry in the internal-node array.

```text
InternalNode (12 bytes; byte offsets increase to the right)

byte  0                   4                   8                  12
      +-------------------+-------------------+-------------------+
      | var : UInt32      | hi : UInt32       | lo : UInt32       |
      +-------------------+-------------------+-------------------+
           4 bytes             4 bytes             4 bytes

Each edge word (hi or lo; bits shown from most to least significant)

bit   31                                               1     0
      +------------------------------------------------+-----+
      | Node representation (31 bits)                  |compl|
      +------------------------------------------------+-----+
        0  = sink                                        1 bit
        p  = inode p, where 0 < p < 2^31
```

This data layout can be expressed in Transmog as follows:

```lean
import Transmog

open Transmog

namespace BDD

abbrev Ptr := { p : UInt32 // p ≠ 0 ∧ p.fitsBits 31 }

transmog Ptr as [p : UInt32[0:31] // p ≠ 0]

inductive Node where
  | sink
  | inode (p : Ptr)

transmog Node as [n : UInt32[0:31]] where
  | sink => guard n = 0
  | inode =>
    p : Ptr <= n

structure Edge where
  compl : Bool
  node : Node

transmog Edge as [r : UInt32] where
  compl : Bool <= lsbAsBool r[0]
  node : Node <= r[1:32]
derive_layout C packed

structure InternalNode where
  var : UInt32
  hi : Edge
  lo : Edge

transmog InternalNode as [var : UInt32, hi : UInt32, lo : UInt32] where
  var : UInt32 <= var
  hi : Edge <= hi
  lo : Edge <= lo
derive_layout C packed

example : (HasLayout.layout (α := Edge)).size = 4 := rfl
example : (HasLayout.layout (α := InternalNode)).size = 12 := rfl

abbrev NodeArray := CompactArray InternalNode

end BDD
```

The guard `n = 0` selects `sink` when decoding; a nonzero value decodes to `inode p`.
The slice `r[1:32]` is half-open, and `lsbAsBool` converts bit 0 to a `Bool`.
These declarations compose the representations of `Ptr`, `Node`, and `Edge`, then derive the byte layout of `InternalNode`.
Transmog generates the conversions and their round-trip proofs, while user code can still pattern-match on `Node.sink` and `Node.inode p`.

In this design, the uncomplemented terminal denotes `false`, so the packed edge words `0` and `1` denote `false` and `true`, respectively.
An edge to an internal node is encoded as `(p << 1) | complement`.
Pointers are one-based: pointer `p` addresses array element `p - 1`, at byte offset `12 * (p - 1)`.
Thus, the array stores only internal nodes, without a placeholder for the terminal.

The layout in use, `C packed`, introduces no padding, giving a stride of 12 bytes.
The data for array element `i` begins at byte offset `12 * i`, and elements are accessed through the usual `CompactArray` operations.
[Examples/BDD.lean](Examples/BDD.lean) contains this layout together with code that builds a small diagram in the array and evaluates it.

A type with parameters is represented one instantiation at a time.
With `inductive Node (α : Type u)` in place of the `Node` above, the same declaration reads `transmog Node Ptr as [n : UInt32[0:31]] where ...`, and a structure over it writes its field types as instantiated, `node : Node Ptr <= r[1:32]`.
Each instantiation gets its own `DataRepr` and `HasLayout` instances, so `Node Ptr` and `Node Bool` can be laid out differently.
A bare type `T` also receives the package `T.Repr` with `toRepr`, `fromRepr` and `from_to`; an instantiation has no namespace of its own, so its codecs are reached through the classes.
The `replace_runtime` clause below does not extend to instantiations, because the compiler represents an inductive type the same way for all of them.

### Declaring the type and its representation together

A closed type can be declared together with its representation, so that the constructors and the fields are written once.
`transmog enum` stands for an `inductive` and `transmog struct` for a `structure`; each field carries its place, and the guard and the slot hints of a constructor follow a `=>`.

```lean
/-- A BDD node. -/
transmog enum Node as [n : UInt32[0:31]] where
  /-- The terminal. -/
  | sink => guard n = 0
  /-- An internal node. -/
  | inode (p : Ptr <= n)
deriving DecidableEq, Repr

transmog struct Edge as [r : UInt32] where
  compl : Bool <= lsbAsBool r[0]
  node : Node <= r[1:32]
derive_layout C packed
deriving DecidableEq, Repr
```

The command expands to the `inductive` or `structure` declaration, the `transmog` declaration over it and a `deriving instance` command.
The instances are derived right after the type, so the representation can use them, as the fallback of `fromRepr` uses `Inhabited` and a `correct_by` proof may use `DecidableEq`; with a `replace_runtime` clause they are derived last instead, after the clause has taken effect.
Doc comments, attributes and the visibility of the type, doc comments and modifiers of constructors and fields, default values and auto-params of fields, and a custom constructor `make ::` of a structure all go to the type declaration unchanged.
Parameters, indices and `extends` have no place in the combined forms, since a representation belongs to a closed type; an instantiation of a parametric type is still represented with the standalone declaration.

### Niches

A slot value that no payload produces can mark a constructor, which is what Rust calls a niche.
The `Node` above already uses one, since a pointer is never `0`.
The same works for an enumeration, which takes a few of a byte's values and leaves the rest to the wrappers around it:

```lean
transmog Ordering as [o : UInt8 // o ≤ 2] where
  | lt => guard o = 0
  | eq => guard o = 1
  | gt => guard o = 2

transmog Option Ordering as [o : UInt8 // o ≤ 3] where
  | none => guard o = 3
  | some => val : Ordering <= o
```

The valid range is stated on the slot rather than computed, and the round-trip theorem checks that the guard falls outside the payload's range.
A field whose representation carrier is such a constrained slot is placed through that representation, so niches nest, and a constrained representation fits into a bit slice of a wider slot whenever the ranges agree, as `Option Ordering` does in two bits.
`derive_layout` does not yet accept a slot with a custom `//` property, so such a representation is stored through a type that embeds it in plain slots.
[Examples/Niche.lean](Examples/Niche.lean) goes through the usual sources of niches, a nonzero pointer, an index below a sentinel, an enumeration, a component of a pair, and packs four `Option Ordering` into one byte.

## Experimental: replacing the runtime representation

Ordinarily a value of `Node` is a heap-allocated constructor object even though its representation
is a single 31-bit word, and the packed form only appears once the value is stored in a
`CompactArray`. The `replace_runtime` clause removes that gap: the compiler then carries `Node`
values as the boxed representation word everywhere, so matching becomes an unboxing and a compare,
construction becomes a boxing, and the representation round trip becomes the identity. Nothing
changes logically. Pattern matching, the recursors, derived instances, and the `DataRepr` laws are
all still the ones the type theory gives.

```lean
inductive Node where
  | sink
  | inode (p : Ptr)

transmog Node as [n : UInt32[0:31]] where
  | sink => guard n = 0
  | inode =>
    p : Ptr <= n
  replace_runtime
```

The carrier defaults to the smallest of `UInt8`, `UInt16` and `UInt32` that holds the
representation, and `replace_runtime as UInt16` selects one explicitly. Wider carriers are
rejected because only these three box into an immediate on a 64-bit host; on a 32-bit host boxing
a `UInt32` allocates, which costs performance but not correctness.

By default the clause applies to an inductive that has at least one constructor without fields and
at least one with, because that is the shape the compiler treats as a possibly-tagged pointer, on
which it already tests for a scalar before counting references. A structure and an inductive whose
every constructor carries a field are rejected unless the classification override described below
is enabled. Always rejected, with an explanation, are a type whose every constructor is fieldless
and a structure with a single relevant field, since the compiler already represents both as
scalars, as well as parameters, indices, universe parameters, proof fields, and representations
wider than 32 bits.

The clause must appear in the module that declares the inductive, before anything that mentions
it. A definition compiled earlier still reads the object layout, and the clause reports it by
name; that includes the instances a `deriving` clause on the `inductive` itself would derive.
The combined form avoids the question, since its `deriving` clause runs after the clause:

```lean
transmog enum Node as [n : UInt32[0:31]] where
  | sink => guard n = 0
  | inode (p : Ptr <= n)
replace_runtime
deriving DecidableEq, Repr
```

For a hand-written `inductive`, write `deriving instance ... for Node` after the `transmog`
declaration instead.  The module must also re-export a path to Transmog's code generator passes,
which `public import Transmog.DSL` provides; consumers then need nothing at all, in this package
or in another one.

At function boundaries a word-backed value still has Lean's `lean_object*` ABI, so C code reached
through `extern` sees a boxed word and must not use `lean_ctor_get` on it.

### Overriding the compiler's classification

The compiler classifies each inductive once, when it is declared, into the IR type that decides
how the backend treats its values. A structure such as `Edge`, and any inductive whose every
constructor carries a field, is classified as a definite heap reference, and the backend then
increments and decrements its reference count without first testing for a scalar. A boxed word
does not survive that, which is why such types are rejected by default.

```lean
set_option transmog.replaceRuntime.overrideClassification true

structure Edge where
  compl : Bool
  node : Node

transmog Edge as [r : UInt32] where
  compl : Bool <= lsbAsBool r[0]
  node : Node <= r[1:32]
replace_runtime
derive_layout C packed
```

With `transmog.replaceRuntime.overrideClassification` set, the clause instead rewrites the
classification of the type to `tagged`, the IR type of a value that is always a boxed scalar,
which is exactly what a word-backed value is. The override applies to every `replace_runtime`
clause in the file, including the ones the default would have accepted, and it removes reference
counting from the type altogether rather than leaving the tested no-ops behind. Field access
through projections,
through `match`, and through the recursors is routed through the packed word in the same way as
for an inductive, so `Edge` values are carried as words and `InternalNode` from the example above
stores its two edges as two immediates.

[Examples/WordBacked.lean](Examples/WordBacked.lean) declares `Node` and `Edge` this way and shows that the representation of a value is the word the compiler carries.

Because the classification is fixed when a type is declared, a structure or inductive that stores
a field of the type and was declared before the clause keeps the old classification for that field
and would count references on the word. The clause rejects such containers by name; declare them
after it. A wrapper the compiler erases to its single field is exempt, since it has no layout of
its own.

The option is unsafe in the literal sense. It writes to a table that is private to the compiler,
located by name, so it depends on the pinned toolchain; the clause reads its write back through
the compiler's own accessor and fails if the table has moved. And the classification is a claim
the compiler takes on trust: should a value of the type turn out to be a heap object after all,
it is freed by nobody or dereferenced as a scalar, without any diagnostic. Enable the option
deliberately and keep it scoped to the files that need it.

### What this costs

The kernel is untouched and the `transmog` declaration keeps its round-trip theorem. What the clause
adds is a claim the compiler cannot check, namely that the generated helpers really do reinterpret
the value, at the same level of trust as `@[implemented_by]`. It also depends on how the pinned
Lean toolchain lowers inductive types, which is why it is experimental and warns at every use;
`set_option experimental.transmog.replaceRuntime true` acknowledges that status and silences the
warning once the tradeoff is understood.

Against a mistake in the arrangement rather than in the trust assumption there is a guard. A
verification pass runs once code generation has finished inlining and turns any surviving
construction, projection or elimination through the object layout into a compile error in
whichever module it appears, rather than into memory corruption at run time.

## License

Transmog is distributed under the [MIT license](LICENSE.md).
