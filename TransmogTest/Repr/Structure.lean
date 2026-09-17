/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL
meta import Transmog.DSL

/-!
# Tests for structure representations and the field conversion table

One declaration per row of the `FieldConversion` table, the two gadgets, products, hints, the
declarations a `transmog` command generates for a structure, and the diagnostics of a structure
body.
-/

-- Deliberately ill-formed declarations follow.
set_option linter.hazel false

namespace Transmog.Test.Structure

open Transmog

@[expose] public section

/-! ## `equiv`: the field type is the slot type -/

structure Point where
  x : UInt32
  y : UInt32
deriving DecidableEq

transmog Point as [px : UInt32, py : UInt32] where
  x : UInt32 <= px
  y : UInt32 <= py

example : DataRepr Point (UInt32 × UInt32) := inferInstance
example : Point.Repr.toRepr ⟨1, 2⟩ = (1, 2) := rfl
example : Point.Repr.fromRepr (1, 2) = ⟨1, 2⟩ := rfl
example (p : Point) : Point.Repr.fromRepr (Point.Repr.toRepr p) = p := Point.Repr.from_to p
example : DataRepr.fromRepr (DataRepr.toRepr (⟨1, 2⟩ : Point)) = (⟨1, 2⟩ : Point) := by decide

-- A subtype field into a slot carrying the same property, up to binder names.
structure Small where
  v : { u : UInt32 // u < 16 }
deriving DecidableEq

transmog Small as [r : UInt32 // r < 16] where
  v : { u : UInt32 // u < 16 } <= r

example : Small.Repr.toRepr ⟨⟨7, by decide⟩⟩ = ⟨7, by decide⟩ := rfl

/-! ## `project`: a subtype field into a bare slot, when the property is inherent -/

structure Fits where
  v : { u : UInt8 // u.fitsBits 8 }
deriving DecidableEq

transmog Fits as [r : UInt8] where
  v : { u : UInt8 // u.fitsBits 8 } <= r

example : DataRepr Fits UInt8 := inferInstance
example : Fits.Repr.toRepr ⟨⟨7, by decide⟩⟩ = 7 := rfl
example : Fits.Repr.fromRepr 7 = ⟨⟨7, by decide⟩⟩ := rfl

/-! ## `inject`: a bare field into a subtype slot -/

structure Byte where
  v : UInt8
deriving DecidableEq

transmog Byte as [r : UInt8 // r ≤ 255] where
  v : UInt8 <= r

example : DataRepr Byte { r : UInt8 // r ≤ 255 } := inferInstance
example : (Byte.Repr.toRepr ⟨7⟩).val = 7 := rfl
example : Byte.Repr.fromRepr ⟨7, by decide⟩ = ⟨7⟩ := rfl

/-! ## `reproject`: two subtypes over the same scalar -/

structure Nibble where
  v : { u : UInt32 // u < 16 }
deriving DecidableEq

transmog Nibble as [r : UInt32 // r ≤ 15] where
  v : { u : UInt32 // u < 16 } <= r

example : DataRepr Nibble { r : UInt32 // r ≤ 15 } := inferInstance
example : (Nibble.Repr.toRepr ⟨⟨7, by decide⟩⟩).val = 7 := rfl
example : Nibble.Repr.fromRepr ⟨7, by decide⟩ = ⟨⟨7, by decide⟩⟩ := rfl

-- A ranged place is a subtype of the scalar as well.
structure Nibbles where
  lo : { u : UInt8 // u < 16 }
  hi : { u : UInt8 // u < 16 }
deriving DecidableEq

transmog Nibbles as [r : UInt8] where
  lo : { u : UInt8 // u < 16 } <= r[:4]
  hi : { u : UInt8 // u < 16 } <= r[4:]

example : Nibbles.Repr.toRepr ⟨⟨0xA, by decide⟩, ⟨0xB, by decide⟩⟩ = 0xBA := by decide
example : Nibbles.Repr.fromRepr 0xBA = ⟨⟨0xA, by decide⟩, ⟨0xB, by decide⟩⟩ := by decide

/-! ## `reprProject` and `reprReproject`: a field placed through its representation -/

transmog Option Bool as [r : UInt8 // r ≤ 2] where
  | none => guard r = 2
  | some => val : Bool <= lsbAsBool r

-- The carrier `{ r // r ≤ 2 }` into a bare slot: the obligation on decoding comes from the guard.
inductive Held where
  | held (b : Option Bool)
  | empty
deriving DecidableEq

transmog Held as [r : UInt8] where
  | held =>
    guard r ≤ 2
    b : Option Bool <= r
  | empty => r := 3

example : Held.Repr.toRepr (.held (some true)) = 1 := rfl
example : Held.Repr.toRepr (.held none) = 2 := rfl
example : Held.Repr.toRepr .empty = 3 := rfl
example : Held.Repr.fromRepr 2 = .held none := by decide
example : Held.Repr.fromRepr 3 = .empty := by decide

-- A carrier into a two-bit place, another subtype of the scalar with the same range.
transmog Option (Option Bool) as [r : UInt8 // r ≤ 3] where
  | none => guard r = 3
  | some => val : Option Bool <= r

structure Pair where
  a : Option (Option Bool)
  b : Option (Option Bool)
deriving DecidableEq

transmog Pair as [r : UInt8] where
  a : Option (Option Bool) <= r[0:2]
  b : Option (Option Bool) <= r[2:4]

example : Pair.Repr.toRepr ⟨some none, none⟩ = 0b1110 := rfl
example : Pair.Repr.fromRepr 0b1110 = ⟨some none, none⟩ := by decide

/-! ## `needCast`: everything else goes through `DataCastT` -/

-- A nested representation whose carrier is the slot type itself.
structure Foo where
  v : UInt32
deriving DecidableEq

transmog Foo as [r : UInt32] where
  v : UInt32 <= r

structure FooWrap where
  f : Foo
deriving DecidableEq

transmog FooWrap as [r : UInt32] where
  f : Foo <= r

example : FooWrap.Repr.toRepr ⟨⟨99⟩⟩ = 99 := rfl
example : FooWrap.Repr.fromRepr 99 = ⟨⟨99⟩⟩ := rfl

-- A scalar of another signedness converts through the base casts without any gadget.
structure Signed where
  v : Int16
deriving DecidableEq

transmog Signed as [r : UInt16] where
  v : Int16 <= r

example : Signed.Repr.toRepr ⟨-5⟩ = 0xFFFB := by decide
example : Signed.Repr.fromRepr 0xFFFB = ⟨-5⟩ := by decide

/-! ## Gadgets -/

-- `cast` forces the conversion through `DataCastT`, also across a product.
structure Casts where
  v : Int16
  w : Int8 × UInt16
deriving DecidableEq

transmog Casts as [r : UInt16, a : UInt8, b : UInt16] where
  v : Int16 <= cast r
  w : (Int8 × UInt16) <= cast (a, b)

example : Casts.Repr.toRepr ⟨-1, (-2, 3)⟩ = (0xFFFF, 0xFE, 3) := by decide
example : Casts.Repr.fromRepr (0xFFFF, 0xFE, 3) = ⟨-1, (-2, 3)⟩ := by decide

-- `lsbAsBool` reads one bit as a `Bool`.
structure Flags where
  a : Bool
  b : Bool
  rest : { u : UInt8 // u.fitsBits 6 }
deriving DecidableEq

transmog Flags as [r : UInt8] where
  a : Bool <= lsbAsBool r[0]
  b : Bool <= lsbAsBool r[1]
  rest : { u : UInt8 // u.fitsBits 6 } <= r[2:]

example : Flags.Repr.toRepr ⟨true, false, ⟨0b101010, by decide⟩⟩ = 0b10101001 := by decide
example : Flags.Repr.fromRepr 0b10101001 = ⟨true, false, ⟨0b101010, by decide⟩⟩ := by decide

/-! ## Products -/

structure Pairs where
  pair : UInt32 × UInt32
  triple : UInt8 × UInt16 × Bool
deriving DecidableEq

transmog Pairs as [a : UInt32, b : UInt32, c : UInt8, d : UInt16, e : UInt8] where
  pair : (UInt32 × UInt32) <= (a, b)
  triple : (UInt8 × UInt16 × Bool) <= (c, d, lsbAsBool e)

example : Pairs.Repr.toRepr ⟨(1, 2), (3, 4, true)⟩ = (1, 2, 3, 4, 1) := rfl
example : Pairs.Repr.fromRepr (1, 2, 3, 4, 1) = ⟨(1, 2), (3, 4, true)⟩ := by decide

/-! ## Field order and hints -/

-- Fields may be written in any order; the codecs follow the constructor.
structure Ordered where
  first : UInt8
  second : UInt16
deriving DecidableEq

transmog Ordered as [s : UInt16, f : UInt8] where
  second : UInt16 <= s
  first : UInt8 <= f

example : Ordered.Repr.toRepr ⟨1, 2⟩ = (2, 1) := rfl

/--
info: @[expose] def Transmog.Test.Structure.Ordered.Repr.toRepr : Ordered → UInt16 × UInt8 :=
fun x ↦
  match x with
  | { first := first, second := second } => (second, first)
-/
#guard_msgs in
#print Ordered.Repr.toRepr

-- A slot no field writes is zero unless a hint sets it.
structure Tagged where
  v : UInt8
deriving DecidableEq

set_option linter.unusedVariables false in
transmog Tagged as [tag : UInt8, v : UInt8] where
  tag := 7
  v : UInt8 <= v

example : Tagged.Repr.toRepr ⟨1⟩ = (7, 1) := rfl
example : Tagged.Repr.fromRepr (0, 1) = ⟨1⟩ := rfl

structure Untagged where
  v : UInt8
deriving DecidableEq

set_option linter.unusedVariables false in
transmog Untagged as [pad : UInt8, v : UInt8] where
  v : UInt8 <= v

example : Untagged.Repr.toRepr ⟨1⟩ = (0, 1) := rfl

/-! ## The generated declarations -/

/-- info: Transmog.Test.Structure.Point.Repr.toRepr : Point → UInt32 × UInt32 -/
#guard_msgs in
#check Point.Repr.toRepr

/-- info: Transmog.Test.Structure.Point.Repr.fromRepr : UInt32 × UInt32 → Point -/
#guard_msgs in
#check Point.Repr.fromRepr

/--
info: theorem Transmog.Test.Structure.Point.Repr.from_to : ∀ (x : Point), Point.Repr.fromRepr (Point.Repr.toRepr x) = x
-/
#guard_msgs in
#print sig Point.Repr.from_to

/--
info: @[instance_reducible, expose] def Transmog.Test.Structure.instDataReprPointProdUInt32 : DataRepr Point
  (UInt32 × UInt32) :=
{ toRepr := Point.Repr.toRepr, fromRepr := Point.Repr.fromRepr, from_to := Point.Repr.from_to }
-/
#guard_msgs in
#print instDataReprPointProdUInt32

-- The codecs are inlined.
run_meta do
  let env ← Lean.getEnv
  guard (Lean.Compiler.hasInlineAttribute env ``Point.Repr.toRepr)
  guard (Lean.Compiler.hasInlineAttribute env ``Point.Repr.fromRepr)

/-- info: 'Transmog.Test.Structure.Point.Repr.from_to' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Point.Repr.from_to

/-- info: 'Transmog.Test.Structure.Flags.Repr.from_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Flags.Repr.from_to

/-- info: 'Transmog.Test.Structure.Pair.Repr.from_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pair.Repr.from_to

end

/-! ## Errors -/

structure Q where
  x : UInt8
  y : UInt8

/-- error: cannot transmogrify types without runtime data -/
#guard_msgs in
transmog Q as [r : UInt8] where

/-- error: don't know how to represent the following fields of `Q`: [y] -/
#guard_msgs in
transmog Q as [r : UInt8] where
  x : UInt8 <= r

/-- error: `z` is not a field of structure `Q` -/
#guard_msgs in
transmog Q as [r : UInt8, s : UInt8] where
  x : UInt8 <= r
  y : UInt8 <= s
  z : UInt8 <= s

/-- error: duplicate field `x` -/
#guard_msgs in
transmog Q as [r : UInt8, s : UInt8] where
  x : UInt8 <= r
  x : UInt8 <= s

/--
error: field `x` of `Q.mk` has type
  UInt8
but is declared with type
  UInt16
-/
#guard_msgs in
transmog Q as [r : UInt8, s : UInt8] where
  x : UInt16 <= r
  y : UInt8 <= s

/-- error: the type is not fully determined; a type in a representation must be closed -/
#guard_msgs in
transmog Q as [r : UInt8, s : UInt8] where
  x : _ <= r
  y : UInt8 <= s

/-- error: structure-like repr requires a Lean structure type -/
#guard_msgs in
transmog Option UInt8 as [r : UInt8] where
  val : UInt8 <= r

/-- error: invalid gadget foo, supported ones: `cast`, `lsbAsBool` -/
#guard_msgs in
transmog Q as [r : UInt8, s : UInt8] where
  x : UInt8 <= foo r
  y : UInt8 <= s

/-- error: `lsbAsBool` requires an atomic ident (may with bit range), got (r, s) -/
#guard_msgs in
transmog Q as [r : UInt8, s : UInt8] where
  x : UInt8 <= lsbAsBool (r, s)
  y : UInt8 <= s

/-- error: expected a product type with at least 2 factors, got: UInt8 -/
#guard_msgs in
transmog Q as [r : UInt8, s : UInt8] where
  x : UInt8 <= r
  y : UInt8 <= (r, s)

/--
error: conflicting writes to `r`: this write and an earlier one target the same bits with different values
-/
#guard_msgs in
transmog Q as [r : UInt8, s : UInt8] where
  x : UInt8 <= r
  y : UInt8 <= s
  r := 1
  r := 2

/-- error: overlapping bit-range writes to slot `r`: [2:6) overlaps an earlier write to [0:4) -/
#guard_msgs in
transmog Q as [r : UInt8] where
  x : UInt8 <= r[:4]
  y : UInt8 <= r[2:6]

/-! ### Failures inside the generated definitions -/

-- These leave the codecs behind, so each uses a type of its own.

structure NestedCast where
  v : Int16

/-- error: nested `cast` is not supported in the Transmog DSL -/
#guard_msgs in
transmog NestedCast as [r : UInt16] where
  v : Int16 <= cast (cast r)

structure NotBool where
  v : UInt8

-- Each codec reports the missing cast.
/--
error: failed to synthesize instance of type class
  DataCastT UInt8 Bool

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: failed to synthesize instance of type class
  DataCastT UInt8 Bool

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
transmog NotBool as [r : UInt8] where
  v : UInt8 <= lsbAsBool r

structure Narrowing where
  v : UInt32

/--
error: failed to synthesize instance of type class
  DataCastT UInt32 UInt8

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: failed to synthesize instance of type class
  DataCastT UInt32 UInt8

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
transmog Narrowing as [r : UInt8] where
  v : UInt32 <= r

structure Loose where
  v : { u : UInt32 // u < 16 }

-- A property the slot does not carry cannot be re-established on decoding.
/--
error: failed to prove Transmog `DataRepr` subtype obligation
repr✝ : UInt32
r : UInt32 := repr✝
⊢ r < 16
-/
#guard_msgs in
transmog Loose as [r : UInt32] where
  v : { u : UInt32 // u < 16 } <= r

end Transmog.Test.Structure
