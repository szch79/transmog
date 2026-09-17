/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL

/-!
# Tests for the bodiless form

A `transmog` declaration without a body represents a type that is itself a scalar or a subtype of
one, converting through the same table as a field would.
-/

namespace Transmog.Test.Alias

open Transmog

@[expose] public section

/-! ## `equiv` -/

-- A scalar is its own representation.
transmog UInt32 as [r : UInt32]

example : DataRepr UInt32 UInt32 := inferInstance
example : UInt32.Repr.toRepr 7 = 7 := rfl
example : UInt32.Repr.fromRepr 7 = 7 := rfl

-- The package of a scalar lives in the scalar's own namespace.
/--
info: @[expose] def UInt32.Repr.toRepr : UInt32 → UInt32 :=
id
-/
#guard_msgs in
#print UInt32.Repr.toRepr

/-! ## `project` and `reproject` -/

abbrev Ptr := { p : UInt32 // p ≠ 0 ∧ p.fitsBits 31 }

transmog Ptr as [p : UInt32[0:31] // p ≠ 0]

example : DataRepr Ptr { p : UInt32 // p ≠ 0 ∧ p.fitsBits 31 } := inferInstance
example : (Ptr.Repr.toRepr ⟨5, by decide⟩).val = 5 := rfl
example : (Ptr.Repr.fromRepr ⟨5, by decide⟩).val = 5 := rfl

abbrev Nibble := { u : UInt8 // u < 16 }

transmog Nibble as [r : UInt8 // r ≤ 15]

example : (Nibble.Repr.toRepr ⟨5, by decide⟩).val = 5 := rfl

-- A subtype into a bare slot, when its property is inherent.
abbrev Fits := { u : UInt8 // u.fitsBits 8 }

transmog Fits as [r : UInt8]

example : Fits.Repr.toRepr ⟨5, by decide⟩ = 5 := rfl
example : Fits.Repr.fromRepr 5 = ⟨5, by decide⟩ := rfl

/-! ## `inject` -/

abbrev Byte := UInt8

transmog Byte as [r : UInt8 // r ≤ 255]

example : (Byte.Repr.toRepr 5).val = 5 := rfl

/-! ## `needCast` -/

transmog Int16 as [r : UInt16]

example : Int16.Repr.toRepr (-1) = 0xFFFF := by decide
example : Int16.Repr.fromRepr 0xFFFF = -1 := by decide

/-! ## Generated declarations -/

/--
info: theorem Transmog.Test.Alias.Ptr.Repr.from_to : ∀ (x : Ptr), Ptr.Repr.fromRepr (Ptr.Repr.toRepr x) = x
-/
#guard_msgs in
#print sig Ptr.Repr.from_to

/-- info: 'Transmog.Test.Alias.Ptr.Repr.from_to' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Ptr.Repr.from_to

/-- info: 'Int16.Repr.from_to' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Int16.Repr.from_to

end

end Transmog.Test.Alias
