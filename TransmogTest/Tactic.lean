/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL.Core.UInt
public import Transmog.DSL.Tactics

/-!
# Tests for the proof automation

One goal per rung of the `transmog_subtype_trivial` ladder, chosen so that the rungs below it
cannot close the goal, then the round-trip finishers and the two failure messages.
-/

namespace Transmog.Test.Tactic

/-! ## The `transmog_subtype` ladder -/

public section

-- `rfl`.
theorem byRfl (x : UInt8) : x = x := by transmog_subtype

-- `assumption`.
theorem byAssumption (x : UInt8) (_h : x ≠ 0) : x ≠ 0 := by transmog_subtype

-- The keyed `simp_all` rung, through the generic slice lemmas of `transmog_norm`.
theorem bySlice (x : UInt16) : (x.extractSlice 1 4).fitsBits 3 := by transmog_subtype
theorem byVal (p : { x : UInt8 // x.fitsBits 3 }) : p.val.fitsBits 3 := by transmog_subtype
theorem byToBool (b : Bool) : b.toUInt8.fitsBits 1 := by transmog_subtype
theorem byPos (x : UInt32) (_h : 0 < x) : x ≠ 0 := by transmog_subtype
theorem byFitsAll (x : UInt16) : x.fitsBits 16 := by transmog_subtype

-- `grind`, reading `fitsBits` arithmetically.
theorem byGrind (x : UInt8) (h : x.fitsBits 1) : x ≤ 2 := by transmog_subtype
theorem byGrindToNat (x : UInt8) (h : x.toNat < 8) : x.fitsBits 3 := by transmog_subtype
theorem byGrindWiden (x : UInt16) (h : x.fitsBits 12) : x.fitsBits 13 := by transmog_subtype

-- `bv_decide`, on a bitwise hypothesis arithmetic does not see through.
theorem byBvDecide (x : UInt8) (h : x &&& 0xF0 = 0) : x < 16 := by transmog_subtype

-- `bv_decide` after simplifying the goal with the `transmog_subtype_simps` definitions.
theorem bySimpBvDecide (x : UInt32) (b : Bool) :
    ((x.extractSlice 0 31).packBoolLsb b).extractSlice 1 32 = x.extractSlice 0 31 := by
  transmog_subtype

end

-- A conjunction splits and each side takes its own rung.
example (x : UInt8) (_h : x ≠ 0) : x ≠ 0 ∧ x.fitsBits 8 := by transmog_subtype
example (x : UInt16) (h : x.fitsBits 12) : (x.extractSlice 1 4).fitsBits 3 ∧ x ≤ 4095 := by
  transmog_subtype

-- A user tactic runs before the ladder.
example (x : UInt8) (h : x = 3) : x < 4 := by transmog_subtype_with (subst h; decide)

-- Nothing left to prove.
example : (3 : UInt8) < 4 := by
  decide
  transmog_subtype

-- The obligations of the niche encodings, in the shape codegen leaves them.
example (x : UInt8) (h : x.fitsBits 1) : x ≤ 2 := by transmog_subtype
example (x : UInt8) (h : x.fitsBits 2) (hne : ¬ x = 3) : x ≤ 2 := by transmog_subtype
example (r : UInt32) (h : r.fitsBits 31) (hne : ¬ r = 0) : r ≠ 0 ∧ r.fitsBits 31 := by
  transmog_subtype

/-! ## The round-trip finishers -/

-- Rung one, the keyed normal form.
example (b : Bool) : b.toUInt8.lsbAsBool = b := by transmog_from_to_case []
example (x : UInt8) (h : x.fitsBits 1) : ¬ x = 2 := by transmog_from_to_case []
example (p : { x : UInt32 // x.fitsBits 31 }) (b : Bool) :
    (⟨UInt32.packBoolLsb p.val b >>> 1, by transmog_subtype⟩ : { x : UInt32 // x.fitsBits 31 }) =
      p := by
  transmog_from_to_case []

-- Rung two, `grind` bridging arithmetic the normal form leaves behind.
example (a b : UInt8) (ha : a.toNat < 4) (hb : b.fitsBits 2) : a.toNat + b.toNat < 8 := by
  transmog_from_to_case []

-- Extra simp lemmas unfold the user's definitions.
def enc (b : Bool) : UInt8 := b.toUInt8
def dec (x : UInt8) : Bool := x.lsbAsBool

example : ∀ b, dec (enc b) = b := by transmog_from_to [enc, dec]

inductive Tri where
  | a
  | b
  | c

def Tri.enc : Tri → UInt8
  | .a => 0
  | .b => 1
  | .c => 2

def Tri.dec (x : UInt8) : Tri :=
  if x = 0 then .a else if x = 1 then .b else .c

example : ∀ t, Tri.dec (Tri.enc t) = t := by transmog_from_to [Tri.enc, Tri.dec]

/-! ## Axioms -/

/-- info: 'Transmog.Test.Tactic.bySlice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bySlice

/-- info: 'Transmog.Test.Tactic.byGrind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms byGrind

/--
info: 'Transmog.Test.Tactic.byBvDecide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 byBvDecide._native.bv_decide.ax_1_5]
-/
#guard_msgs in
#print axioms byBvDecide

/-! ## Errors -/

/--
error: failed to prove Transmog `DataRepr` subtype obligation
x : UInt8
⊢ x < 3
-/
#guard_msgs in
example (x : UInt8) : x < 3 := by transmog_subtype

/--
error: failed to prove Transmog `DataRepr` round-trip obligation: goal constituents did not align; restate guard conjuncts in the same form as the field subtype properties, or provide `correct_by`
x : UInt8
h : UInt8.fitsBits 1 x
⊢ x = 0
-/
#guard_msgs in
example (x : UInt8) (h : x.fitsBits 1) : x = 0 := by transmog_from_to_case []

-- A known gap: the `bv_decide` rungs unfold `fitsBits` to a shape with `UInt8.ofNat 4`, which
-- `bv_decide` abstracts as an opaque variable, so a bitwise goal under a `fitsBits` hypothesis
-- is out of reach.
/--
error: failed to prove Transmog `DataRepr` subtype obligation
x : UInt8
h : UInt8.fitsBits 4 x
⊢ x &&& 240 = 0
-/
#guard_msgs in
example (x : UInt8) (h : x.fitsBits 4) : x &&& 0xF0 = 0 := by transmog_subtype

end Transmog.Test.Tactic
