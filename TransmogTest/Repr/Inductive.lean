/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL

/-!
# Tests for inductive representations

Arms, guards and the writes inferred from them, hints, the unguarded fallback and the
`Inhabited` fallback, `correct_by`, the decode chain a body compiles to, and the diagnostics
of an inductive body.
-/

-- Deliberately ill-formed declarations follow.
set_option linter.hazel false

namespace Transmog.Test.Inductive

open Transmog

@[expose] public section

/-! ## A tag and a payload -/

inductive OptByte where
  | none
  | some (b : UInt8)
deriving DecidableEq

transmog OptByte as [tag : UInt8, v : UInt8] where
  | none =>
    guard tag = 0
  | some =>
    tag := 1
    b : UInt8 <= v

example : DataRepr OptByte (UInt8 × UInt8) := inferInstance
example : OptByte.Repr.toRepr .none = (0, 0) := rfl
example : OptByte.Repr.toRepr (.some 42) = (1, 42) := rfl
example : OptByte.Repr.fromRepr (0, 7) = .none := by decide
example : OptByte.Repr.fromRepr (1, 42) = .some 42 := by decide
-- Any tag other than the guarded one decodes as the unguarded constructor.
example : OptByte.Repr.fromRepr (9, 42) = .some 42 := by decide

/-! ## Writes inferred from guards -/

-- An equation with the slot on either side determines the slot; a conjunction contributes
-- every equation; parentheses and a comparison contribute nothing.
inductive Mode where
  | off
  | on
  | blink
  | dim (level : UInt8)
deriving DecidableEq

transmog Mode as [tag : UInt8, v : UInt8] where
  | off =>
    guard tag = 1
  | on =>
    guard 2 = tag ∧ v = 7
  | blink =>
    guard (tag = 3 ∧ (v = 8))
  | dim =>
    tag := 4
    level : UInt8 <= v

example : Mode.Repr.toRepr .off = (1, 0) := rfl
example : Mode.Repr.toRepr .on = (2, 7) := rfl
example : Mode.Repr.toRepr .blink = (3, 8) := rfl
example : Mode.Repr.toRepr (.dim 9) = (4, 9) := rfl
example : Mode.Repr.fromRepr (2, 7) = .on := by decide
example : Mode.Repr.fromRepr (2, 6) = .dim 6 := by decide
example : Mode.Repr.fromRepr (3, 8) = .blink := by decide

-- The guards are tested in order, and the unguarded arm is the fallback.
/--
info: @[expose] def Transmog.Test.Inductive.Mode.Repr.fromRepr : UInt8 × UInt8 → Mode :=
fun repr ↦
  have tag := repr.fst;
  have v := repr.snd;
  if h : tag = 1 then Mode.off
  else if h : 2 = tag ∧ v = 7 then Mode.on else if h : tag = 3 ∧ v = 8 then Mode.blink else Mode.dim v
-/
#guard_msgs in
#print Mode.Repr.fromRepr

-- A guard that is not an equation determines nothing, so the constructor needs a hint; the
-- guard is still available to the obligations of the arms after it.
inductive Range where
  | low
  | high (v : { u : UInt8 // 128 ≤ u })
deriving DecidableEq

transmog Range as [r : UInt8] where
  | low =>
    guard r < 128
    r := 0
  | high =>
    v : { u : UInt8 // 128 ≤ u } <= r

example : Range.Repr.toRepr .low = 0 := rfl
example : Range.Repr.fromRepr 5 = .low := by decide
example : Range.Repr.fromRepr 200 = .high ⟨200, by decide⟩ := by decide

-- A hint that repeats the guard is accepted.
inductive Repeated where
  | a
  | b
deriving DecidableEq, Inhabited

transmog Repeated as [t : UInt8] where
  | a =>
    guard t = 0
    t := 0
  | b => guard t = 1

example : Repeated.Repr.toRepr .a = 0 := rfl

/-! ## Slots no arm determines are zero -/

inductive Op where
  | nop
  | imm (v : UInt8)
deriving DecidableEq

transmog Op as [tag : UInt8, arg : UInt8] where
  | nop => guard tag = 0
  | imm =>
    tag := 1
    v : UInt8 <= arg

example : Op.Repr.toRepr .nop = (0, 0) := rfl

/-! ## Every constructor guarded -/

-- The fallback branch needs `Inhabited`.
inductive Tri where
  | a
  | b
  | c
deriving DecidableEq, Inhabited

transmog Tri as [t : UInt8] where
  | a => guard t = 0
  | b => guard t = 1
  | c => guard t = 2

example : Tri.Repr.toRepr .c = 2 := rfl
example : Tri.Repr.fromRepr 2 = .c := by decide
example : Tri.Repr.fromRepr 7 = default := by decide

/-! ## A manual round-trip proof -/

inductive Sign where
  | pos (v : UInt8)
  | neg (v : UInt8)
deriving DecidableEq

transmog Sign as [s : UInt8, w : UInt8] where
  | pos =>
    guard s = 0
    v : UInt8 <= w
  | neg =>
    s := 1
    v : UInt8 <= w
correct_by
  intro x
  cases x <;> rfl

example : Sign.Repr.fromRepr (1, 3) = .neg 3 := by decide

-- The whole-theorem finisher also serves `correct_by`.
inductive Bit where
  | zero
  | one
deriving DecidableEq, Inhabited

transmog Bit as [b : UInt8] where
  | zero => guard b = 0
  | one => guard b = 1
correct_by
  transmog_from_to []

/-! ## Generated declarations -/

/-- info: Transmog.Test.Inductive.OptByte.Repr.toRepr : OptByte → UInt8 × UInt8 -/
#guard_msgs in
#check OptByte.Repr.toRepr

/--
info: @[expose] def Transmog.Test.Inductive.OptByte.Repr.toRepr : OptByte → UInt8 × UInt8 :=
fun x ↦
  match x with
  | OptByte.none => (0, 0)
  | OptByte.some b => (1, b)
-/
#guard_msgs in
#print OptByte.Repr.toRepr

/-- info: 'Transmog.Test.Inductive.OptByte.Repr.from_to' depends on axioms: [propext] -/
#guard_msgs in
#print axioms OptByte.Repr.from_to

/-- info: 'Transmog.Test.Inductive.Mode.Repr.from_to' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Mode.Repr.from_to

/-- info: 'Transmog.Test.Inductive.Sign.Repr.from_to' does not depend on any axioms -/
#guard_msgs in
#print axioms Sign.Repr.from_to

end

/-! ## Errors -/

inductive E where
  | a
  | b (v : UInt8)

/-- error: unknown constructor `c` -/
#guard_msgs in
transmog E as [t : UInt8, v : UInt8] where
  | a => guard t = 0
  | c => v : UInt8 <= v

/-- error: constructor `b` expects 1 payload fields, but the repr clause provides 0 -/
#guard_msgs in
transmog E as [t : UInt8, v : UInt8] where
  | a => guard t = 0
  | b => t := 1

/-- error: don't know how to represent the following constructors of `E`: [E.b] -/
#guard_msgs in
transmog E as [t : UInt8, v : UInt8] where
  | a => guard t = 0

/-- error: duplicate constructor `a` -/
#guard_msgs in
transmog E as [t : UInt8, v : UInt8] where
  | a => guard t = 0
  | a => guard t = 1
  | b => v : UInt8 <= v

/-- error: enum repr can have at most one unguarded constructor, otherwise ambiguous -/
#guard_msgs in
transmog E as [t : UInt8, v : UInt8] where
  | a => t := 0
  | b => v : UInt8 <= v

/-- error: failed to infer writes from the guard, both sides are slot places -/
#guard_msgs in
transmog E as [t : UInt8, v : UInt8] where
  | a => guard t = v
  | b => v : UInt8 <= v

/--
error: conflicting writes to `t`: this write and an earlier one target the same bits with different values
-/
#guard_msgs in
transmog E as [t : UInt8, v : UInt8] where
  | a =>
    guard t = 0
    t := 1
  | b => v : UInt8 <= v

/--
error: every constructor of `E` is guarded, so the generated `fromRepr` needs `Inhabited E` for its fallback branch; add a `deriving Inhabited` clause, provide an instance, or leave one constructor unguarded
-/
#guard_msgs in
transmog E as [t : UInt8, v : UInt8] where
  | a => guard t = 0
  | b =>
    guard t = 1
    v : UInt8 <= v

-- A proof field has no runtime data; the failure is the elaborator's, on the field's universe.
inductive Proven where
  | a
  | b (v : UInt8) (h : True)

/-- error: invalid universe level, 0 is not greater than 0 -/
#guard_msgs in
transmog Proven as [t : UInt8, v : UInt8] where
  | a => guard t = 0
  | b =>
    v : UInt8 <= v
    h : True <= v

/-! ### Failures inside the generated definitions -/

-- These leave the codecs behind, so each uses a type of its own.

-- Two arms with the same guard cannot both round-trip.
inductive Twin where
  | a
  | b
deriving Inhabited

/--
error: failed to prove Transmog `DataRepr` round-trip obligation: goal constituents did not align; restate guard conjuncts in the same form as the field subtype properties, or provide `correct_by`
x✝ : Twin
⊢ False
-/
#guard_msgs in
transmog Twin as [t : UInt8] where
  | a => guard t = 0
  | b => guard t = 0

-- An equation the inference does not read leaves the slot at zero, and the round trip fails.
inductive Coerced where
  | a
  | b (v : UInt8)

/--
error: failed to prove Transmog `DataRepr` round-trip obligation: goal constituents did not align; restate guard conjuncts in the same form as the field subtype properties, or provide `correct_by`
x✝ : Coerced
⊢ False
-/
#guard_msgs in
transmog Coerced as [t : UInt8, v : UInt8] where
  | a => guard (t : UInt8) = 1
  | b => v : UInt8 <= v

inductive Disjunctive where
  | a
  | b (v : UInt8)

/--
error: failed to prove Transmog `DataRepr` round-trip obligation: goal constituents did not align; restate guard conjuncts in the same form as the field subtype properties, or provide `correct_by`
x✝ : Disjunctive
⊢ False
-/
#guard_msgs in
transmog Disjunctive as [t : UInt8, v : UInt8] where
  | a => guard t = 1 ∨ t = 2
  | b => v : UInt8 <= v

end Transmog.Test.Inductive
