/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL

/-!
# Tests for the representation specification

The slot list of a `transmog` declaration: the four scalar widths, bit ranges on slots and on
places, user properties, and the source types the command accepts.
-/

-- Deliberately ill-formed declarations follow.
set_option linter.hazel false

namespace Transmog.Test.Spec

open Transmog

@[expose] public section

/-! ## Scalar slots of every width -/

structure Four where
  a : UInt8
  b : UInt16
  c : UInt32
  d : UInt64

transmog Four as [a : UInt8, b : UInt16, c : UInt32, d : UInt64] where
  a : UInt8 <= a
  b : UInt16 <= b
  c : UInt32 <= c
  d : UInt64 <= d

example : DataRepr Four (UInt8 × UInt16 × UInt32 × UInt64) := inferInstance
example : Four.Repr.toRepr ⟨1, 2, 3, 4⟩ = (1, 2, 3, 4) := rfl
example : Four.Repr.fromRepr (1, 2, 3, 4) = ⟨1, 2, 3, 4⟩ := rfl

/-! ## Ranged slots -/

-- `[n]` is one bit, `[:n]` the low `n`, `[m:]` from bit `m` to the top, `[m:n]` a window,
-- and `[:]` the whole scalar, which is the same as no range at all.
structure Bits where
  one : { x : UInt8 // x.fitsBits 1 }
  low : { x : UInt8 // x.fitsBits 3 }
  high : { x : UInt8 // x.fitsBits 5 }
  mid : { x : UInt16 // x.fitsBits 4 }
  whole : UInt32

transmog Bits as
    [one : UInt8[5], low : UInt8[:3], high : UInt8[3:], mid : UInt16[2:6], whole : UInt32[:]] where
  one : { x : UInt8 // x.fitsBits 1 } <= one
  low : { x : UInt8 // x.fitsBits 3 } <= low
  high : { x : UInt8 // x.fitsBits 5 } <= high
  mid : { x : UInt16 // x.fitsBits 4 } <= mid
  whole : UInt32 <= whole

example : DataRepr Bits
    ({ one : UInt8 // UInt8.fitsBits 1 one } × { low : UInt8 // UInt8.fitsBits 3 low } ×
      { high : UInt8 // UInt8.fitsBits 5 high } × { mid : UInt16 // UInt16.fitsBits 4 mid } ×
      UInt32) :=
  inferInstance

-- A ranged slot holds its value in the low bits, whatever the range's start.
example : Bits.Repr.toRepr ⟨⟨1, by decide⟩, ⟨5, by decide⟩, ⟨31, by decide⟩, ⟨15, by decide⟩, 9⟩ =
    (⟨1, by decide⟩, ⟨5, by decide⟩, ⟨31, by decide⟩, ⟨15, by decide⟩, 9) := rfl

/-! ## Places with ranges inside slots -/

structure Nibbles where
  lo : { x : UInt8 // x.fitsBits 4 }
  hi : { x : UInt8 // x.fitsBits 4 }
deriving DecidableEq

transmog Nibbles as [r : UInt8] where
  lo : { x : UInt8 // x.fitsBits 4 } <= r[:4]
  hi : { x : UInt8 // x.fitsBits 4 } <= r[4:]

example : Nibbles.Repr.toRepr ⟨⟨0xA, by decide⟩, ⟨0xB, by decide⟩⟩ = 0xBA := by decide
example : Nibbles.Repr.fromRepr 0xBA = ⟨⟨0xA, by decide⟩, ⟨0xB, by decide⟩⟩ := by decide

/-! ## Slot properties -/

abbrev Ptr := { p : UInt32 // p ≠ 0 ∧ p.fitsBits 31 }

transmog Ptr as [p : UInt32[0:31] // p ≠ 0]

-- The user property comes first, then the range-induced fit.
example : DataRepr Ptr { p : UInt32 // p ≠ 0 ∧ UInt32.fitsBits 31 p } := inferInstance

structure Wrapped where
  p : Ptr

transmog Wrapped as [r : UInt32 // r ≠ 0 ∧ UInt32.fitsBits 31 r] where
  p : Ptr <= r

example : DataRepr Wrapped { r : UInt32 // r ≠ 0 ∧ UInt32.fitsBits 31 r } := inferInstance

end

/-! ## Errors -/

structure Q where
  x : UInt8

/-- error: invalid bit range, expected stop ≤ 8 -/
#guard_msgs in
transmog Q as [r : UInt8[:9]] where
  x : UInt8 <= r

/-- error: invalid bit range, expected start < stop -/
#guard_msgs in
transmog Q as [r : UInt8[4:2]] where
  x : UInt8 <= r

/-- error: invalid bit range, expected start < stop -/
#guard_msgs in
transmog Q as [r : UInt8[3:3]] where
  x : UInt8 <= r

/-- error: invalid bit range, expected start ≥ 2 -/
#guard_msgs in
transmog Q as [r : UInt8[2:6]] where
  x : UInt8 <= r[0:2]

/-- error: invalid bit range, expected stop ≤ 6 -/
#guard_msgs in
transmog Q as [r : UInt8[2:6]] where
  x : UInt8 <= r[4:7]

/-- error: invalid representation slot type, expected UInt8, UInt16, UInt32, or UInt64 -/
#guard_msgs in
transmog Q as [r : Nat] where
  x : UInt8 <= r

/-- error: invalid representation slot type, expected UInt8, UInt16, UInt32, or UInt64 -/
#guard_msgs in
transmog Q as [r : Int8] where
  x : UInt8 <= r

/-- error: Unknown constant `NoSuchType` -/
#guard_msgs in
transmog Q as [r : NoSuchType] where
  x : UInt8 <= r

/-- error: duplicate representation slot `r` -/
#guard_msgs in
transmog Q as [r : UInt8, r : UInt8] where
  x : UInt8 <= r

/-- error: unknown representation slot `s` -/
#guard_msgs in
transmog Q as [r : UInt8] where
  x : UInt8 <= s

-- A place inside a ranged slot names bits of the scalar, so a slot range starting above bit
-- zero cannot host places: their writes do not fit the slot's own range-induced type.
structure Inner where
  a : { x : UInt8 // x.fitsBits 2 }
  b : { x : UInt8 // x.fitsBits 2 }

/--
error: failed to prove Transmog `DataRepr` subtype obligation
a b : { x // UInt8.fitsBits 2 x }
this✝¹ : UInt8.fitsBits 2 a.val
this✝ : UInt8.fitsBits 2 b.val
⊢ UInt8.fitsBits 4 (UInt8.insertSlice 4 6 (UInt8.insertSlice 2 4 0 a.val) b.val)
-/
#guard_msgs in
transmog Inner as [r : UInt8[2:6]] where
  a : { x : UInt8 // x.fitsBits 2 } <= r[2:4]
  b : { x : UInt8 // x.fitsBits 2 } <= r[4:6]

/-! ### Source types -/

/--
error: type expected, got
  3
-/
#guard_msgs in
transmog (3 : Nat) as [r : UInt8]

/--
error: expected a type constant applied to its arguments, got
  Nat → Nat
-/
#guard_msgs in
transmog (Nat → Nat) as [r : UInt8]

/--
error: `Option` has parameters; a type with parameters is represented one instantiation at a time, so apply it to its arguments
-/
#guard_msgs in
transmog Option as [r : UInt8]

/--
error: the type is not fully determined; the representation belongs to one instantiation, so every argument must be given
-/
#guard_msgs in
transmog Option _ as [t : UInt8, v : UInt8] where
  | none => guard t = 0
  | some =>
    t := 1
    val : UInt8 <= v

/-- error: Unknown identifier `β` -/
#guard_msgs in
transmog Option β as [t : UInt8, v : UInt8] where
  | none => guard t = 0
  | some =>
    t := 1
    val : UInt8 <= v

inductive Tagged : Bool → Type where
  | yes : Tagged true
  | no : Tagged false

/-- error: `Tagged` is an indexed family, which is not supported -/
#guard_msgs in
transmog Tagged true as [t : UInt8] where
  | yes => guard t = 1
  | no => t := 0

/-- error: can't transmogrify recursive Lean types -/
#guard_msgs in
transmog Nat as [t : UInt8] where
  | zero => guard t = 0
  | succ => n : Nat <= t

end Transmog.Test.Spec
