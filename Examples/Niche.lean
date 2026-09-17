/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
import Transmog

/-!
# Niches

A niche is a bit pattern of a payload's storage that no value of the payload takes.  A sum type
wrapping the payload can mark its other constructors with such patterns, and then the tag costs
nothing beyond the payload itself.  Rust's layout algorithm discovers niches on its own, which
is why `Option<&T>` is one pointer wide and `Option<bool>` is one byte.  In Transmog the
invariant that creates a niche is stated on the slot, and the round-trip theorem checks that
the marks fall outside the payload's range, so the same optimizations are available and
verified.

Niches come from three sources, each shown below: an invariant of the payload such as a pointer
being nonzero or an index staying below a sentinel, an enumeration with fewer values than its
byte has patterns, and a component of a compound payload that already carries one.  The last
section packs niche-bearing values into bit slices, which is where stating the range pays off
twice.
-/

open Transmog

namespace Niche

/-!
## A pointer is never null

The oldest niche.  A pointer into an array is one-based here, so `0` is free, and `Option Ptr`
stores `none` as `0`, as `Option<NonNull<T>>` or `Option<NonZeroU32>` does in Rust.
-/

abbrev Ptr := { p : UInt32 // p ≠ 0 }

transmog Ptr as [p : UInt32 // p ≠ 0]

transmog Option Ptr as [p : UInt32] where
  | none => guard p = 0
  | some => val : Ptr <= p

example : DataRepr.toRepr (none : Option Ptr) = 0 := rfl
example : DataRepr.toRepr (some (⟨7, by decide⟩ : Ptr)) = 7 := rfl
example : DataRepr.fromRepr (α := Option Ptr) 0 = none := by decide

/-!
## An index stays below a sentinel

Zero is a perfectly good array index, so an index type instead gives up its largest value, in
the manner of `NonMaxU32` and of the index newtypes inside `rustc`.  `Option Idx` then stores
`none` as `0xFFFFFFFF`, and a zero-based index keeps its natural encoding.
-/

abbrev Idx := { i : UInt32 // i ≠ 0xFFFFFFFF }

transmog Idx as [i : UInt32 // i ≠ 0xFFFFFFFF]

transmog Option Idx as [i : UInt32] where
  | none => guard i = 0xFFFFFFFF
  | some => val : Idx <= i

example : DataRepr.toRepr (none : Option Idx) = 0xFFFFFFFF := rfl
example : DataRepr.toRepr (some (⟨0, by decide⟩ : Idx)) = 0 := rfl
example : DataRepr.fromRepr (α := Option Idx) 3 = some ⟨3, by decide⟩ := by decide

/-!
## An enumeration leaves most patterns unused

`Ordering` has three values and a byte has 256 patterns, so `Option Ordering` marks `none` with
the fourth pattern and `Option (Option Ordering)` with the fifth, still in one byte.  Every
wrapper takes one more pattern from the same byte, exactly as `Option<Option<bool>>` stays one
byte in Rust.  The bound `o ≤ 2` on the slot is the statement that lets the outer declaration
know which patterns are free.
-/

transmog Ordering as [o : UInt8 // o ≤ 2] where
  | lt => guard o = 0
  | eq => guard o = 1
  | gt => guard o = 2

transmog Option Ordering as [o : UInt8 // o ≤ 3] where
  | none => guard o = 3
  | some => val : Ordering <= o

transmog Option (Option Ordering) as [o : UInt8 // o ≤ 4] where
  | none => guard o = 4
  | some => val : Option Ordering <= o

example : (DataRepr.toRepr (some (some Ordering.gt))).val = 2 := rfl
example : (DataRepr.toRepr (some (none : Option Ordering))).val = 3 := rfl
example : (DataRepr.toRepr (none : Option (Option Ordering))).val = 4 := rfl
example : DataRepr.fromRepr (α := Option (Option Ordering)) ⟨1, by decide⟩ =
    some (some .eq) := by decide

/-!
## A compound payload carries the niche of one component

Rust stores the tag of `Option<(bool, u32)>` in the `bool`.  Here the pair is written
componentwise, the flag byte states its range, and `Option (Bool × UInt32)` marks `none` with
the flag value `2` while the second slot is left alone.
-/

transmog Option (Bool × UInt32) as [f : UInt8 // f ≤ 2, v : UInt32] where
  | none => guard f = 2
  | some => val : (Bool × UInt32) <= (lsbAsBool f, v)

example : (DataRepr.toRepr (some ((true, 9) : Bool × UInt32))).1.val = 1 := rfl
example : (DataRepr.toRepr (some ((true, 9) : Bool × UInt32))).2 = 9 := rfl
example : (DataRepr.toRepr (none : Option (Bool × UInt32))).1.val = 2 := rfl
example : DataRepr.fromRepr (α := Option (Bool × UInt32)) (⟨0, by decide⟩, 4) =
    some (false, 4) := by decide

/-!
## Niches fit into bit slices

The range `o ≤ 3` of `Option Ordering` is exactly the range of a two-bit slice, so a byte holds
four of them.  Rust stops at byte granularity; here a range stated on a slot carries over to a
slice of the same range, and the four-valued field costs two bits and no more.
-/

/-- Four optional comparison results, two bits each. -/
structure Quad where
  a : Option Ordering
  b : Option Ordering
  c : Option Ordering
  d : Option Ordering
deriving DecidableEq

transmog Quad as [r : UInt8] where
  a : Option Ordering <= r[0:2]
  b : Option Ordering <= r[2:4]
  c : Option Ordering <= r[4:6]
  d : Option Ordering <= r[6:8]
derive_layout C packed

example : (HasLayout.layout (α := Quad)).size = 1 := rfl
example : DataRepr.toRepr { a := some .lt, b := none, c := some .gt, d := some .eq : Quad } =
    0b01101100 := rfl
example : (DataRepr.fromRepr 0b01101100 : Quad) =
    { a := some .lt, b := none, c := some .gt, d := some .eq } := by decide

-- Eight quads occupy eight bytes.
/-- info: 8 -/
#guard_msgs in
#eval (List.replicate 8 { a := some .lt, b := none, c := some .gt, d := some .eq : Quad })
  |>.toCompactArray.data.size

end Niche
