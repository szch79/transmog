/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL

/-!
# Tests for niches

A slot value outside a payload's range marks a constructor, so an `Option` costs no extra byte.
The range has to be stated on the slot so that the representation composes, and the three ways
of getting it wrong are pinned.
-/

-- Deliberately ill-formed declarations follow.
set_option linter.hazel false

namespace Transmog.Test.Niche

open Transmog

@[expose] public section

-- A `Bool` takes two of the byte's values and the third marks `none`.
transmog Option Bool as [r : UInt8 // r ≤ 2] where
  | none => guard r = 2
  | some => val : Bool <= lsbAsBool r

example : (DataRepr.toRepr (some true)).val = 1 := rfl
example : (DataRepr.toRepr (some false)).val = 0 := rfl
example : (DataRepr.toRepr (none : Option Bool)).val = 2 := rfl
example : DataRepr.fromRepr (α := Option Bool) ⟨2, by decide⟩ = none := by decide
example : DataRepr.fromRepr (α := Option Bool) ⟨1, by decide⟩ = some true := by decide

-- A field whose carrier is a subtype of the slot scalar is placed through that carrier; the
-- guard leaves exactly the carrier's range to the payload.
transmog Option (Option Bool) as [r : UInt8 // r ≤ 3] where
  | none => guard r = 3
  | some => val : Option Bool <= r

example : (DataRepr.toRepr (some (some true))).val = 1 := rfl
example : (DataRepr.toRepr (some (none : Option Bool))).val = 2 := rfl
example : (DataRepr.toRepr (none : Option (Option Bool))).val = 3 := rfl
example : DataRepr.fromRepr (α := Option (Option Bool)) ⟨2, by decide⟩ = some none := by decide

-- Two such fields share a byte, each in a two-bit slice; the slice's `fitsBits 2` and the
-- carrier's `≤ 3` are the same range, read in both directions.
structure Pair where
  a : Option (Option Bool)
  b : Option (Option Bool)
deriving DecidableEq

transmog Pair as [r : UInt8] where
  a : Option (Option Bool) <= r[0:2]
  b : Option (Option Bool) <= r[2:4]

example : DataRepr.toRepr (Pair.mk (some none) none) = 0b1110 := rfl
example : (DataRepr.fromRepr 0b1110 : Pair) = ⟨some none, none⟩ := by decide

-- The nonzero pointer leaves `0` to `none`, and the word above the pointers to the outer `none`.
abbrev Ptr := { p : UInt32 // p ≠ 0 ∧ p.fitsBits 31 }

transmog Ptr as [p : UInt32[0:31] // p ≠ 0]

transmog Option Ptr as [n : UInt32[0:31]] where
  | none => guard n = 0
  | some => val : Ptr <= n

example : (DataRepr.toRepr (none : Option Ptr)).val = 0 := rfl
example : (DataRepr.toRepr (some (⟨5, by decide⟩ : Ptr))).val = 5 := rfl
example : DataRepr.fromRepr (α := Option Ptr) ⟨5, by decide⟩ = some ⟨5, by decide⟩ := by decide

transmog Option (Option Ptr) as [n : UInt32 // n ≤ 2147483648] where
  | none => guard n = 2147483648
  | some => val : Option Ptr <= n

example : (DataRepr.toRepr (none : Option (Option Ptr))).val = 2147483648 := rfl
example : (DataRepr.toRepr (some (none : Option Ptr))).val = 0 := rfl
example : (DataRepr.toRepr (some (some (⟨5, by decide⟩ : Ptr)))).val = 5 := rfl

-- The two `Option` nestings render alike and are told apart by an index; the two pointer
-- options differ in their carriers.
/--
info: [Transmog.Test.Niche.instDataReprOptionBoolSubtypeUInt8LeOfNat_transmogTest.from_to,
 Transmog.Test.Niche.instDataReprOptionBoolSubtypeUInt8LeOfNat_transmogTest_1.from_to,
 Transmog.Test.Niche.instDataReprOptionPtrSubtypeUInt32FitsBitsOfNatNat.from_to,
 Transmog.Test.Niche.instDataReprOptionPtrSubtypeUInt32LeOfNat.from_to,
 Transmog.Test.Niche.Pair.Repr.from_to,
 Transmog.Test.Niche.Ptr.Repr.from_to]
-/
#guard_msgs in
run_cmd do
  let env ← Lean.getEnv
  let names := env.constants.map₂.toList.filterMap fun (n, _) =>
    if (`Transmog.Test.Niche).isPrefixOf n && n.getString! == "from_to" then some n else none
  Lean.logInfo m!"{names.toArray.qsort Lean.Name.lt}"

/--
info: 'Transmog.Test.Niche.instDataReprOptionPtrSubtypeUInt32LeOfNat.from_to' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms instDataReprOptionPtrSubtypeUInt32LeOfNat.from_to

end

/-! ## Errors -/

-- The declarations below fail inside a generated definition, whose recovery on this toolchain
-- adds a kernel diagnostic of its own.
public section

-- The payload's range is not stated on the slot.
structure Loose where
  v : Option Bool

/--
error: failed to prove Transmog `DataRepr` subtype obligation
repr✝ : UInt8
r : UInt8 := repr✝
⊢ r ≤ 2
---
error: (kernel) declaration has metavariables 'Transmog.Test.Niche.Loose.Repr.fromRepr'
-/
#guard_msgs in
transmog Loose as [r : UInt8] where
  v : Option Bool <= r

-- The niche lies inside the payload's range.
inductive Marked where
  | mark
  | held (v : Option Bool)

/--
error: failed to prove Transmog `DataRepr` subtype obligation
repr✝ : { r // r ≤ 3 }
r : UInt8
property✝ : r ≤ 3
h✝ : ¬r = 1
⊢ r ≤ 2
---
error: (kernel) declaration has metavariables 'Transmog.Test.Niche.Marked.Repr.fromRepr'
-/
#guard_msgs in
transmog Marked as [r : UInt8 // r ≤ 3] where
  | mark => guard r = 1
  | held => v : Option Bool <= r

-- A three-valued carrier in a two-bit slice.
structure Narrow where
  a : Option Bool

/--
error: failed to prove Transmog `DataRepr` subtype obligation
repr✝ : UInt8
r : UInt8 := repr✝
this✝ : UInt8.fitsBits 2 ⟨UInt8.extractSlice 0 2 r, ⋯⟩.val
⊢ ⟨UInt8.extractSlice 0 2 r, ⋯⟩.val ≤ 2
---
error: (kernel) declaration has metavariables 'Transmog.Test.Niche.Narrow.Repr.fromRepr'
-/
#guard_msgs in
transmog Narrow as [r : UInt8] where
  a : Option Bool <= r[0:2]

end

end Transmog.Test.Niche
