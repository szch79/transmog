/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Transmog.Init
/-!
# Layout algorithms

The two intermediate data structures between the repr slots and the
emitted `Layout` term: `LayoutMode` is the validated request an algorithm
receives (with `PhysSlot` the slots as it sees them), and `PhysLayout` is
the physical arrangement it decides, with padding explicit.  The
algorithms are pure `Nat` computations, so adding a new strategy means
adding a case here and a piece of syntax; the assembly codegen is
untouched.
-/

public meta section

namespace Transmog.DSL.LayoutAlg

/-! ## Algorithm input -/

/--
Slot ordering strategy: `c` keeps declaration order; `auto` reorders
by descending effective alignment, preserving declaration order for ties.
-/
inductive SlotOrder where
  | c
  | auto
deriving Inhabited, Repr, BEq

/--
A validated layout request: the independent axes a layout algorithm is
characterized by.  `fieldCap` caps every field's effective alignment
(`packed n`; `none` keeps natural alignment); `structFloor` raises the
struct alignment (`align n`).  The surface grammar allows only one of the
two to deviate from its default, but the algorithms treat them uniformly.
-/
structure LayoutMode where
  order : SlotOrder
  fieldCap : Option Nat := none
  structFloor : Nat := 1
deriving Inhabited, Repr

/-- The effective alignment of a field with natural alignment `natAlign`. -/
def LayoutMode.effAlign (mode : LayoutMode) (natAlign : Nat) : Nat :=
  match mode.fieldCap with
  | .some cap => min natAlign cap
  | .none => natAlign

/--
One representation slot as the layout algorithms see it: its index in
the declared slot list, its scalar width in bytes, and its natural
alignment (equal to the width for the `UIntN` scalars).
-/
structure PhysSlot where
  idx : Nat
  byteSize : Nat
  natAlign : Nat
deriving Inhabited, Repr

/-! ## Algorithm output -/

/--
One entry of a physical layout: a declared repr slot, or explicit
padding bytes.
-/
inductive PhysEntry where
  | slot (idx : Nat)
  | pad (bytes : Nat)
deriving Inhabited, Repr, BEq

/--
A computed physical layout: the entries in physical byte order with
padding explicit, plus the total size and struct alignment.  Offsets are
the entries' prefix sums (`placements`); the subsequence of `slot`
entries is the physical-to-declared index mapping, whose inverse is the
section used when emitting the reorder retract.
-/
structure PhysLayout where
  entries : Array PhysEntry
  size : Nat
  align : Nat
deriving Inhabited, Repr

-- `Id.run` supplies the monad expected by the following do block.
set_option linter.hazel.style.preferDotNotation false in
/--
The physical slots as `(declared index, byte offset)` pairs in
physical order, recovered from the entries' prefix sums.
-/
def PhysLayout.placements (l : PhysLayout) (phys : Array PhysSlot) :
    Array (Nat × Nat) := Id.run do
  let mut placed := #[]
  let mut cur := 0
  for e in l.entries do
    match e with
    | .slot idx =>
      placed := placed.push (idx, cur)
      cur := cur + phys[idx]!.byteSize
    | .pad n => cur := cur + n
  return placed

/-! ## Algorithms -/

/-- Round `x` up to the next multiple of `a` (`a > 0`). -/
def alignUp (x a : Nat) : Nat := (x + a - 1) / a * a

def SlotOrder.arrange (order : SlotOrder) (effAlign : Nat → Nat)
    (slots : Array PhysSlot) : Array PhysSlot :=
  match order with
  | .c => slots
  | .auto =>
    -- Distinct `idx` values make the lexicographic sort a stable
    -- descending-alignment sort.
    slots.qsort fun a b =>
      effAlign a.natAlign > effAlign b.natAlign ||
        (effAlign a.natAlign == effAlign b.natAlign && a.idx < b.idx)

-- `Id.run` supplies the monad expected by the following do block.
set_option linter.hazel.style.preferDotNotation false in
/--
Bump-allocate the slots in the mode's order at effective-alignment
offsets, recording padding gaps explicitly; struct alignment is the max
field alignment raised to the mode's floor; the tail is padded to the
struct alignment.
-/
def computeLayout (mode : LayoutMode) (slots : Array PhysSlot) :
    PhysLayout := Id.run do
  let ordered := mode.order.arrange mode.effAlign slots
  let mut entries := #[]
  let mut cur := 0
  let mut structAlign := mode.structFloor
  for s in ordered do
    let fa := max 1 (mode.effAlign s.natAlign)
    let off := alignUp cur fa
    if cur < off then
      entries := entries.push (.pad (off - cur))
    entries := entries.push (.slot s.idx)
    cur := off + s.byteSize
    structAlign := max structAlign fa
  let size := alignUp cur structAlign
  if cur < size then
    entries := entries.push (.pad (size - cur))
  return { entries, size, align := structAlign }

end Transmog.DSL.LayoutAlg

end -- public meta section
