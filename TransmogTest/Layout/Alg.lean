/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Transmog.DSL.Elab.LayoutAlg

/-!
# Tests for the layout algorithm

`computeLayout` is a pure computation on slot widths, so it is checked directly on the mode
matrix, apart from the syntax and the term assembly around it.
-/

namespace Transmog.Test.LayoutAlg

open Transmog.DSL.LayoutAlg

/-! ## Helpers -/

#guard alignUp 0 4 == 0
#guard alignUp 1 4 == 4
#guard alignUp 4 4 == 4
#guard alignUp 5 1 == 5
#guard alignUp 7 8 == 8

#guard ({ order := .c } : LayoutMode).effAlign 4 == 4
#guard ({ order := .c, fieldCap := some 2 } : LayoutMode).effAlign 4 == 2
#guard ({ order := .c, fieldCap := some 8 } : LayoutMode).effAlign 4 == 4

/-! ## Arrangement -/

/-- A one-byte, a four-byte and a two-byte slot, in declaration order. -/
meta def slots : Array PhysSlot := #[⟨0, 1, 1⟩, ⟨1, 4, 4⟩, ⟨2, 2, 2⟩]

#guard (SlotOrder.c.arrange id slots).map (·.idx) == #[0, 1, 2]
-- Descending alignment, declaration order among equals.
#guard (SlotOrder.auto.arrange id slots).map (·.idx) == #[1, 2, 0]
#guard (SlotOrder.auto.arrange (min · 2) slots).map (·.idx) == #[1, 2, 0]
#guard (SlotOrder.auto.arrange (fun _ => 1) slots).map (·.idx) == #[0, 1, 2]
-- The sort is stable.
#guard (SlotOrder.auto.arrange id #[⟨0, 2, 2⟩, ⟨1, 4, 4⟩, ⟨2, 2, 2⟩, ⟨3, 4, 4⟩]).map (·.idx) ==
  #[1, 3, 0, 2]

/-! ## The mode matrix on three slots -/

-- `C packed`: no padding at all.
#guard
  let l := computeLayout { order := .c, fieldCap := some 1 } slots
  l.entries == #[.slot 0, .slot 1, .slot 2] && l.size == 7 && l.align == 1

-- `C packed 2`: fields aligned to at most two bytes.
#guard
  let l := computeLayout { order := .c, fieldCap := some 2 } slots
  l.entries == #[.slot 0, .pad 1, .slot 1, .slot 2] && l.size == 8 && l.align == 2

-- `C align 1`: natural alignment, gap before the four-byte slot, tail to four bytes.
#guard
  let l := computeLayout { order := .c } slots
  l.entries == #[.slot 0, .pad 3, .slot 1, .slot 2, .pad 2] && l.size == 12 && l.align == 4

-- `C align 8`: the struct alignment is raised above the fields'.
#guard
  let l := computeLayout { order := .c, structFloor := 8 } slots
  l.entries == #[.slot 0, .pad 3, .slot 1, .slot 2, .pad 6] && l.size == 16 && l.align == 8

-- `auto packed 2`: reordered under the cap, no gaps, tail to two bytes.
#guard
  let l := computeLayout { order := .auto, fieldCap := some 2 } slots
  l.entries == #[.slot 1, .slot 2, .slot 0, .pad 1] && l.size == 8 && l.align == 2

-- `auto align 1`: reordered, no gaps, tail to four bytes.
#guard
  let l := computeLayout { order := .auto } slots
  l.entries == #[.slot 1, .slot 2, .slot 0, .pad 1] && l.size == 8 && l.align == 4

-- `auto align 8`: the seven bytes already fit an eight-byte struct.
#guard
  let l := computeLayout { order := .auto, structFloor := 8 } slots
  l.entries == #[.slot 1, .slot 2, .slot 0, .pad 1] && l.size == 8 && l.align == 8

/-! ## Placements -/

#guard (computeLayout { order := .c } slots).placements slots == #[(0, 0), (1, 4), (2, 8)]
#guard (computeLayout { order := .auto } slots).placements slots == #[(1, 0), (2, 4), (0, 6)]
#guard (computeLayout { order := .c, fieldCap := some 1 } slots).placements slots ==
  #[(0, 0), (1, 1), (2, 5)]

/-! ## Degenerate inputs -/

-- A single slot has no padding under natural alignment.
#guard
  let l := computeLayout { order := .c } #[⟨0, 8, 8⟩]
  l.entries == #[.slot 0] && l.size == 8 && l.align == 8

-- Under a floor above its width, a single slot gets a tail.
#guard
  let l := computeLayout { order := .c, structFloor := 4 } #[⟨0, 1, 1⟩]
  l.entries == #[.slot 0, .pad 3] && l.size == 4 && l.align == 4

end Transmog.Test.LayoutAlg
