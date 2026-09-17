/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
import Transmog

/-!
# Points in a compact array

The smallest complete use of the library.  A structure of two scalars is given a representation
in two slots and a packed byte layout, and a `CompactArray` then stores its values eight bytes
apiece.
-/

open Transmog

namespace Points

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

/-- info: [{ x := 10, y := 20 }] -/
#guard_msgs in
#eval points.toList

/-- info: 8 -/
#guard_msgs in
#eval points.data.size

/-- info: [{ x := 10, y := 20 }] -/
#guard_msgs in
#eval points.iter.toList

-- The array is updated in place through the layout, and iterated like any other.
/-- info: [{ x := 10, y := 21 }, { x := 3, y := 4 }] -/
#guard_msgs in
#eval ((points.push { x := 3, y := 4 }).set! 0 { x := 10, y := 21 }).toList

/-- info: 13 -/
#guard_msgs in
#eval (points.push { x := 3, y := 4 }).foldl (fun acc p => acc + p.x) 0

end Points
