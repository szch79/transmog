/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL

/-!
# The combined declaration form under `replace_runtime`

The `deriving` clause of a `transmog enum` declaration runs after the clause, so the derived
instances are compiled against the word without the stale-code error a `deriving` on the
`inductive` itself would raise, and the verification pass makes any remaining access to the
object layout in this module a compile error.  A private constructor and a dotted type name
with a layout go through the same path.
-/

set_option experimental.transmog.replaceRuntime true
-- A deliberately private declaration follows.
set_option linter.hazel false

open Transmog

namespace Transmog.Test.RuntimeRepr.Decl

@[expose] public section

abbrev Ptr := { p : UInt32 // p ≠ 0 ∧ p.fitsBits 31 }

transmog Ptr as [p : UInt32[0:31] // p ≠ 0]

transmog enum Node as [n : UInt32[0:31]] where
  | sink => guard n = 0
  | inode (p : Ptr <= n)
replace_runtime
deriving Repr, BEq, DecidableEq, Hashable

/-- The fifth node. -/
def fifth : Node := .inode ⟨5, by decide⟩

/-- info: (Transmog.Test.RuntimeRepr.Decl.Node.inode 5, Transmog.Test.RuntimeRepr.Decl.Node.sink) -/
#guard_msgs in
#eval (fifth, Node.sink)

/-- info: (true, false, true, false) -/
#guard_msgs in
#eval (fifth == fifth, fifth == .sink, decide (fifth = fifth), decide (fifth = .sink))

/-- info: true -/
#guard_msgs in
#eval hash fifth == hash (Node.inode ⟨5, by decide⟩) && hash fifth != hash Node.sink

-- The representation of a value is the word the compiler holds.
/-- info: 5 -/
#guard_msgs in
#eval (DataRepr.toRepr fifth).val

/-! ## A private constructor -/

-- An exposed definition cannot name a private constructor, so the pins are evaluations.
transmog enum Sec as [t : UInt8, a : UInt8] where
  | nothing => guard t = 0
  | private just (v : UInt8 <= a) => t := 1
replace_runtime

/-- info: (1, 2) -/
#guard_msgs in
#eval DataRepr.toRepr (Sec.just 2)

/-- info: 10 -/
#guard_msgs in
#eval match Sec.Repr.fromRepr (1, 9) with
  | .nothing => 0
  | .just v => v.toNat + 1

/-! ## A dotted name with a layout -/

transmog enum Deep.Node as [n : UInt32[0:31]] where
  | sink => guard n = 0
  | inode (p : Ptr <= n)
replace_runtime
derive_layout C packed
deriving DecidableEq, Repr

/-- info: (Transmog.Test.RuntimeRepr.Decl.Deep.Node.inode 5, 4) -/
#guard_msgs in
#eval (Deep.Node.inode ⟨5, by decide⟩, (HasLayout.layout (α := Deep.Node)).size)

end

/-! ## A private type cannot be word-backed -/

/--
error: `Hidden` is private, and so would be the `csimp` lemmas that `replace_runtime` emits, which must be public; make the type public, in a `public section` and without `private`
-/
#guard_msgs(error, drop all) in
transmog enum Hidden as [t : UInt8, a : UInt8] where
  | nothing => guard t = 0
  | just (v : UInt8 <= a) => t := 1
replace_runtime
deriving Repr

end Transmog.Test.RuntimeRepr.Decl
