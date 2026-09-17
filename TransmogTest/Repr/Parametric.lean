/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL

/-!
# Tests for instantiations of parametric types

A type with parameters is represented one instantiation at a time.  The instantiation has no
namespace of its own, so its package hangs off the instance name, and each instantiation gets
its own instance.
-/

-- Deliberately ill-formed declarations follow.
set_option linter.hazel false

namespace Transmog.Test.Parametric

open Transmog

@[expose] public section

abbrev Ptr := { p : UInt32 // p ≠ 0 ∧ p.fitsBits 31 }

transmog Ptr as [p : UInt32[0:31] // p ≠ 0]

inductive Node (α : Type u) where
  | sink
  | inode (p : α)
deriving DecidableEq

transmog Node Ptr as [n : UInt32[0:31]] where
  | sink => guard n = 0
  | inode =>
    p : Ptr <= n

structure Edge (α : Type u) where
  compl : Bool
  node : Node α
deriving DecidableEq

transmog Edge Ptr as [r : UInt32] where
  compl : Bool <= lsbAsBool r[0]
  node : Node Ptr <= r[1:32]

-- The package hangs off the instance name.
example : DataRepr (Node Ptr) { n : UInt32 // UInt32.fitsBits 31 n } := inferInstance
example : (instDataReprNodePtrSubtypeUInt32FitsBitsOfNatNat.toRepr .sink).val = 0 := rfl
example : (DataRepr.toRepr (Node.inode (⟨2, by decide⟩ : Ptr))).val = 2 := rfl

-- The uncomplemented edge to node `2` is the word `2 <<< 1`.
example : DataRepr.toRepr (⟨false, .inode ⟨2, by decide⟩⟩ : Edge Ptr) = 4 := by decide
example : (DataRepr.fromRepr 5 : Edge Ptr) = ⟨true, .inode ⟨2, by decide⟩⟩ := by decide

-- A second instantiation of the same type gets a package and an instance of its own.
transmog Node Bool as [t : UInt8, b : UInt8] where
  | sink => guard t = 0
  | inode =>
    t := 1
    p : Bool <= lsbAsBool b

example : DataRepr (Node Bool) (UInt8 × UInt8) := inferInstance
example : DataRepr.toRepr (Node.inode true) = (1, 1) := rfl
example : (DataRepr.fromRepr (1, 1) : Node Bool) = .inode true := by decide

-- A type from the standard library, instantiated; its instance name carries the package.
transmog Option UInt8 as [t : UInt8, v : UInt8] where
  | none => guard t = 0
  | some =>
    t := 1
    val : UInt8 <= v

example : DataRepr (Option UInt8) (UInt8 × UInt8) := inferInstance
example : DataRepr.toRepr (some (7 : UInt8)) = (1, 7) := rfl
example : (DataRepr.fromRepr (1, 7) : Option UInt8) = some 7 := by decide

/-- info: Transmog.Test.Parametric.instDataReprOptionUInt8Prod_transmogTest.toRepr : Option UInt8 → UInt8 × UInt8 -/
#guard_msgs in
#check instDataReprOptionUInt8Prod_transmogTest.toRepr

-- Nested instantiations render alike but get distinct packages.
structure Box (α : Type u) where
  val : α
deriving DecidableEq

transmog Box UInt8 as [b : UInt8] where
  val : UInt8 <= b

transmog Box (Box UInt8) as [b : UInt8] where
  val : Box UInt8 <= b

example : DataRepr (Box UInt8) UInt8 := inferInstance
example : DataRepr (Box (Box UInt8)) UInt8 := inferInstance
example : DataRepr.toRepr (Box.mk (Box.mk (7 : UInt8))) = 7 := rfl
example : (DataRepr.fromRepr 7 : Box (Box UInt8)) = ⟨⟨7⟩⟩ := by decide

-- Every package of this module, named after its instance; the second `Box` gets an index, and
-- the instantiation of library types alone gets the package suffix Lean adds to keep instance
-- names unique across packages.
/--
info: [Transmog.Test.Parametric.instDataReprBoxUInt8.toRepr,
 Transmog.Test.Parametric.instDataReprBoxUInt8_1.toRepr,
 Transmog.Test.Parametric.instDataReprEdgePtrUInt32.toRepr,
 Transmog.Test.Parametric.instDataReprNodeBoolProdUInt8.toRepr,
 Transmog.Test.Parametric.instDataReprNodePtrSubtypeUInt32FitsBitsOfNatNat.toRepr,
 Transmog.Test.Parametric.instDataReprOptionUInt8Prod_transmogTest.toRepr,
 Transmog.Test.Parametric.Ptr.Repr.toRepr]
-/
#guard_msgs in
run_cmd do
  let env ← Lean.getEnv
  let names := env.constants.map₂.toList.filterMap fun (n, _) =>
    if (`Transmog.Test.Parametric).isPrefixOf n && n.getString! == "toRepr" then some n else none
  Lean.logInfo m!"{names.toArray.qsort Lean.Name.lt}"

end

/-! ## Errors -/

/--
error: field `p` of `Node.inode` has type
  Ptr
but is declared with type
  UInt32
-/
#guard_msgs in
transmog Node Ptr as [n : UInt32] where
  | sink => guard n = 0
  | inode =>
    p : UInt32 <= n

-- A word-backed representation belongs to the type, not to one of its instantiations.
public section

/--
error: `Node` has parameters, indices or universe parameters, which a word-backed representation does not support; the compiler represents an inductive type the same way for all of its instantiations, so none of them can be word-backed on its own
-/
#guard_msgs in
transmog Node UInt8 as [t : UInt8, v : UInt8] where
  | sink => guard t = 0
  | inode =>
    t := 1
    p : UInt8 <= v
  replace_runtime

end

end Transmog.Test.Parametric
