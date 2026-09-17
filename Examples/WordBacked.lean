/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
import Transmog

/-!
# Edges carried as machine words

The `Node` and `Edge` types of the BDD example have single-word representations, but a value of
either is still a heap-allocated constructor object until it is stored into a `CompactArray`.
The experimental `replace_runtime` clause closes that gap.  The compiler then carries every
`Node` and every `Edge` as its boxed representation word, so that constructing one is a boxing,
matching on one is an unboxing and a comparison, and the representation round trip is the
identity.  The logical side is untouched, so the code below still pattern matches on
`Node.sink` and `Node.inode p` and still gets the round-trip theorems.  Both types are declared
with the combined forms, whose `deriving` clause runs after the `replace_runtime` clause, so the
derived instances are compiled against the word.

`Edge` is a structure, which the compiler classifies as a definite heap reference, so its clause
needs `transmog.replaceRuntime.overrideClassification`, and the file acknowledges the
experimental status of both clauses with `experimental.transmog.replaceRuntime`.
-/

set_option experimental.transmog.replaceRuntime true
set_option transmog.replaceRuntime.overrideClassification true

open Transmog

namespace WordBacked

abbrev Ptr := { p : UInt32 // p ≠ 0 ∧ p.fitsBits 31 }

transmog Ptr as [p : UInt32[0:31] // p ≠ 0]

transmog enum Node as [n : UInt32[0:31]] where
  | sink => guard n = 0
  | inode (p : Ptr <= n)
replace_runtime
deriving DecidableEq, Repr

transmog struct Edge as [r : UInt32] where
  compl : Bool <= lsbAsBool r[0]
  node : Node <= r[1:32]
replace_runtime
derive_layout C packed
deriving DecidableEq, Repr

/-- The edge to the terminal denoting the constant `b`. -/
def Edge.const (b : Bool) : Edge := ⟨b, .sink⟩

/-- The pointer an edge carries, or `0` for the terminal. -/
def Edge.target : Edge → UInt32
  | ⟨_, .sink⟩ => 0
  | ⟨_, .inode p⟩ => p.val

/-- An edge to the fifth node, complemented, whose word is `5 <<< 1 ||| 1`. -/
def edge : Edge := { compl := true, node := .inode ⟨5, by decide⟩ }

-- The representation of a value is the word the compiler already holds.
/-- info: 11 -/
#guard_msgs in
#eval (DataRepr.toRepr edge : UInt32)

/-- info: (5, 0) -/
#guard_msgs in
#eval (edge.target, (Edge.const false).target)

/-- info: { compl := true, node := WordBacked.Node.inode 5 } -/
#guard_msgs in
#eval (DataRepr.fromRepr 11 : Edge)

-- A `CompactArray` of edges stores the same words it carries.
/-- info: [11, 0, 1] -/
#guard_msgs in
#eval [edge, .const false, .const true].toCompactArray.toList.map fun e =>
  (DataRepr.toRepr e : UInt32)

end WordBacked
