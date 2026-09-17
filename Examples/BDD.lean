/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
import Transmog

/-!
# Binary decision diagrams over a packed node array

A binary decision diagram (BDD) branches on a Boolean variable at each internal node.  The high
edge selects the branch where the variable is true and the low edge the branch where it is
false.  This example stores the internal nodes of a diagram in a `CompactArray`, twelve bytes
each, and carries edges as single 32-bit words.

```text
InternalNode (12 bytes; byte offsets increase to the right)

byte  0                   4                   8                  12
      +-------------------+-------------------+-------------------+
      | var : UInt32      | hi : UInt32       | lo : UInt32       |
      +-------------------+-------------------+-------------------+

Each edge word (bits shown from most to least significant)

bit   31                                               1     0
      +------------------------------------------------+-----+
      | Node representation (31 bits)                  |compl|
      +------------------------------------------------+-----+
        0  = sink                                        1 bit
        p  = inode p, where 0 < p < 2^31
```

The terminal is represented directly in an edge, as node representation `0`, and needs no entry
in the array.  Pointers are one-based, so pointer `p` addresses array element `p - 1`.  The
complement bit negates the function an edge denotes; with the uncomplemented terminal denoting
`false`, the edge words `0` and `1` denote `false` and `true`.

The `transmog` declarations below describe this layout once.  Transmog generates the conversions
between the Lean types and the words, proves that they round-trip, and derives the byte layout
that `CompactArray` stores; user code keeps pattern matching on `Node.sink` and `Node.inode p`.
The second half of the file builds a small diagram in the array and evaluates it.
-/

open Transmog

namespace BDD

/-! ## The layout -/

/-- A one-based index into the node array, kept below `2^31` so that it packs beside a bit. -/
abbrev Ptr := { p : UInt32 // p ≠ 0 ∧ p.fitsBits 31 }

transmog Ptr as [p : UInt32[0:31] // p ≠ 0]

/-- The target of an edge, either the terminal or an internal node. -/
inductive Node where
  | sink
  | inode (p : Ptr)
deriving DecidableEq

transmog Node as [n : UInt32[0:31]] where
  | sink => guard n = 0
  | inode =>
    p : Ptr <= n

/-- An edge, denoting the function of its target node, negated when `compl` is set. -/
structure Edge where
  compl : Bool
  node : Node
deriving DecidableEq

transmog Edge as [r : UInt32] where
  compl : Bool <= lsbAsBool r[0]
  node : Node <= r[1:32]
derive_layout C packed

/-- An internal node, branching on `var` between the edges `hi` and `lo`. -/
structure InternalNode where
  var : UInt32
  hi : Edge
  lo : Edge

transmog InternalNode as [var : UInt32, hi : UInt32, lo : UInt32] where
  var : UInt32 <= var
  hi : Edge <= hi
  lo : Edge <= lo
derive_layout C packed

example : (HasLayout.layout (α := Edge)).size = 4 := rfl
example : (HasLayout.layout (α := InternalNode)).size = 12 := rfl

/-- The node array; element `i` holds the node that pointer `i + 1` addresses. -/
abbrev NodeArray := CompactArray InternalNode

/-! ## Using the array -/

/-- The edge to the terminal denoting the constant `b`. -/
def Edge.const (b : Bool) : Edge := ⟨b, .sink⟩

/-- The edge denoting the negation of what `e` denotes. -/
def Edge.not (e : Edge) : Edge := { e with compl := !e.compl }

/--
Append the internal node branching on `var` between `hi` and `lo` and return the edge to it, or
`none` once the pointers are exhausted.
-/
def NodeArray.mkNode (nodes : NodeArray) (var : UInt32) (hi lo : Edge) :
    Option (NodeArray × Edge) :=
  let p := nodes.size + 1
  if h : p < 2 ^ 31 then
    let ptr : Ptr := ⟨p.toUInt32, by simp [UInt32.fitsBits]; grind⟩
    some (nodes.push { var, hi, lo }, ⟨false, .inode ptr⟩)
  else
    none

/--
The value under the assignment `ω` of the function that `e` denotes, following at most `fuel`
edges; `nodes.size` is always enough fuel for a diagram built through `mkNode`, since every edge
points to an earlier node.
-/
def NodeArray.eval (nodes : NodeArray) (ω : UInt32 → Bool) : Nat → Edge → Bool
  | 0, e => e.compl
  | fuel + 1, e =>
    match e.node with
    | .sink => e.compl
    | .inode p =>
      let i := p.val.toNat - 1
      if h : i < nodes.size then
        let n := nodes[i]
        e.compl ^^ nodes.eval ω fuel (if ω n.var then n.hi else n.lo)
      else
        e.compl

/-- The diagram of `v₀ ∧ v₁`, with the node for `v₁` created first so that `v₀` can point at it. -/
def conj : Option (NodeArray × Edge) := do
  let (nodes, e₁) ← NodeArray.mkNode CompactArray.empty 1 (.const true) (.const false)
  nodes.mkNode 0 e₁ (.const false)

/-- The truth table of the function `e` denotes over the first two variables. -/
def table (nodes : NodeArray) (e : Edge) : List Bool :=
  [(false, false), (false, true), (true, false), (true, true)].map fun (a, b) =>
    nodes.eval (fun v => if v = 0 then a else b) nodes.size e

-- Two internal nodes occupy twenty-four bytes.
/-- info: some 24 -/
#guard_msgs in
#eval conj.map fun (nodes, _) => nodes.data.size

-- The root edge is the word `4`, that is `2 <<< 1`, an uncomplemented pointer `2`.
/-- info: some 4 -/
#guard_msgs in
#eval conj.map fun (_, e) => DataRepr.toRepr e

-- Each stored node as its variable and its two edge words; element `0` is the node for `v₁`,
-- whose edges are the constants `true` and `false`, and element `1` points at it.
/-- info: some [(1, 1, 0), (0, 2, 0)] -/
#guard_msgs in
#eval conj.map fun (nodes, _) =>
  nodes.toList.map fun (n : InternalNode) => (n.var, DataRepr.toRepr n.hi, DataRepr.toRepr n.lo)

-- The conjunction, and its complement through the edge bit alone.
/-- info: some ([false, false, false, true], [true, true, true, false]) -/
#guard_msgs in
#eval conj.map fun (nodes, e) => (table nodes e, table nodes e.not)

end BDD
