/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.Data
public import TransmogTest.RuntimeRepr.Retag
public import TransmogTest.RuntimeRepr.Wide

/-!
# Cross-module probes of the word-backed targets

Every probe is compiled in a module that does not set the options, so it establishes that the
representation, and the classification override where there is one, travel with the type.  The
probes are exported so that `check.sh` can find them in the generated C, and the native
executable runs them.  Every field access on `Edge` is exercised both as a projection and as a
match, because the frontend produces different code for the two.
-/

@[expose] public section

namespace Transmog.Test.RuntimeRepr

open Transmog

/-! ## The two-constructor type -/

deriving instance BEq, Repr, DecidableEq for Node

@[export runtime_node_match, noinline]
def matchWord : Node → UInt32
  | .sink => 0
  | .inode p => p.val

@[export runtime_node_wildcard, noinline]
def wildcard : Node → UInt32
  | .inode p => p.val
  | _ => 0

@[export runtime_node_rec, noinline]
def recWord (n : Node) : UInt32 := n.rec 0 (fun p => p.val)

@[export runtime_node_cases, noinline]
def casesWord (n : Node) : UInt32 := n.casesOn 0 (fun p => p.val)

@[export runtime_node_rec_on, noinline]
def recOnWord (n : Node) : UInt32 := n.recOn 0 (fun p => p.val)

@[export runtime_node_index, noinline]
def constructorIndex (n : Node) : Nat := n.ctorIdx

@[export runtime_node_dependent, noinline]
def dependent (n : Node) : (match n with | .sink => UInt32 | .inode _ => Ptr) :=
  match n with
  | .sink => 0
  | .inode p => p

@[export runtime_node_dependent_word, noinline]
def dependentWord (n : Node) : UInt32 :=
  match n with
  | .sink => dependent .sink
  | .inode p => (dependent (.inode p)).val

@[export runtime_node_make, noinline]
def makeNode (p : Ptr) : Node := .inode p

@[export runtime_node_beq, noinline]
def equal (a b : Node) : Bool := a == b

@[export runtime_node_dec_eq, noinline]
def decideEqual (a b : Node) : Bool := decide (a = b)

@[export runtime_node_codec, noinline]
def codec (n : Node) : Node :=
  DataRepr.fromRepr (DataRepr.toRepr n)

example : matchWord .sink = 0 := rfl
example (p : Ptr) : matchWord (.inode p) = p.val := rfl
example (p : Ptr) : recWord (.inode p) = p.val := rfl
example (p : Ptr) : casesWord (.inode p) = p.val := rfl

/-! ## A nullary constructor whose encoding is not the runtime's own `box 0` -/

@[export runtime_cell_empty, noinline]
def cellEmpty : Cell := .empty

@[export runtime_cell_make, noinline]
def cellMake (a b : UInt8) : Cell := .pair a b

@[export runtime_cell_fst, noinline]
def cellFst : Cell → UInt8
  | .empty => 0
  | .pair a _ => a

@[export runtime_cell_snd, noinline]
def cellSnd (c : Cell) : UInt8 :=
  match c with
  | .pair _ b => b
  | _ => 0

/-- The two matches merge into one continuation, so the tail becomes a join point. -/
@[export runtime_cell_pick, noinline]
def cellPick (c : Cell) (flag : Bool) : UInt8 :=
  (if flag then cellFst c else cellSnd c) + 1

@[export runtime_cell_codec, noinline]
def cellCodec (c : Cell) : Cell :=
  DataRepr.fromRepr (DataRepr.toRepr c)

/-! ## Enough constructors to route derived equality through the per-constructor eliminators -/

@[export runtime_op_imm, noinline]
def opImm (v : UInt8) : Op := .imm v

@[export runtime_op_arg, noinline]
def opArg : Op → UInt8
  | .imm v => v
  | _ => 0

@[export runtime_op_index, noinline]
def opIndex (o : Op) : Nat := o.ctorIdx

@[export runtime_op_beq, noinline]
def opBEq (a b : Op) : Bool := a == b

@[export runtime_op_dec_eq, noinline]
def opDecEq (a b : Op) : Bool := decide (a = b)

@[export runtime_op_hash, noinline]
def opHash (o : Op) : UInt64 := hash o

@[export runtime_op_le, noinline]
def opLE (a b : Op) : Bool := compare a b != .gt

@[export runtime_op_codec, noinline]
def opCodec (o : Op) : Op :=
  DataRepr.fromRepr (DataRepr.toRepr o)

/-- The match sits inside a closure, which is lifted out before the impure phase. -/
@[export runtime_op_fold, noinline]
def opFold (ops : List Op) : UInt8 :=
  ops.foldl (init := 0) fun acc o => acc + (match o with | .imm v => v | _ => 1)

/-! ## Word-backed values inside ordinary containers -/

@[noinline]
def opsRoundTrip (ops : Array Op) : Array Op :=
  ops.map opCodec

@[noinline]
def cellsToCompact (cs : List Cell) : CompactArray Cell :=
  cs.toCompactArray

@[noinline]
def cellOption (c? : Option Cell) : UInt8 :=
  match c? with
  | some c => cellFst c
  | none => 255

/-! ## Every constructor carries a field -/

@[export runtime_signed_value, noinline]
def signedValue : Signed → UInt8
  | .pos v => v
  | .neg v => 0 - v

@[export runtime_signed_make, noinline]
def signedMake (negative : Bool) (v : UInt8) : Signed :=
  if negative then .neg v else .pos v

@[export runtime_signed_index, noinline]
def signedIndex (s : Signed) : Nat := s.ctorIdx

@[export runtime_signed_beq, noinline]
def signedBEq (a b : Signed) : Bool := a == b

@[export runtime_signed_dec_eq, noinline]
def signedDecEq (a b : Signed) : Bool := decide (a = b)

@[export runtime_signed_codec, noinline]
def signedCodec (s : Signed) : Signed :=
  DataRepr.fromRepr (DataRepr.toRepr s)

/-! ## A structure over a word-backed inductive -/

deriving instance BEq, DecidableEq, Repr for Edge

@[export runtime_edge_compl, noinline]
def edgeCompl (e : Edge) : Bool := e.compl

@[export runtime_edge_node, noinline]
def edgeNode (e : Edge) : UInt32 :=
  match e.node with
  | .sink => 0
  | .inode p => p.val

@[export runtime_edge_match, noinline]
def edgeMatch (e : Edge) : UInt32 :=
  match e with
  | ⟨c, .sink⟩ => if c then 1 else 0
  | ⟨c, .inode p⟩ => (p.val <<< 1) ||| (if c then 1 else 0)

@[export runtime_edge_make, noinline]
def edgeMake (c : Bool) (n : Node) : Edge := ⟨c, n⟩

@[export runtime_edge_flip, noinline]
def edgeFlip (e : Edge) : Edge := { e with compl := !e.compl }

@[export runtime_edge_rec, noinline]
def edgeRec (e : Edge) : UInt32 := e.rec fun c n => if c then matchWord n else 0

@[export runtime_edge_beq, noinline]
def edgeBEq (a b : Edge) : Bool := a == b

@[export runtime_edge_dec_eq, noinline]
def edgeDecEq (a b : Edge) : Bool := decide (a = b)

@[export runtime_edge_codec, noinline]
def edgeCodec (e : Edge) : Edge :=
  DataRepr.fromRepr (DataRepr.toRepr e)

/-- The projection function passed as a value is unfolded into a closure by the frontend. -/
@[noinline]
def edgeCompls (es : List Edge) : List Bool := es.map Edge.compl

/-! ## Word-backed values inside ordinary containers and a real structure -/

@[noinline]
def linkHi (l : Link) : Edge := l.hi

@[noinline]
def linkSwap (l : Link) : Link := { hi := l.lo, lo := l.hi }

@[noinline]
def edgeOption (e? : Option Edge) : UInt32 :=
  match e? with
  | some e => edgeMatch e
  | none => 0xffffffff

@[noinline]
def edgesRoundTrip (es : Array Edge) : Array Edge :=
  es.map edgeCodec

@[noinline]
def edgesToCompact (es : List Edge) : CompactArray Edge :=
  es.toCompactArray

@[noinline]
def linksToCompact (ls : List Link) : CompactArray Link :=
  ls.toCompactArray

/-! ## Allocation stress -/

def ptrOf (i : Nat) : Ptr :=
  let v := (i % 1000 + 1).toUInt32
  if h : v ≠ 0 ∧ v.fitsBits 31 then ⟨v, h⟩ else ⟨1, by decide⟩

/--
Builds, transforms and consumes a large array of word-backed values.  A reference counting
operation emitted on a boxed word would crash here, whereas a single call would not necessarily
notice.
-/
def churnRound (round : Nat) : Nat :=
  let fresh := (Array.range 2048).map fun i =>
    let n : Node := if i % 3 == 0 then .sink else .inode (ptrOf (i + round))
    edgeMake (i % 2 == 0) n
  let es := edgesRoundTrip (fresh.map edgeFlip)
  let ls := es.zipWith (fun hi lo => ({ hi, lo } : Link)) es.reverse
  let ls := (linksToCompact ls.toList).toList.map linkSwap
  let fromLinks := ls.foldl (init := 0) fun acc l => acc + (edgeMatch (linkHi l)).toNat
  fromLinks + (edgesToCompact es.toList).size + (edgeCompls es.toList).length

@[noinline]
def churn (rounds : Nat) : Nat :=
  (List.range rounds).foldl (init := 0) fun acc round => acc + churnRound round

end Transmog.Test.RuntimeRepr
