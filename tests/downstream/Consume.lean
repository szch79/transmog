module

public import TransmogTest.RuntimeRepr.Probes

/-! # A downstream module that matches on word-backed types with no preparation of its own -/

set_option linter.hazel false

@[expose] public section

namespace Consumer

open Transmog.Test.RuntimeRepr

@[export consumer_node_word, noinline]
def nodeWord : Node → UInt32
  | .sink => 0
  | .inode p => p.val

@[export consumer_node_wildcard, noinline]
def nodeWildcard (n : Node) : UInt32 :=
  match n with
  | .inode p => p.val
  | _ => 0

@[export consumer_node_make, noinline]
def nodeMake (p : Ptr) : Node := .inode p

@[export consumer_op_arg, noinline]
def opArgDown : Op → UInt8
  | .imm v => v
  | _ => 0

@[export consumer_cell_fst, noinline]
def cellFstDown : Cell → UInt8
  | .empty => 0
  | .pair a _ => a

@[export consumer_edge_word, noinline]
def edgeWordDown (e : Edge) : UInt32 :=
  (nodeWord e.node <<< 1) ||| (if e.compl then 1 else 0)

@[export consumer_edge_make, noinline]
def edgeMakeDown (c : Bool) (n : Node) : Edge := { compl := c, node := n }

@[export consumer_signed_value, noinline]
def signedValueDown : Signed → UInt8
  | .pos v => v
  | .neg v => 0 - v

-- The registry and the classification override are persisted across packages.
open Lean.Compiler.LCNF in
run_meta do
  let env ← Lean.getEnv
  unless (Transmog.Runtime.reprInfo? env ``Node).isSome do throwError "Node is not registered"
  unless (← nameToImpureType ``Edge) == ImpureType.tagged do throwError "Edge is not tagged"
  unless (← nameToImpureType ``Op) == ImpureType.tobject do throwError "Op is not tobject"

end Consumer
