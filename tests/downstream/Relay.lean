module

public import Consume

/-! # An intermediate module, so the consumer below reaches the types through two hops -/

set_option linter.hazel false

@[expose] public section

namespace Relay

open Transmog.Test.RuntimeRepr Consumer

@[export relay_node_pair, noinline]
def nodePair (a b : Node) : Bool :=
  match a, b with
  | .sink, .sink => true
  | .inode p, .inode q => p.val == q.val
  | _, _ => false

@[export relay_op_eq, noinline]
def opEq (a b : Op) : Bool := a == b

@[export relay_edge_eq, noinline]
def edgeEq (a b : Edge) : Bool :=
  match a, b with
  | ⟨c, .sink⟩, ⟨d, .sink⟩ => c == d
  | ⟨c, .inode p⟩, ⟨d, .inode q⟩ => c == d && p.val == q.val
  | _, _ => false

end Relay
