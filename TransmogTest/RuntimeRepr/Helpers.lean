/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import TransmogTest.RuntimeRepr.Probes
meta import TransmogTest.RuntimeRepr.Probes

/-!
# Tests for the helpers `replace_runtime` generates

The carrier a representation gets, the names, signatures and values of the packed-word helpers,
the redirection of the codecs, the registry entry, the classification of the type after the
clause, and what the round-trip theorem rests on.
-/

-- Deliberately ill-formed declarations follow.
set_option linter.hazel false

namespace Transmog.Test.RuntimeRepr

open Transmog

/-! ## Carriers -/

-- The smallest carrier that fits the slots, a ranged slot counting up to the top of its range.
/-- info: @[expose] unsafe def Transmog.Test.RuntimeRepr.Node.Runtime.word : Node → UInt32 -/
#guard_msgs in
#print sig Node.Runtime.word

/-- info: @[expose] unsafe def Transmog.Test.RuntimeRepr.Op.Runtime.word : Op → UInt16 -/
#guard_msgs in
#print sig Op.Runtime.word

/-- info: @[expose] unsafe def Transmog.Test.RuntimeRepr.Cell.Runtime.word : Cell → UInt32 -/
#guard_msgs in
#print sig Cell.Runtime.word

/-- info: @[expose] unsafe def Transmog.Test.RuntimeRepr.Edge.Runtime.word : Edge → UInt32 -/
#guard_msgs in
#print sig Edge.Runtime.word

@[expose] public section

inductive Small where
  | zero
  | one (v : { u : UInt8 // u.fitsBits 4 })

set_option experimental.transmog.replaceRuntime true in
transmog Small as [t : UInt8[:1], v : UInt8[:4]] where
  | zero => guard t = 0
  | one =>
    t := 1
    v : { u : UInt8 // u.fitsBits 4 } <= v
  replace_runtime

inductive Wider where
  | zero
  | one (v : { u : UInt8 // u.fitsBits 4 })

-- A carrier wider than needed can be requested.
set_option experimental.transmog.replaceRuntime true in
transmog Wider as [t : UInt8[:1], v : UInt8[:4]] where
  | zero => guard t = 0
  | one =>
    t := 1
    v : { u : UInt8 // u.fitsBits 4 } <= v
  replace_runtime as UInt16

end

/-- info: @[expose] unsafe def Transmog.Test.RuntimeRepr.Small.Runtime.word : Small → UInt8 -/
#guard_msgs in
#print sig Small.Runtime.word

/-- info: @[expose] unsafe def Transmog.Test.RuntimeRepr.Wider.Runtime.word : Wider → UInt16 -/
#guard_msgs in
#print sig Wider.Runtime.word

/-! ## The packed-word helpers of `Node` -/

/-- info: @[expose] unsafe def Transmog.Test.RuntimeRepr.Node.Runtime.ofWord : UInt32 → Node -/
#guard_msgs in
#print sig Node.Runtime.ofWord

/-- info: @[expose] def Transmog.Test.RuntimeRepr.Node.Runtime.pack : { n // UInt32.fitsBits 31 n } → UInt32 -/
#guard_msgs in
#print sig Node.Runtime.pack

/-- info: @[expose] unsafe def Transmog.Test.RuntimeRepr.Node.Runtime.unpack : UInt32 → { n // UInt32.fitsBits 31 n } -/
#guard_msgs in
#print sig Node.Runtime.unpack

/-- info: @[expose] unsafe def Transmog.Test.RuntimeRepr.Node.Runtime.toReprImpl : Node → { n // UInt32.fitsBits 31 n } -/
#guard_msgs in
#print sig Node.Runtime.toReprImpl

/-- info: @[expose] unsafe def Transmog.Test.RuntimeRepr.Node.Runtime.fromReprImpl : { n // UInt32.fitsBits 31 n } → Node -/
#guard_msgs in
#print sig Node.Runtime.fromReprImpl

/--
info: @[instance_reducible, expose] unsafe def Transmog.Test.RuntimeRepr.Node.Runtime.dataReprImpl : DataRepr Node
  { n // UInt32.fitsBits 31 n }
-/
#guard_msgs in
#print sig Node.Runtime.dataReprImpl

/-- info: @[expose] unsafe def Transmog.Test.RuntimeRepr.Node.Runtime.ctor_sink : Node -/
#guard_msgs in
#print sig Node.Runtime.ctor_sink

/-- info: @[expose] unsafe def Transmog.Test.RuntimeRepr.Node.Runtime.ctor_inode : Ptr → Node -/
#guard_msgs in
#print sig Node.Runtime.ctor_inode

/-- info: @[expose] def Transmog.Test.RuntimeRepr.Node.Runtime.test_sink : UInt32 → Bool -/
#guard_msgs in
#print sig Node.Runtime.test_sink

/-- info: @[expose] unsafe def Transmog.Test.RuntimeRepr.Node.Runtime.field_inode_p : UInt32 → Ptr -/
#guard_msgs in
#print sig Node.Runtime.field_inode_p

/-- info: @[expose] def Transmog.Test.RuntimeRepr.Node.Runtime.ctorIdxImpl : Node → Nat -/
#guard_msgs in
#print sig Node.Runtime.ctorIdxImpl

/-- info: theorem Transmog.Test.RuntimeRepr.Node.Runtime.ctorIdx_eq : Node.ctorIdx = Node.Runtime.ctorIdxImpl -/
#guard_msgs in
#print sig Node.Runtime.ctorIdx_eq

/--
info: def Transmog.Test.RuntimeRepr.Node.Runtime.recImpl.{u} : {motive : Node → Sort u} →
  motive Node.sink → ((p : Ptr) → motive (Node.inode p)) → (t : Node) → motive t
-/
#guard_msgs in
#print sig Node.Runtime.recImpl

/-- info: theorem Transmog.Test.RuntimeRepr.Node.Runtime.rec_eq.{u} : @Node.rec = @Node.Runtime.recImpl -/
#guard_msgs in
#print sig Node.Runtime.rec_eq

/--
info: def Transmog.Test.RuntimeRepr.Node.Runtime.recOnImpl.{u} : {motive : Node → Sort u} →
  (t : Node) → motive Node.sink → ((p : Ptr) → motive (Node.inode p)) → motive t
-/
#guard_msgs in
#print sig Node.Runtime.recOnImpl

/-- info: theorem Transmog.Test.RuntimeRepr.Node.Runtime.recOn_eq.{u} : @Node.recOn = @Node.Runtime.recOnImpl -/
#guard_msgs in
#print sig Node.Runtime.recOn_eq

-- The pure helpers compute in the kernel.
example : Node.Runtime.pack ⟨5, by decide⟩ = 5 := rfl
example : Node.Runtime.test_sink 0 = true := rfl
example : Node.Runtime.test_sink 5 = false := rfl
example : Node.Runtime.ctorIdxImpl .sink = 0 := rfl
example (p : Ptr) : Node.Runtime.ctorIdxImpl (.inode p) = 1 := rfl
example : Op.Runtime.pack (10, 7) = 0x070A := rfl
example : Cell.Runtime.pack (1, 2, 3) = 0x030201 := rfl
example : Op.Runtime.test_nop 0x070A = false := rfl
example : Op.Runtime.test_shl 0x0009 = true := rfl

-- The unsafe helpers run in the interpreter.
#guard_msgs in
#eval show IO Unit from do
  let check (label : String) (ok : Bool) : IO Unit := unless ok do throw (IO.userError label)
  check "word" (Node.Runtime.word (.inode ⟨5, by decide⟩) == 5)
  check "word of sink" (Node.Runtime.word .sink == 0)
  check "field" ((Node.Runtime.field_inode_p 5).val == 5)
  check "nullary constructor" (Node.Runtime.ctor_sink == .sink)
  check "constructor" (Node.Runtime.ctor_inode ⟨5, by decide⟩ == .inode ⟨5, by decide⟩)
  check "unpack" ((Node.Runtime.unpack 5).val == 5)
  check "field of Op" (Op.Runtime.field_imm_v 0x070A == 7)
  check "word of Cell" (Cell.Runtime.word (.pair 2 3) == 0x030201)
  check "word of the nullary Cell" (Cell.Runtime.word .empty == 0x090700)
  check "word of Edge" (Edge.Runtime.word ⟨true, .inode ⟨5, by decide⟩⟩ == 11)
  check "word of Signed" (Signed.Runtime.word (.neg 3) == 0x0301)

-- The codecs are redirected to the packed-word implementations.
run_meta do
  let env ← Lean.getEnv
  unless Lean.Compiler.getImplementedBy? env ``Node.Repr.toRepr == some ``Node.Runtime.toReprImpl do
    throwError "toRepr is not redirected"
  unless Lean.Compiler.getImplementedBy? env ``Node.Repr.fromRepr ==
      some ``Node.Runtime.fromReprImpl do
    throwError "fromRepr is not redirected"
  unless Lean.Compiler.getImplementedBy? env ``Op.Repr.toRepr == some ``Op.Runtime.toReprImpl do
    throwError "toRepr of Op is not redirected"

#guard (DataRepr.toRepr (Node.inode ⟨5, by decide⟩)).val == 5
#guard (DataRepr.fromRepr ⟨5, by decide⟩ : Node) == .inode ⟨5, by decide⟩
#guard DataRepr.toRepr (Op.imm 7) == (10, 7)
#guard (DataRepr.fromRepr (10, 7) : Op) == .imm 7

/-! ## The registry -/

run_meta do
  let env ← Lean.getEnv
  let some info := Transmog.Runtime.reprInfo? env ``Node | throwError "Node is not registered"
  unless info.carrier == ``UInt32 do throwError "carrier"
  unless info.ctors == #[``Node.sink, ``Node.inode] do throwError "ctors"
  unless info.word == ``Node.Runtime.word do throwError "word"
  unless info.ctorImpls == #[``Node.Runtime.ctor_sink, ``Node.Runtime.ctor_inode] do
    throwError "ctorImpls"
  unless info.tests == #[some ``Node.Runtime.test_sink, none] do throwError "tests"
  unless info.fields == #[#[], #[``Node.Runtime.field_inode_p]] do throwError "fields"
  unless info.order == #[0] do throwError "order"
  unless info.unguarded? == some 1 do throwError "unguarded"
  -- The auxiliaries of the inductive and the logical codecs were compiled against the object
  -- layout, and must never be called.
  unless info.forbidden == #[``Node.ctorElim, ``Node.ctorIdx, ``Node.rec, ``Node.Repr.toRepr,
      ``Node.Repr.fromRepr] do
    throwError "forbidden: {info.forbidden}"

run_meta do
  let env ← Lean.getEnv
  let some info := Transmog.Runtime.reprInfo? env ``Op | throwError "Op is not registered"
  unless info.carrier == ``UInt16 do throwError "carrier"
  unless info.ctors.size == 11 do throwError "ctors"
  unless info.order == #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9] do throwError "order"
  unless info.unguarded? == some 10 do throwError "unguarded"
  unless info.fields[10]! == #[``Op.Runtime.field_imm_v] do throwError "fields"
  -- Derived equality compiled against the object layout before the clause is forbidden.
  unless (Transmog.Runtime.reprInfo? env ``Cell).isSome do throwError "Cell is not registered"
  unless (Transmog.Runtime.reprInfo? env ``Small).isSome do throwError "Small is not registered"
  if (Transmog.Runtime.reprInfo? env ``Ptr).isSome then throwError "Ptr is registered"

-- The registry indexes constructors and forbidden declarations.
run_meta do
  let reg := Transmog.Runtime.getRegistry (← Lean.getEnv)
  unless reg.ctors.find? ``Node.inode == some (``Node, 1) do throwError "ctor index"
  unless reg.ctors.find? ``Op.imm == some (``Op, 10) do throwError "ctor index of Op"
  unless reg.types.contains ``Edge do throwError "Edge is not registered"

/-! ## The classification after the clause -/

-- A possibly tagged pointer keeps its classification; the override makes a definite heap
-- reference a tagged scalar.
open Lean.Compiler.LCNF in
run_meta do
  unless (← nameToImpureType ``Op) == ImpureType.tobject do throwError "Op"
  unless (← nameToImpureType ``Node) == ImpureType.tagged do throwError "Node"
  unless (← nameToImpureType ``Edge) == ImpureType.tagged do throwError "Edge"
  unless (← nameToImpureType ``Signed) == ImpureType.tagged do throwError "Signed"

/-! ## Axioms -/

-- The round trip is proved on the logical codecs; the redirection adds no axiom.
/-- info: 'Transmog.Test.RuntimeRepr.Node.Repr.from_to' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Node.Repr.from_to

-- The replacement equalities hold by reflexivity on the logical side.
/-- info: 'Transmog.Test.RuntimeRepr.Node.Runtime.rec_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Node.Runtime.rec_eq

/-- info: 'Transmog.Test.RuntimeRepr.Node.Runtime.ctorIdx_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Node.Runtime.ctorIdx_eq

end Transmog.Test.RuntimeRepr
