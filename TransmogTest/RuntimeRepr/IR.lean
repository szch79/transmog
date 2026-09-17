/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import TransmogTest.RuntimeRepr.Retag
public import TransmogTest.RuntimeRepr.Wide

/-!
# Pinned compiler output for word-backed targets

What the lowering pass produces for one match, and what the code generator makes of it: a match
becomes an unboxed comparison, a construction a boxed word, the constructor index a call to its
replacement, and a reclassified type loses its reference counting.
-/

set_option linter.hazel false

namespace Transmog.Test.RuntimeRepr.IR

open Transmog

public section

/-! ## The lowering pass -/

-- A match on `Node` is rewritten to the guard test and the field projection on the word.
/--
trace: [Compiler.Transmog.lowerRuntimeRepr] size: 15
    def Transmog.Test.RuntimeRepr.IR.nodeWord n : UInt32 :=
      fun _f.1 _ : UInt32 :=
        let _x.2 := 0;
        let _x.3 := @UInt32.instOfNat _x.2;
        let _x.4 := _x.3 # 0;
        return _x.4;
      let _alt.5 := _f.1;
      fun _f.6 p : UInt32 :=
        let _x.7 := p # 0;
        return _x.7;
      let _alt.8 := _f.6;
      let raw := Node.Runtime.word n;
      let isCtor := Node.Runtime.test_sink raw;
      cases isCtor : UInt32
      | Bool.true =>
        let _x.9 := ();
        let _x.10 := _alt.5 _x.9;
        return _x.10
      | Bool.false =>
        let p.11 := Node.Runtime.field_inode_p raw;
        let _x.12 := _alt.8 p.11;
        return _x.12
-/
#guard_msgs (trace) in
set_option trace.Compiler.Transmog.lowerRuntimeRepr true in
def nodeWord (n : Node) : UInt32 :=
  match n with
  | .sink => 0
  | .inode p => p.val

/-! ## The generated IR -/

-- No `casesOn` and no projection remain: the word is unboxed and compared.
/--
trace: [Compiler.IR] [result]
    def Transmog.Test.RuntimeRepr.IR.nodeWord' (x_1 : tagged) : u32 :=
      let x_2 : u32 := 0;
      let x_3 : u32 := unbox x_1;
      let x_4 : u8 := UInt32.decEq x_3 x_2;
      case x_4 : u8 of
      Bool.true →
        ret x_2
      Bool.false →
        let x_5 : u32 := unbox x_1;
        ret x_5
    def Transmog.Test.RuntimeRepr.IR.nodeWord'._boxed (x_1 : tagged) : tobj :=
      let x_2 : u32 := Transmog.Test.RuntimeRepr.IR.nodeWord' x_1;
      let x_3 : tobj := box x_2;
      ret x_3
-/
#guard_msgs (trace) in
set_option trace.compiler.ir.result true in
def nodeWord' (n : Node) : UInt32 :=
  match n with
  | .sink => 0
  | .inode p => p.val

-- A construction packs the fields and boxes the word.
/--
trace: [Compiler.IR] [result]
    def Transmog.Test.RuntimeRepr.IR.mkNode (x_1 : u32) : tagged :=
      let x_2 : tagged := box x_1;
      ret x_2
    def Transmog.Test.RuntimeRepr.IR.mkNode._boxed (x_1 : tobj) : tagged :=
      let x_2 : u32 := unbox x_1;
      dec x_1;
      let x_3 : tagged := Transmog.Test.RuntimeRepr.IR.mkNode x_2;
      ret x_3
-/
#guard_msgs (trace) in
set_option trace.compiler.ir.result true in
def mkNode (p : Ptr) : Node := .inode p

-- The constructor index is computed from the word through the `csimp` replacement.
/--
trace: [Compiler.IR] [result]
    def Transmog.Test.RuntimeRepr.IR.nodeIndex (x_1 : tagged) : tobj :=
      let x_2 : tobj := Transmog.Test.RuntimeRepr.Node.Runtime.ctorIdxImpl x_1;
      ret x_2
-/
#guard_msgs (trace) in
set_option trace.compiler.ir.result true in
def nodeIndex (n : Node) : Nat := n.ctorIdx

-- Without the override, a value of a possibly tagged type is still reference counted when it
-- is duplicated; with it, the boxed word is not.
/--
trace: [Compiler.IR] [result]
    def Transmog.Test.RuntimeRepr.IR.twoCells (x_1 : tobj) : obj :=
      inc x_1;
      let x_2 : obj := ctor_0[Prod.mk] x_1 x_1;
      ret x_2
-/
#guard_msgs (trace) in
set_option trace.compiler.ir.result true in
def twoCells (c : Cell) : Cell × Cell := (c, c)

/--
trace: [Compiler.IR] [result]
    def Transmog.Test.RuntimeRepr.IR.twoEdges (x_1 : tagged) : obj :=
      let x_2 : obj := ctor_0[Prod.mk] x_1 x_1;
      ret x_2
-/
#guard_msgs (trace) in
set_option trace.compiler.ir.result true in
def twoEdges (e : Edge) : Edge × Edge := (e, e)

end

end Transmog.Test.RuntimeRepr.IR
