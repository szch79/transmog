/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL

/-!
# Word-backed targets exercising the wider shapes

`Cell` has a nullary constructor whose encoding is nonzero, so it cannot be confused with the
`lean_box(0)` the runtime would use on its own, and its representation spans three slots.  `Op`
has enough constructors to push derived equality onto the per-constructor eliminators, and a tag
narrow enough to fit a `UInt16` carrier.
-/

set_option experimental.transmog.replaceRuntime true

@[expose] public section

namespace Transmog.Test.RuntimeRepr

inductive Cell where
  | empty
  | pair (a : UInt8) (b : UInt8)

transmog Cell as [t : UInt8, p : UInt8, q : UInt8] where
  | empty =>
    guard t = 0
    p := 7
    q := 9
  | pair =>
    t := 1
    a : UInt8 <= p
    b : UInt8 <= q
  replace_runtime
  derive_layout C packed

inductive Op where
  | nop
  | add
  | sub
  | mul
  | div
  | mod
  | band
  | bor
  | bxor
  | shl
  | imm (v : UInt8)

transmog Op as [tag : UInt8, arg : UInt8] where
  | nop => guard tag = 0
  | add => guard tag = 1
  | sub => guard tag = 2
  | mul => guard tag = 3
  | div => guard tag = 4
  | mod => guard tag = 5
  | band => guard tag = 6
  | bor => guard tag = 7
  | bxor => guard tag = 8
  | shl => guard tag = 9
  | imm =>
    tag := 10
    v : UInt8 <= arg
  replace_runtime

deriving instance BEq, DecidableEq, Ord, Hashable, Repr for Op

deriving instance BEq, DecidableEq, Repr for Cell

/-- Declared here so that the negative tests can reject a clause written in another module. -/
inductive Elsewhere where
  | nothing
  | just (v : UInt8)

end Transmog.Test.RuntimeRepr
