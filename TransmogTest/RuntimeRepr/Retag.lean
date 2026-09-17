/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import TransmogTest.RuntimeRepr.Node

/-!
# Word-backed targets that need the IR classification overridden

`Signed` is an inductive whose every constructor carries a field, and `Edge` is the structure from
the README, pairing a complement bit with a word-backed `Node`.  The compiler classifies both as
definite heap references, so `replace_runtime` accepts them only with
`transmog.replaceRuntime.overrideClassification` set, and then reclassifies them as tagged scalars.  `Link`
is declared after the clause and stores two `Edge`s, so its layout is computed against the new
classification.
-/

set_option experimental.transmog.replaceRuntime true
set_option transmog.replaceRuntime.overrideClassification true

@[expose] public section

namespace Transmog.Test.RuntimeRepr

open Transmog

inductive Signed where
  | pos (v : UInt8)
  | neg (v : UInt8)

transmog Signed as [s : UInt8, w : UInt8] where
  | pos =>
    guard s = 0
    v : UInt8 <= w
  | neg =>
    s := 1
    v : UInt8 <= w
  replace_runtime

deriving instance BEq, DecidableEq, Repr for Signed

structure Edge where
  compl : Bool
  node : Node

transmog Edge as [r : UInt32] where
  compl : Bool <= lsbAsBool r[0]
  node : Node <= r[1:32]
replace_runtime
derive_layout C packed

structure Link where
  hi : Edge
  lo : Edge

transmog Link as [hi : UInt32, lo : UInt32] where
  hi : Edge <= hi
  lo : Edge <= lo
derive_layout C packed

example : (HasLayout.layout (α := Edge)).size = 4 := rfl
example : (HasLayout.layout (α := Link)).size = 8 := rfl

end Transmog.Test.RuntimeRepr
