/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

-- The DSL is imported for its syntax only, so nothing re-exports the code generator passes;
-- modules importing this one would then see the type but not the passes that make its runtime
-- representation work.
public import Transmog.DSL.Core.Basic
meta import Transmog.DSL

/-! # A `replace_runtime` clause that its module does not re-export support for -/

set_option experimental.transmog.replaceRuntime true
set_option linter.hazel false

@[expose] public section

namespace Transmog.Test.RuntimeRepr.NoReach

inductive Unreachable where
  | nothing
  | just (v : UInt8)

/--
error: this module does not re-export a path to `Transmog.DSL.Runtime.Pass`, so modules importing it would compile `Unreachable` without the runtime representation passes; import Transmog with `public import Transmog.DSL`
-/
#guard_msgs(error, drop all) in
transmog Unreachable as [t : UInt8, a : UInt8] where
  | nothing => guard t = 0
  | just =>
    t := 1
    v : UInt8 <= a
  replace_runtime

end Transmog.Test.RuntimeRepr.NoReach
