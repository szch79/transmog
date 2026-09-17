/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL

/-!
# Experimental word-backed inductive target

`Node` is the two-constructor type from the README.  The compiler classifies it as a possibly
tagged pointer, so it needs no override; the option is set anyway, so that the override's effect
on a type that did not need it, namely the removal of the tested reference counting, is covered
as well.  `Wide.lean` keeps the default path covered.
-/

set_option experimental.transmog.replaceRuntime true
set_option transmog.replaceRuntime.overrideClassification true

@[expose] public section

namespace Transmog.Test.RuntimeRepr

open Transmog

abbrev Ptr := {p : UInt32 // p ≠ 0 ∧ p.fitsBits 31}

transmog Ptr as [p : UInt32[0:31] // p ≠ 0]

inductive Node where
  | sink
  | inode (p : Ptr)

transmog Node as [n : UInt32[0:31]] where
  | sink => guard n = 0
  | inode =>
    p : Ptr <= n
  replace_runtime

end Transmog.Test.RuntimeRepr
