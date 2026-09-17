/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL

/-!
# The code generator's last line of defence

With the staleness check turned off, a definition compiled before the clause survives and is
inlined into a later one, where it would read the object layout of a value that no longer has
one.  The verification pass turns that into a compile error, for an elimination, a construction
and a call into an auxiliary of the type.  The structure case leaks a projection rather than a
match; the mono phase turns it into a `cases`, which is what the pass sees.
-/

set_option experimental.transmog.replaceRuntime true
set_option debug.transmog.skipStaleCheck true
set_option linter.hazel false

@[expose] public section

namespace Transmog.Test.RuntimeRepr.Verifier

inductive Leak where
  | nothing
  | just (v : UInt8)

@[inline] def leakWord : Leak → UInt8
  | .nothing => 0
  | .just v => v

@[inline] def leakMake (v : UInt8) : Leak := .just v

@[inline] def leakIndex (l : Leak) : Nat := l.ctorIdx

transmog Leak as [t : UInt8, a : UInt8] where
  | nothing => guard t = 0
  | just =>
    t := 1
    v : UInt8 <= a
  replace_runtime

/--
error: `useLeak` still eliminates through the object layout of `Leak`, whose runtime representation was replaced.

This usually means the code was compiled before the `replace_runtime` clause ran, and was then inlined here.  Move every definition that mentions `Leak` after the clause.
-/
#guard_msgs(error, drop all) in
def useLeak (l : Leak) : UInt8 := leakWord l

/--
error: `useLeakMake` still allocates through the object layout of `Leak`, whose runtime representation was replaced.

This usually means the code was compiled before the `replace_runtime` clause ran, and was then inlined here.  Move every definition that mentions `Leak` after the clause.
-/
#guard_msgs(error, drop all) in
def useLeakMake (v : UInt8) : Leak := leakMake v

/--
error: `useLeakIndex` still calls `Leak.ctorIdx`, which operates through the object layout of `Leak`, whose runtime representation was replaced.

This usually means the code was compiled before the `replace_runtime` clause ran, and was then inlined here.  Move every definition that mentions `Leak` after the clause.
-/
#guard_msgs(error, drop all) in
def useLeakIndex (l : Leak) : Nat := leakIndex l

structure LeakPair where
  a : UInt8
  b : UInt8

@[inline] def leakFirst (p : LeakPair) : UInt8 := p.a

set_option transmog.replaceRuntime.overrideClassification true in
transmog LeakPair as [x : UInt8, y : UInt8] where
  a : UInt8 <= x
  b : UInt8 <= y
replace_runtime

/--
error: `useLeakPair` still eliminates through the object layout of `LeakPair`, whose runtime representation was replaced.

This usually means the code was compiled before the `replace_runtime` clause ran, and was then inlined here.  Move every definition that mentions `LeakPair` after the clause.
-/
#guard_msgs(error, drop all) in
def useLeakPair (p : LeakPair) : UInt8 := leakFirst p

end Transmog.Test.RuntimeRepr.Verifier
