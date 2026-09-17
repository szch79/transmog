/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL

/-!
# Tests for the module-system scopes

The same declarations in a private scope, in a plain `public section` and in an `@[expose]
public section`: what the generated declarations' visibility is, that every clause works in
each scope, that a type's own visibility modifier carries over to its package, and how the
command recovers from a failure.
-/

-- Deliberately ill-formed declarations follow.
set_option linter.hazel false

namespace Transmog.Test.Scope

open Transmog

/-! ## A private scope -/

namespace Private

structure Byte where
  v : UInt8
deriving DecidableEq

transmog Byte as [b : UInt8] where
  v : UInt8 <= b
derive_layout C packed

transmog Option Byte as [t : UInt8, v : UInt8] where
  | none => guard t = 0
  | some =>
    t := 1
    val : Byte <= v
derive_layout C packed

-- The package and the instances are private with the type.
/-- info: private def Transmog.Test.Scope.Private.Byte.Repr.toRepr : Byte → UInt8 -/
#guard_msgs in
#print sig Byte.Repr.toRepr

run_meta do
  for n in [`Transmog.Test.Scope.Private.Byte.Repr.from_to,
      `Transmog.Test.Scope.Private.instDataReprByteUInt8,
      `Transmog.Test.Scope.Private.instHasLayoutByteUInt8OfNatNat] do
    unless Lean.isPrivateName (← Lean.realizeGlobalConstNoOverload (Lean.mkIdent n)) do
      throwError "{n} is not private"

example : Byte.Repr.toRepr ⟨7⟩ = 7 := rfl
example : (HasLayout.layout (α := Byte)).size = 1 := rfl
example : ((HasLayout.layout (α := Option Byte)).toBytes
    (DataRepr.toRepr (some ⟨7⟩ : Option Byte))).data = #[1, 7] := by decide

-- A `public` type declared with the combined form gets a public package and public instances.
public transmog enum Flag as [t : UInt8] where
  | off => guard t = 0
  | on => t := 1
deriving Repr

run_meta do
  for n in [`Transmog.Test.Scope.Private.Flag.Repr.toRepr,
      `Transmog.Test.Scope.Private.instDataReprFlagUInt8,
      `Transmog.Test.Scope.Private.instReprFlag] do
    if Lean.isPrivateName (← Lean.realizeGlobalConstNoOverload (Lean.mkIdent n)) then
      throwError "{n} is private"

end Private

/-! ## A plain public section -/

namespace Public

public section

structure Byte where
  v : UInt8
deriving DecidableEq

transmog Byte as [b : UInt8] where
  v : UInt8 <= b
derive_layout C packed

transmog Option Byte as [t : UInt8, v : UInt8] where
  | none => guard t = 0
  | some =>
    t := 1
    val : Byte <= v
derive_layout C packed

inductive Node where
  | sink
  | inode (p : UInt8)

set_option experimental.transmog.replaceRuntime true in
transmog Node as [t : UInt8, v : UInt8] where
  | sink => guard t = 0
  | inode =>
    t := 1
    p : UInt8 <= v
  replace_runtime

-- A private type in a public section keeps its package private, whether the type is declared
-- on its own or with the combined form.
private inductive Hidden where
  | off
  | on

transmog Hidden as [t : UInt8] where
  | off => guard t = 0
  | on => t := 1

private transmog enum Secret as [t : UInt8] where
  | off => guard t = 0
  | on => t := 1
deriving Repr

end

run_meta do
  for n in [`Transmog.Test.Scope.Public.Hidden.Repr.toRepr,
      `Transmog.Test.Scope.Public.instDataReprHiddenUInt8,
      `Transmog.Test.Scope.Public.Secret.Repr.toRepr,
      `Transmog.Test.Scope.Public.instDataReprSecretUInt8,
      `Transmog.Test.Scope.Public.instReprSecret] do
    unless Lean.isPrivateName (← Lean.realizeGlobalConstNoOverload (Lean.mkIdent n)) do
      throwError "{n} is not private"

-- The generated definitions are exposed whether or not the section is, so that importing
-- modules can compute with them.
/-- info: @[expose] def Transmog.Test.Scope.Public.Byte.Repr.toRepr : Byte → UInt8 -/
#guard_msgs in
#print sig Byte.Repr.toRepr

/--
info: @[expose] def Transmog.Test.Scope.Public.Byte.Repr.load : (bs : ByteArray) → (off : Nat) → off + 1 ≤ bs.size → UInt8
-/
#guard_msgs in
#print sig Byte.Repr.load

/-- info: @[expose] def Transmog.Test.Scope.Public.Byte.Repr.layoutRef : Layout UInt8 0 -/
#guard_msgs in
#print sig Byte.Repr.layoutRef

run_meta do
  for n in [`Transmog.Test.Scope.Public.Byte.Repr.from_to,
      `Transmog.Test.Scope.Public.instDataReprByteUInt8,
      `Transmog.Test.Scope.Public.instHasLayoutByteUInt8OfNatNat] do
    if Lean.isPrivateName (← Lean.realizeGlobalConstNoOverload (Lean.mkIdent n)) then
      throwError "{n} is private"

example : Byte.Repr.toRepr ⟨7⟩ = 7 := rfl
example : (HasLayout.layout (α := Option Byte)).size = 2 := rfl
example : Node.Runtime.pack (1, 7) = 0x0701 := rfl

end Public

/-! ## An exposed public section -/

namespace Exposed

@[expose] public section

structure Byte where
  v : UInt8
deriving DecidableEq

transmog Byte as [b : UInt8] where
  v : UInt8 <= b
derive_layout C packed

transmog Option Byte as [t : UInt8, v : UInt8] where
  | none => guard t = 0
  | some =>
    t := 1
    val : Byte <= v
derive_layout C packed

end

/-- info: @[expose] def Transmog.Test.Scope.Exposed.Byte.Repr.toRepr : Byte → UInt8 -/
#guard_msgs in
#print sig Byte.Repr.toRepr

example : Byte.Repr.toRepr ⟨7⟩ = 7 := rfl
example : (HasLayout.layout (α := Option Byte)).size = 2 := rfl

end Exposed

/-! ## Recovery -/

structure Q where
  x : UInt8

-- A layout over a broken representation adds no diagnostic of its own.
/-- error: unknown representation slot `s` -/
#guard_msgs in
transmog Q as [r : UInt8] where
  x : UInt8 <= s
derive_layout C packed

-- After a failure past the codecs the package exists, so the declaration cannot be repeated.
structure Loose where
  v : { u : UInt8 // u < 16 }

/--
error: failed to prove Transmog `DataRepr` subtype obligation
repr✝ : UInt8
r : UInt8 := repr✝
⊢ r < 16
-/
#guard_msgs in
transmog Loose as [r : UInt8] where
  v : { u : UInt8 // u < 16 } <= r

/--
error: private declaration `Transmog.Test.Scope.Loose.Repr.toRepr` has already been declared
---
error: private declaration `Transmog.Test.Scope.Loose.Repr.fromRepr` has already been declared
-/
#guard_msgs in
transmog Loose as [r : UInt8 // r < 16] where
  v : { u : UInt8 // u < 16 } <= r

end Transmog.Test.Scope
