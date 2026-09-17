/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import TransmogTest.RuntimeRepr.Wide

/-!
# Diagnostics of the `replace_runtime` clause

Every precondition of the clause, with and without the classification override, the code that
must not precede it, and the experimental warning that precedes an accepted clause.
-/

set_option experimental.transmog.replaceRuntime true
-- The declarations below are deliberately ill-formed, so style checking adds nothing.
set_option linter.hazel false

@[expose] public section

namespace Transmog.Test.RuntimeRepr.Errors

/-! ## Every constructor is already fieldless -/

inductive Flag where
  | off
  | on

/--
error: every constructor of `Flag` is already fieldless, so the compiler already represents it as a scalar; `replace_runtime` has nothing to add
-/
#guard_msgs(error, drop all) in
transmog Flag as [t : UInt8] where
  | off => guard t = 0
  | on =>
    t := 1
  replace_runtime

/-! ## A structure is a definite heap reference unless the classification is overridden -/

structure Pt where
  x : UInt8
  y : UInt8

/--
error: every constructor of `Pt` carries a field, so the compiler represents it as a definite heap reference and counts references on it without testing for a scalar, which a boxed word does not survive.  Setting `transmog.replaceRuntime.overrideClassification` lets `replace_runtime` override that classification; read the option's description before enabling it
-/
#guard_msgs(error, drop all) in
transmog Pt as [a : UInt8, b : UInt8] where
  x : UInt8 <= a
  y : UInt8 <= b
replace_runtime

/-! ## Every constructor carries a field -/

inductive Signed where
  | pos (v : UInt8)
  | neg (v : UInt8)

/--
error: every constructor of `Signed` carries a field, so the compiler represents it as a definite heap reference and counts references on it without testing for a scalar, which a boxed word does not survive.  Setting `transmog.replaceRuntime.overrideClassification` lets `replace_runtime` override that classification; read the option's description before enabling it
-/
#guard_msgs(error, drop all) in
transmog Signed as [s : UInt8, w : UInt8] where
  | pos =>
    guard s = 0
    v : UInt8 <= w
  | neg =>
    s := 1
    v : UInt8 <= w
  replace_runtime

/-! ## A single relevant field is already unwrapped by the compiler -/

structure Wrapped where
  v : UInt8

/--
error: `Wrapped` has one constructor with one relevant field, so the compiler already represents it by that field alone; `replace_runtime` has nothing to add
-/
#guard_msgs(error, drop all) in
transmog Wrapped as [a : UInt8] where
  v : UInt8 <= a
replace_runtime

/-! ## Wider than any carrier that boxes into an immediate -/

inductive Big where
  | small
  | wide (v : UInt32) (w : UInt16)

/--
error: the representation needs 56 bits, but a word-backed runtime representation is limited to 32; `UInt64` and `USize` always allocate when boxed
-/
#guard_msgs(error, drop all) in
transmog Big as [t : UInt8, a : UInt32, b : UInt16] where
  | small => guard t = 0
  | wide =>
    t := 1
    v : UInt32 <= a
    w : UInt16 <= b
  replace_runtime

/-! ## The requested carrier is too narrow -/

inductive Narrow where
  | none
  | some (v : UInt16)

/--
error: the representation needs 24 bits, which does not fit the 8-bit carrier `UInt8`
-/
#guard_msgs(error, drop all) in
transmog Narrow as [t : UInt8, a : UInt16] where
  | none => guard t = 0
  | some =>
    t := 1
    v : UInt16 <= a
  replace_runtime as UInt8

/-! ## The clause must live where the type is declared -/

open Transmog.Test.RuntimeRepr in
/--
error: `Elsewhere` is not declared in this module; `replace_runtime` changes how the type is compiled everywhere, so it must appear where the type is declared
-/
#guard_msgs(error, drop all) in
transmog Elsewhere as [t : UInt8, a : UInt8] where
  | nothing => guard t = 0
  | just =>
    t := 1
    v : UInt8 <= a
  replace_runtime

/-! ## Code compiled before the clause -/

inductive Stale where
  | nothing
  | just (v : UInt8)
deriving BEq

/--
error: the following declarations were compiled before `replace_runtime` and still use the object layout of `Stale`: [instBEqStale.beq]

Move them after the `transmog` declaration, including any `deriving` clause written on the `inductive` itself, or declare the type with `transmog enum`, whose `deriving` clause runs after the clause
-/
#guard_msgs(error, drop all) in
transmog Stale as [t : UInt8, a : UInt8] where
  | nothing => guard t = 0
  | just =>
    t := 1
    v : UInt8 <= a
  replace_runtime

/-! ## A declaration in the type's namespace compiled before the clause -/

inductive Premature where
  | nothing
  | just (v : UInt8)

def Premature.word : Premature → UInt8
  | .nothing => 0
  | .just v => v

/--
error: the following declarations were compiled before `replace_runtime` and still use the object layout of `Premature`: [Premature.word]

Move them after the `transmog` declaration, including any `deriving` clause written on the `inductive` itself, or declare the type with `transmog enum`, whose `deriving` clause runs after the clause
-/
#guard_msgs(error, drop all) in
transmog Premature as [t : UInt8, a : UInt8] where
  | nothing => guard t = 0
  | just =>
    t := 1
    v : UInt8 <= a
  replace_runtime

/-! ## The carrier must box into an immediate -/

inductive Carried where
  | nothing
  | just (v : UInt8)

/-- error: invalid carrier `UInt64`, expected `UInt8`, `UInt16`, or `UInt32`; a wider carrier allocates when boxed -/
#guard_msgs(error, drop all) in
transmog Carried as [t : UInt8, a : UInt8] where
  | nothing => guard t = 0
  | just =>
    t := 1
    v : UInt8 <= a
  replace_runtime as UInt64

/-! ## The bodiless form has no constructors to route -/

abbrev Alias := { u : UInt8 // u ≠ 0 }

/-- error: `replace_runtime` needs a constructor-by-constructor representation -/
#guard_msgs(error, drop all) in
transmog Alias as [r : UInt8 // r ≠ 0]
  replace_runtime

/-! ## A type field has no runtime value -/

inductive Typed where
  | nothing
  | just (v : UInt8) (α : Type)

-- The clause is rejected first; the codecs then fail on their own on the type field.
/--
error: constructor `Typed.just` carries a proof or type field, which a word-backed representation cannot recover from the packed word
---
error: failed to synthesize instance of type class
  DataCastT Type UInt8

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: failed to synthesize instance of type class
  DataCastT Type UInt8

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: failed to prove Transmog `DataRepr` round-trip obligation: goal constituents did not align; restate guard conjuncts in the same form as the field subtype properties, or provide `correct_by`
x✝ : Typed
v : UInt8
α : Type
⊢ sorry () = α
-/
#guard_msgs(error, drop all) in
transmog Typed as [t : UInt8, a : UInt8, b : UInt8] where
  | nothing => guard t = 0
  | just =>
    t := 1
    v : UInt8 <= a
    α : Type <= b
  replace_runtime

/-! ## The experimental warning -/

-- Without `experimental.transmog.replaceRuntime`, an accepted clause warns once, naming the type
-- and, under the classification override, the override.

inductive Plain where
  | nothing
  | just (v : UInt8)

/--
warning: The `replace_runtime` clause is experimental and depends on how the current Lean compiler lowers inductive types; it gives up the object layout of `Plain` for a boxed machine word, at the same level of trust as `implemented_by`; `set_option experimental.transmog.replaceRuntime true` acknowledges its experimental status and silences this warning.
-/
#guard_msgs (warning) in
set_option experimental.transmog.replaceRuntime false in
transmog Plain as [t : UInt8, a : UInt8] where
  | nothing => guard t = 0
  | just =>
    t := 1
    v : UInt8 <= a
  replace_runtime

structure Overridden where
  a : UInt8
  b : UInt8

/--
warning: The `replace_runtime` clause is experimental and depends on how the current Lean compiler lowers inductive types; it gives up the object layout of `Overridden` for a boxed machine word, at the same level of trust as `implemented_by`, and overrides the compiler's IR classification of `Overridden` as `transmog.replaceRuntime.overrideClassification` requests; `set_option experimental.transmog.replaceRuntime true` acknowledges its experimental status and silences this warning.
-/
#guard_msgs (warning) in
set_option experimental.transmog.replaceRuntime false in
set_option transmog.replaceRuntime.overrideClassification true in
transmog Overridden as [x : UInt8, y : UInt8] where
  a : UInt8 <= x
  b : UInt8 <= y
replace_runtime

/-! ## Under the classification override -/

set_option transmog.replaceRuntime.overrideClassification true

/-! ## A container laid out before the clause -/

structure Pair where
  a : UInt8
  b : UInt8

/-- Stores a `Pair` in an object slot, whose reference counting was fixed at this declaration. -/
structure Early where
  first : Pair
  tag : UInt8

/-- A structure the compiler erases to its single field has no layout of its own. -/
structure Boxed where
  pair : Pair

/--
error: the following inductives were declared before `replace_runtime` and store a field of `Pair` under its previous IR classification: [Early]

Move them after the `transmog` declaration
-/
#guard_msgs(error, drop all) in
transmog Pair as [x : UInt8, y : UInt8] where
  a : UInt8 <= x
  b : UInt8 <= y
replace_runtime

end Transmog.Test.RuntimeRepr.Errors

end -- @[expose] public section

/-! ## A private type -/

namespace Transmog.Test.RuntimeRepr.Errors

inductive Hidden where
  | nothing
  | just (v : UInt8)

/--
error: `Hidden` is private, and so would be the `csimp` lemmas that `replace_runtime` emits, which must be public; make the type public, in a `public section` and without `private`
-/
#guard_msgs(error, drop all) in
transmog Hidden as [t : UInt8, a : UInt8] where
  | nothing => guard t = 0
  | just =>
    t := 1
    v : UInt8 <= a
  replace_runtime

end Transmog.Test.RuntimeRepr.Errors
