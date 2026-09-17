/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL

/-!
# Tests for the combined declaration forms

`transmog enum` and `transmog struct` declare a type together with its representation.  What
the generated `inductive` and `structure` receive, the instances the `deriving` clause derives
and their availability to the representation, the visibility of the pieces, and the diagnostics
of the two forms.
-/

-- Deliberately ill-formed declarations follow.
set_option linter.hazel false

namespace Transmog.Test.Decl

open Lean Transmog

/-- The doc string of `n`, without the surrounding whitespace. -/
private meta def docOf (n : Name) : MetaM (Option String) := do
  return (← findDocString? (← getEnv) n).map (·.trimAscii.toString)

@[expose] public section

/-! ## An inductive type with its representation -/

abbrev Ptr := { p : UInt32 // p ≠ 0 ∧ p.fitsBits 31 }

transmog Ptr as [p : UInt32[0:31] // p ≠ 0]

/-- A BDD node. -/
transmog enum Node as [n : UInt32[0:31]] where
  /-- The terminal. -/
  | sink => guard n = 0
  /-- An internal node. -/
  | inode (p : Ptr <= n)
deriving Repr, BEq, DecidableEq

/-- info: Transmog.Test.Decl.Node.inode (p : Ptr) : Node -/
#guard_msgs in
#check Node.inode

example : DataRepr Node { n : UInt32 // n.fitsBits 31 } := inferInstance
example : (Node.Repr.toRepr .sink).val = 0 := rfl
example : (Node.Repr.toRepr (.inode ⟨5, by decide⟩)).val = 5 := rfl
example : Node.Repr.fromRepr ⟨5, by decide⟩ = .inode ⟨5, by decide⟩ := by decide
example : (Node.inode ⟨5, by decide⟩ == .sink) = false := by decide

/-- info: Transmog.Test.Decl.Node.inode 5 -/
#guard_msgs in
#eval Node.inode ⟨5, by decide⟩

-- The doc comments reach the type and its constructors.
run_meta do
  for (n, doc) in [(`Transmog.Test.Decl.Node, "A BDD node."),
      (`Transmog.Test.Decl.Node.sink, "The terminal."),
      (`Transmog.Test.Decl.Node.inode, "An internal node.")] do
    unless (← docOf n) == some doc do
      throwError "unexpected doc string on {n}"

/-! ## A guard, a field and a hint on one constructor -/

transmog enum Tagged as [t : UInt8, v : UInt8] where
  | none => guard t = 0
  | some (b : UInt8 <= v) =>
    t := 1
  | other (c : UInt8 <= v) =>
    guard t = 2
deriving DecidableEq

example : Tagged.Repr.toRepr .none = (0, 0) := rfl
example : Tagged.Repr.toRepr (.some 7) = (1, 7) := rfl
example : Tagged.Repr.toRepr (.other 7) = (2, 7) := rfl
example : Tagged.Repr.fromRepr (2, 7) = .other 7 := by decide
example : Tagged.Repr.fromRepr (1, 7) = .some 7 := by decide

/-! ## Two fields on one constructor, and a layout -/

transmog enum Two as [x : UInt8, y : UInt8] where
  | pair (a : UInt8 <= x) (b : UInt8 <= y)
derive_layout C packed
deriving Repr, DecidableEq

example : Two.Repr.toRepr (.pair 1 2) = (1, 2) := rfl
example : Two.Repr.fromRepr (1, 2) = .pair 1 2 := rfl
example : (HasLayout.layout (α := Two)).size = 2 := rfl

/-! ## The derived instances serve the representation -/

-- Without a `replace_runtime` clause the instances are derived before the representation, so
-- the fallback branch of `fromRepr` finds `Inhabited` and the `correct_by` proof finds
-- `DecidableEq`.
transmog enum Bit as [b : UInt8] where
  | zero => guard b = 0
  | one => guard b = 1
correct_by
  transmog_from_to []
deriving DecidableEq, Inhabited

example : Bit.Repr.fromRepr 1 = .one := by decide
example : Bit.Repr.fromRepr 7 = default := by decide

/-! ## Constructor modifiers -/

transmog enum Modified as [t : UInt8, v : UInt8] where
  | protected zero => guard t = 0
  | private one (b : UInt8 <= v) => t := 1

example : Modified.Repr.toRepr (.one 3) = (1, 3) := rfl
example : Modified.Repr.fromRepr (1, 3) = .one 3 := rfl

run_meta do
  let env ← getEnv
  unless isProtected env `Transmog.Test.Decl.Modified.zero do
    throwError "`zero` is not protected"
  let one ← realizeGlobalConstNoOverload (mkIdent `Transmog.Test.Decl.Modified.one)
  unless isPrivateName one do
    throwError "`one` is not private"

/-! ## Field modifiers -/

-- A private field makes the constructor private, and core's deriving handlers reject such a
-- type in an exposed section, so nothing is derived here.
transmog struct Sealed as [a : UInt8, b : UInt8] where
  private x : UInt8 <= a
  protected y : UInt8 <= b

example : Sealed.Repr.toRepr ⟨1, 2⟩ = (1, 2) := rfl
example : Sealed.Repr.fromRepr (1, 2) = ⟨1, 2⟩ := rfl

run_meta do
  let env ← getEnv
  let x ← realizeGlobalConstNoOverload (mkIdent `Transmog.Test.Decl.Sealed.x)
  unless isPrivateName x do
    throwError "`x` is not private"
  unless isProtected env `Transmog.Test.Decl.Sealed.y do
    throwError "`y` is not protected"

/-! ## A structure with its representation -/

/-- An edge. -/
transmog struct Edge as [r : UInt32] where
  make ::
  /-- The complement bit. -/
  compl : Bool <= lsbAsBool r[0] := false
  node : Node <= r[1:32]
derive_layout C packed
deriving Repr, DecidableEq

/-- info: Transmog.Test.Decl.Edge.make (compl : Bool) (node : Node) : Edge -/
#guard_msgs in
#check Edge.make

-- The default value fills the field.
example : ({ node := .sink } : Edge).compl = false := rfl

example : (DataRepr.toRepr (Edge.make true (.inode ⟨5, by decide⟩)) : UInt32) = 11 := rfl
example : (DataRepr.fromRepr 11 : Edge) = Edge.make true (.inode ⟨5, by decide⟩) := by decide
example : (HasLayout.layout (α := Edge)).size = 4 := rfl

/-- info: { compl := true, node := Transmog.Test.Decl.Node.inode 5 } -/
#guard_msgs in
#eval (DataRepr.fromRepr 11 : Edge)

run_meta do
  for (n, doc) in [(`Transmog.Test.Decl.Edge, "An edge."),
      (`Transmog.Test.Decl.Edge.compl, "The complement bit.")] do
    unless (← docOf n) == some doc do
      throwError "unexpected doc string on {n}"

/-! ## An auto-param and a hint among the fields -/

set_option linter.unusedVariables false in
transmog struct Padded as [x : UInt8, pad : UInt8, y : UInt8] where
  a : UInt8 <= x
  pad := 0xFF
  b : UInt8 <= y := by exact 3

example : Padded.Repr.toRepr { a := 1 } = (1, 0xFF, 3) := rfl
example : Padded.Repr.fromRepr (1, 0, 2) = { a := 1, b := 2 } := rfl

/-! ## A dotted name, an attribute on the type and the exposed deriving form -/

transmog enum Outer.Inner as [t : UInt8] where
  | a => guard t = 0
  | b => t := 1
deriving Repr

/-- info: Transmog.Test.Decl.Outer.Inner.a : Outer.Inner -/
#guard_msgs in
#check Outer.Inner.a

example : Outer.Inner.Repr.toRepr .b = 1 := rfl

@[ext] transmog struct Pt as [a : UInt8, b : UInt8] where
  x : UInt8 <= a
  y : UInt8 <= b

/-- info: @Pt.ext : ∀ {x y : Pt}, x.x = y.x → x.y = y.y → x = y -/
#guard_msgs in
#check @Pt.ext

transmog enum Exposed as [t : UInt8] where
  | a => guard t = 0
  | b => t := 1
deriving @[expose] DecidableEq

example : DecidableEq Exposed := inferInstance

/-! ## Diagnostics -/

/--
error: a type with a representation cannot be `unsafe`; the generated definitions and the round-trip theorem are ordinary declarations
-/
#guard_msgs in
unsafe transmog enum Unsafe as [t : UInt8] where
  | a => guard t = 0
  | b => t := 1

/--
error: a type with a representation cannot be `meta`; the generated definitions and the round-trip theorem are ordinary declarations
-/
#guard_msgs in
meta transmog enum Meta as [t : UInt8] where
  | a => guard t = 0
  | b => t := 1

-- A representation belongs to a closed type, so the grammar has no parameters, and
-- `transmog enum Parametric (α : Type) as ...` is a parse error at the binder.

-- An unknown identifier in a field type is reported as such, whatever the `autoImplicit`
-- setting, and on the field.
/--
error: Unknown identifier `Nonexistent`

Note: It is not possible to treat `Nonexistent` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
-/
#guard_msgs in
transmog enum Unknown as [t : UInt8, v : UInt8] where
  | a => guard t = 0
  | b (x : Option Nonexistent <= v) => t := 1

-- What core rejects on a constructor it reports on the constructor.
/-- error: Invalid attribute: Attributes cannot be added to constructors -/
#guard_msgs in
transmog enum Attributed as [t : UInt8] where
  | a => guard t = 0
  | @[simp] b => t := 1

/-- error: Invalid attribute: Attributes cannot be added to fields -/
#guard_msgs in
transmog struct AttributedField as [a : UInt8] where
  @[simp] x : UInt8 <= a

-- A doc comment before the bar and one after it are both the constructor's.
/-- error: Duplicate doc string -/
#guard_msgs in
transmog enum Documented as [t : UInt8] where
  /-- a -/ | /-- b -/ a => guard t = 0
  | b => t := 1

-- Every constructor guarded and no `Inhabited` derived.
/--
error: every constructor of `Bare` is guarded, so the generated `fromRepr` needs `Inhabited Bare` for its fallback branch; add a `deriving Inhabited` clause, provide an instance, or leave one constructor unguarded
-/
#guard_msgs in
transmog enum Bare as [t : UInt8] where
  | a => guard t = 0
  | b => guard t = 1

-- A constructor list and a field list stop in front of the next declaration.
transmog enum Followed as [t : UInt8] where
  | a => guard t = 0
  | b => t := 1
/-- The declaration after a constructor list. -/
def afterEnum := 1

transmog struct FollowedStruct as [t : UInt8] where
  x : UInt8 <= t
/-- The declaration after a field list. -/
def afterStruct := 1

example : afterEnum + afterStruct = 2 := rfl

-- A `deriving instance` command after a declaration without a `deriving` clause is a
-- command of its own.
transmog enum Underived as [t : UInt8] where
  | a => guard t = 0
  | b => t := 1
deriving instance Repr for Underived

/-- info: Transmog.Test.Decl.Underived.b -/
#guard_msgs in
#eval Underived.b

end

end Transmog.Test.Decl
