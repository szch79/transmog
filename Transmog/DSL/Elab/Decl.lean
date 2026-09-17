/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.DeclModifiers
public meta import Transmog.DSL.Elab.ElabRepr
public meta import Transmog.DSL.Notation

/-!
# The combined declaration forms

`transmog enum` and `transmog struct` declare a type and its representation in one command.  A
command expands to the `inductive` or `structure` declaration, the standalone `transmog`
declaration over it, and a `deriving instance` command for its `deriving` clause, and stops at
the first failure.  The instances are derived right after the type, so that the representation
can use them, unless a `replace_runtime` clause is present, in which case they are derived last,
after the clause has taken effect.  The user's nodes are spliced into the generated declarations
rather than copied, so the messages of the `inductive` and `structure` elaborators land on them.
-/

public meta section

namespace Transmog.DSL.Decl

open Lean Elab Command Parser

/-- The constructor of the generated `inductive`, and the arm of the representation, for `stx`. -/
def expandCtor (stx : TSyntax ``transmogEnumCtor) :
    CommandElabM (TSyntax ``Command.ctor × TSyntax ``transmogReprCtor) := do
  let `(transmogEnumCtor| $[$doc?:docComment]? | $mods:declModifiers $ctor:ident
        $[$fields:transmogCtorField]* $[$tail?:transmogCtorTail]?) := stx
    | throwErrorAt stx "invalid constructor"
  let mut binders : Array Syntax := #[]
  let mut writes : Array (TSyntax `transmogReprWrite) := #[]
  for field in fields do
    let `(transmogCtorField| ($x:ident : $ty:term <= $val:transmogReprFieldValue)) := field
      | throwErrorAt field "invalid constructor field"
    -- Under the field's ref, so that the binder carries the field's position and the declaration
    -- range of the constructor ends at its last field.
    let (binder, write) ← withRef field do
      return (← `(Term.bracketedBinderF| ($x:ident : $ty)),
        ← `(transmogReprWrite| $x:ident : $ty:term <= $val:transmogReprFieldValue))
    binders := binders.push binder
    writes := writes.push write
  let mut guard? := none
  if let some tail := tail? then
    let `(transmogCtorTail| => $[$g?:transmogReprGuard]? $[$hints:transmogReprHint]*) := tail
      | throwErrorAt tail "invalid constructor"
    guard? := g?
    for hint in hints do
      writes := writes.push (← `(transmogReprWrite| $hint:transmogReprHint))
  -- Core's `ctor` node, built by layout from the doc comment, the bar, the modifiers, the name
  -- and the signature, which here consists of the binders alone.
  let ctorNode := mkNode ``Command.ctor
    #[mkNullNode (doc?.map (·.raw)).toArray, stx.raw[1], mods, ctor,
      mkNode ``Command.optDeclSig #[mkNullNode binders, mkNullNode #[]]]
  let arm ← `(transmogReprCtor|
    | $ctor:ident => $[$guard?:transmogReprGuard]? $[$writes:transmogReprWrite]*)
  return (⟨ctorNode⟩, arm)

/--
The field of the generated `structure`, when `stx` is a field rather than a slot hint, and the
representation write for `stx`.
-/
def expandStructWrite (stx : TSyntax `transmogStructWrite) :
    CommandElabM (Option (TSyntax ``Command.structSimpleBinder) × TSyntax `transmogReprWrite) := do
  match stx with
  | `(transmogStructWrite| $mods:declModifiers $x:ident : $ty:term <= $val:transmogReprFieldValue
        $[$default?]?) =>
    -- Core's `structSimpleBinder` node, built by layout from the modifiers, the name, the
    -- signature, which here consists of the type alone, and the default or auto-param.
    let typeSpec := mkNode ``Term.typeSpec #[stx.raw[2], ty]
    let binder := mkNode ``Command.structSimpleBinder
      #[mods, x, mkNode ``Command.optDeclSig #[mkNullNode #[], mkNullNode #[typeSpec]],
        mkNullNode (default?.map (·.raw)).toArray]
    let write ← withRef stx
      `(transmogReprWrite| $x:ident : $ty:term <= $val:transmogReprFieldValue)
    return (some ⟨binder⟩, write)
  | `(transmogStructWrite| $hint:transmogReprHint) =>
    return (none, ← withRef stx `(transmogReprWrite| $hint:transmogReprHint))
  | _ => throwErrorAt stx "invalid field"

/-- The `deriving instance` command for the `deriving` clause `stx` of the type `name`. -/
def expandDeriving (name : Ident) (stx : TSyntax ``transmogDeriving) : CommandElabM Command := do
  let `(transmogDeriving| deriving $[$classes:derivingClass],*) := stx
    | throwErrorAt stx "invalid `deriving` clause"
  withRef stx `(deriving instance $[$classes:derivingClass],* for $name:ident)

/-- Whether the clauses `suffixes` contain a `replace_runtime` clause. -/
def hasReplaceRuntime (suffixes : TSyntax ``transmogSuffixes) : Bool :=
  match suffixes with
  | `(transmogSuffixes| $[$rr?:transmogReplaceRuntime]? $[$_dl?]? $[$_cb?]?) => rr?.isSome
  | _ => false

/--
Elaborate the commands the combined declaration `stx` with the modifiers `mods` expands to,
stopping at the first that fails, so that a rejected type declaration is not followed by
messages about the missing type.  The instances are derived before the representation when
`derivingFirst` holds, and after it otherwise.  The representation and the derived instances
take the visibility of the type, so a `private` type in a `public section` gets a private
package, and a `public` type in a private scope a public one.
-/
def elabExpansion (stx : Syntax) (mods : TSyntax ``Command.declModifiers)
    (typeCmd reprCmd : Command) (derivingCmd? : Option Command) (derivingFirst : Bool) :
    CommandElabM Unit := do
  let typeIsPublic ← withExporting (isExporting := (← getScope).isPublic) do
    let modifiers ← elabModifiers mods
    if modifiers.isUnsafe then
      throwErrorAt mods.raw[5] "a type with a representation cannot be `unsafe`; the generated \
        definitions and the round-trip theorem are ordinary declarations"
    if modifiers.computeKind matches .meta then
      throwErrorAt mods.raw[4] "a type with a representation cannot be `meta`; the generated \
        definitions and the round-trip theorem are ordinary declarations"
    return modifiers.isInferredPublic (← getEnv)
  -- The grammar has no parameters, so an unknown identifier in a field type is an error, not
  -- an automatically bound parameter, whatever the package's `autoImplicit` setting.
  let typeCmd ← `(command| set_option autoImplicit false in $typeCmd:command)
  let derivingCmds := derivingCmd?.toArray
  let cmds := if derivingFirst then #[typeCmd] ++ derivingCmds ++ #[reprCmd]
    else #[typeCmd, reprCmd] ++ derivingCmds
  withMacroExpansion stx (mkNullNode cmds) do
    unless ← ElabRepr.elabCommandOk typeCmd do return
    withScope (fun sc => { sc with isPublic := typeIsPublic }) do
      if derivingFirst then derivingCmds.forM elabCommand
      unless ← ElabRepr.elabCommandOk reprCmd do return
      unless derivingFirst do derivingCmds.forM elabCommand

elab_rules : command
  | `($mods:declModifiers transmog enum $name:ident as $spec:transmogReprSpec where
        $[$ctors:transmogEnumCtor]* $[$suffixes?:transmogSuffixes]?
        $[$deriving?:transmogDeriving]?) => do
    let (ctors, arms) := Array.unzip (← ctors.mapM expandCtor)
    let typeCmd ← `($mods:declModifiers inductive $name:ident where $ctors*)
    let reprCmd ← `(transmog $name:ident as $spec:transmogReprSpec where
      $[$arms:transmogReprCtor]* $[$suffixes?:transmogSuffixes]?)
    elabExpansion (← getRef) mods typeCmd reprCmd (← deriving?.mapM (expandDeriving name))
      (derivingFirst := !suffixes?.any hasReplaceRuntime)
  | `($mods:declModifiers transmog struct $name:ident as $spec:transmogReprSpec where
        $[$ctor?:structCtor]? $fields:transmogStructFields $[$suffixes?:transmogSuffixes]?
        $[$deriving?:transmogDeriving]?) => do
    let `(transmogStructFields| $[$fields:transmogStructWrite]*) := fields
      | throwErrorAt fields "invalid fields"
    let (binders?, writes) := Array.unzip (← fields.mapM expandStructWrite)
    let binders := binders?.filterMap id
    let typeCmd ← `($mods:declModifiers structure $name:ident where
      $[$ctor?:structCtor]? $binders*)
    let reprCmd ← `(transmog $name:ident as $spec:transmogReprSpec where
      $[$writes:transmogReprWrite]* $[$suffixes?:transmogSuffixes]?)
    elabExpansion (← getRef) mods typeCmd reprCmd (← deriving?.mapM (expandDeriving name))
      (derivingFirst := !suffixes?.any hasReplaceRuntime)

end Transmog.DSL.Decl

end -- public meta section
