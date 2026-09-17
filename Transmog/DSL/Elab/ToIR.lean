/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean.Elab.Command
public meta import Transmog.DSL.Core.Basic
public meta import Transmog.DSL.Elab.IR

/-!
# Transmog DSL syntax to IR

The single pass from surface syntax to the checked IR.  Besides the structural conversion, this
pass resolves each value leaf's `FieldConversion` against the declared field type (producing
`CheckedValue` trees), normalizes structure bodies into single-arm form, and performs all
environment-independent and coverage validation.
-/

meta section

namespace Transmog.DSL.ToIR

open Lean Elab Command Term Transmog

structure Context where
  sourceRef  : Term
  sourceExpr : Expr
  sourceName : Name
  slots      : Array Slot

abbrev M := ReaderT Context CommandElabM

def M.run (ctx : Context) (x : M α) : CommandElabM α := ReaderT.run x ctx

/-! ## Bit ranges -/

def mkBitRange {k : SyntaxNodeKind}
    (minStart maxStop : Nat) (stx : TSyntax k) (start stop : Nat) : CommandElabM BitRange := do
  if stop > maxStop then
    throwErrorAt stx m!"invalid bit range, expected stop ≤ {maxStop}"
  else if start < minStart then
    throwErrorAt stx m!"invalid bit range, expected start ≥ {minStart}"
  else if start >= stop then
    throwErrorAt stx "invalid bit range, expected start < stop"
  else
    return { start, stop }

def toBitRange (minStart maxStop : Nat)
    (stx : TSyntax `transmogReprRange) : CommandElabM (Option BitRange) := do
  let { start, stop } ← match stx with
  | `(transmogReprRange| [$n:num]) =>
      let start := n.getNat
      mkBitRange minStart maxStop n start (start + 1)
  | `(transmogReprRange| [$[$n:num]? : $[$m:num]?]) =>
      let start := n.map (·.getNat) |>.getD minStart
      let stop := m.map (·.getNat) |>.getD maxStop
      mkBitRange minStart maxStop stx start stop
  | _ => throwErrorAt stx "invalid representation range"

  if start = minStart ∧ stop = maxStop then
    return .none
  else
    return .some { start, stop }

/-! ## Data representation spec -/

def toSlot : TSyntax ``transmogReprSlot → CommandElabM Slot
  | `(transmogReprSlot| $name:ident : $slotTy:transmogReprSlotTy $[// $prop:term]?) => do
    match slotTy with
    | `(transmogReprSlotTy| $ty:ident $[$range:transmogReprRange]?) => do
      let tyName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo ty
      let .some width := getUIntBitWidth? tyName
        | throwErrorAt ty
            "invalid representation slot type, expected UInt8, UInt16, UInt32, or UInt64"
      let range? ←
        match range with
        | .none => pure none
        | .some range => toBitRange 0 width range
      return { name, ty := tyName, width, range?, userProps := prop.toArray }
    | _ => throwErrorAt slotTy "invalid representation slot type"
  | stx => throwErrorAt stx "invalid representation slot"

def toSlots : TSyntax ``transmogReprSpec → CommandElabM (Array Slot)
  | stx@`(transmogReprSpec| [$slots:transmogReprSlot,*]) => do
    unless !slots.getElems.isEmpty do
      throwErrorAt stx "can't have empty representation"
    let slots ← slots.getElems.mapM toSlot
    let mut seen : Array Name := #[]
    for slot in slots do
      let key := slot.name.getId
      if seen.contains key then
        throwErrorAt slot.name m!"duplicate representation slot `{key}`"
      seen := seen.push key
    return slots
  | _ => throwError "invalid representation spec"

/-! ## Places -/

/-- The index and the declaration of the slot named `name`, if there is one. -/
def findSlot? (name : Name) : M (Option (Nat × Slot)) := do
  let slots := (← read).slots
  return slots.findIdx? (·.name.getId == name) |>.map fun i => (i, slots[i]!)

def toPlace : TSyntax ``transmogReprPlace → M Place
  | `(transmogReprPlace| $name:ident $[$range:transmogReprRange]?) => do
    let some (slotIdx, slot) ← findSlot? name.getId
      | throwErrorAt name m!"unknown representation slot `{name.getId}`"
    let (minStart, maxStop) :=
      match slot.range? with
      | .some r => (r.start, r.stop)
      | .none => (0, slot.width)
    let range? ←
      match range with
      | .none => pure .none
      | .some range => toBitRange minStart maxStop range
    return ⟨name, slotIdx, range?⟩
  | stx => throwErrorAt stx "invalid representation place"

/-!
## Field value checking

The check pass resolves the conversion between a field's declared type and the slot-side value
type at each leaf, once.  Under an explicit `cast` there is no field-side type context, so the
inner tree carries no conversions; the `Option Expr` context encodes exactly this.
-/

/--
Elaborate a type syntax to a closed term, with no postponed metavariables, so the `isDefEq`
answers in classification cannot depend on elaboration order.  Elaboration errors propagate
rather than being recovered as `sorry`, since the result feeds further meta computation.
-/
public meta def elabTypeStrict (stx : Term) : TermElabM Expr := do
  let e ← Term.withoutErrToSorry <| Term.elabType stx
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then
    throwErrorAt stx "the type is not fully determined; a type in a representation must be closed"
  return e

/-- The carrier of the `DataRepr` instance of `α`, if there is one. -/
def reprCarrier? (α : Expr) : MetaM (Option Expr) := do
  let u ← Meta.getDecLevel α
  let v ← Meta.mkFreshLevelMVar
  let ρ ← Meta.mkFreshExprMVar (mkSort (mkLevelSucc v))
  let some _ ← Meta.synthInstance? (mkApp2 (mkConst ``DataRepr [u, v]) α ρ) | return none
  instantiateMVars ρ

public meta def classifyFieldConversionExpr (α β : Expr) : MetaM FieldConversion := do
  let α ← Meta.whnfR α
  let β ← Meta.whnfR β
  if ← Meta.isDefEq α β then
    return .equiv
  let αSub := α.isAppOfArity ``Subtype 2
  let βSub := β.isAppOfArity ``Subtype 2
  let αBase := if αSub then α.appFn!.appArg! else α
  let βBase := if βSub then β.appFn!.appArg! else β
  if ← Meta.isDefEq αBase βBase then
    match αSub, βSub with
    | true, false => return .project
    | false, true => return .inject
    | true, true => return .reproject
    | false, false => return .equiv
  -- A field placed through its representation, when the carrier is a `Subtype` of the slot
  -- scalar other than `β` itself; the identity `DataCastT` covers the carrier `β`.
  if !αSub then
    if let some ρ ← reprCarrier? α then
      let ρ ← Meta.whnfR ρ
      if ρ.isAppOfArity ``Subtype 2 then
        if ← Meta.isDefEq ρ.appFn!.appArg! βBase then
          unless ← Meta.isDefEq ρ β do
            return if βSub then .reprReproject else .reprProject
  return .needCast

def decomposeProdExpr (ty : Expr) (n : Nat) : MetaM (Array Expr) := do
  let mut current ← Meta.whnfR ty
  let mut acc := #[]
  for _ in [0:n-1] do
    unless current.isAppOfArity ``Prod 2 do
      throwError "expected a product type with at least {n} factors, got: {current}"
    acc := acc.push current.appFn!.appArg!
    current ← Meta.whnfR current.appArg!
  acc := acc.push current
  return acc

/--
Classify a leaf against the field-side type context: the leaf's conversion, and whether the
field-side value is a `Subtype` whose property the round-trip proof should inject.
-/
def classifyLeaf (α? : Option Expr) (slotSideTy : Term) : M (FieldConversion × Bool) := do
  match α? with
  | .none => return (.equiv, false)
  | .some α => liftTermElabM do
    let β ← elabTypeStrict slotSideTy
    let conv ← classifyFieldConversionExpr α β
    let needsProp := conv.viaRepr || (← Meta.whnfR α).isAppOfArity ``Subtype 2
    return (conv, needsProp)

partial def toCheckedValue (α? : Option Expr) :
    TSyntax `transmogReprFieldValue → M CheckedValue
  | `(transmogReprFieldValue| $place:transmogReprPlace) => do
    let p ← toPlace place
    let slot := (← read).slots[p.slotIdx]!
    let (conv, needsProp) ← classifyLeaf α? (← mkSlotElemTy slot.ty p.range?)
    return .place conv needsProp p
  | `(transmogReprFieldValue| $gadget:ident $val:transmogReprFieldValue) => do
    match gadget.getId with
    | `cast =>
      return .transform .cast .equiv false (← toCheckedValue none val)
    | `lsbAsBool => do
      let `(transmogReprFieldValue| $place:transmogReprPlace) := val
        | throwErrorAt val
            m!"`lsbAsBool` requires an atomic ident (may with bit range), got {val}"
      let p ← toPlace place
      let (conv, needsProp) ← classifyLeaf α? (← `(Bool))
      return .transform .lsbAsBool conv needsProp (.place .equiv false p)
    | _ =>
      throwErrorAt gadget m!"invalid gadget {gadget}, supported ones: `cast`, `lsbAsBool`"
  | `(transmogReprFieldValue| ($vals:transmogReprFieldValue,*)) => do
    let vals := vals.getElems
    match α? with
    | .none => return .prod (← vals.mapM (toCheckedValue none))
    | .some α => do
      let factors ← liftTermElabM <| decomposeProdExpr α vals.size
      let mut comps := #[]
      for h : i in [0:vals.size] do
        comps := comps.push (← toCheckedValue (some factors[i]!) vals[i])
      return .prod comps
  | stx => throwErrorAt stx "invalid representation field value"

/-! ## Arms -/

def toWrites (stx : TSyntax ``transmogReprWrites) : M (Array Field × Array Write) := do
  let `(transmogReprWrites| $[$writes:transmogReprWrite]*) := stx
    | throwErrorAt stx "invalid representation write list"
  let mut fields := #[]
  let mut hints := #[]
  let mut seenFields : Array Name := #[]
  for w in writes do
    match w with
    | `(transmogReprWrite| $name:ident : $ty:term <= $val:transmogReprFieldValue) => do
      let fieldKey := name.getId
      if seenFields.contains fieldKey then
        throwErrorAt name m!"duplicate field `{fieldKey}`"
      seenFields := seenFields.push fieldKey
      let α ← liftTermElabM <| elabTypeStrict ty
      fields := fields.push ⟨name, ty, ← toCheckedValue (some α) val⟩
    | `(transmogReprWrite| $hint:transmogReprHint) => do
      let `(transmogReprHint| $place:transmogReprPlace := $value:term) := hint
        | throwErrorAt hint "invalid representation hint"
      hints := hints.push ⟨← toPlace place, value⟩
    | stx => throwErrorAt stx "invalid representation write"
  return (fields, hints)

/--
A guard is expected to be a conjunction of assertions.  An equation between a slot and a value
asserts, in the `fromRepr` direction, that the slot holds the value, so in the `toRepr`
direction it is the write of that value to the slot; these writes are inferred here.  Other
assertions infer nothing.
-/
partial def inferGuardWrites : Term → M (Array Write)
  | `(($cond:term)) => inferGuardWrites cond
  | `($cur:term ∧ $rest:term) => do
      return (← inferGuardWrites cur) ++ (← inferGuardWrites rest)
  | stx@`($lhs:term = $rhs:term) => do
    let lhsPlace? ← termToPlace? lhs
    let rhsPlace? ← termToPlace? rhs
    match lhsPlace?, rhsPlace? with
    | .some place, .none => return #[⟨place, rhs⟩]
    | .none, .some place => return #[⟨place, lhs⟩]
    | .none, .none => return #[]
    | _, _ => throwErrorAt stx
        "failed to infer writes from the guard, both sides are slot places"
  | _ => return #[]
where
  /--
  The guard is a Lean term, in which a slot can only be named as a bare identifier; a slot
  declared with a bit range is named the same way and denotes its ranged value.
  -/
  termToPlace? : Term → M (Option Place)
    | `($name:ident) => do
      let some (slotIdx, _) ← findSlot? name.getId | return .none
      return .some ⟨name, slotIdx, .none⟩
    | _ => pure .none

/--
The constructor of the source type that an arm names with `key`, matched on user-facing names, so
that a `private` constructor is found under its private constant.
-/
def resolveCtor (key : Ident) : M Name := do
  let { sourceName, .. } ← read
  let inductInfo ← getConstInfoInduct sourceName
  let userName := privateToUserName sourceName ++ key.getId
  let some ctorName := inductInfo.ctors.find? (privateToUserName · == userName)
    | throwErrorAt key m!"unknown constructor `{key.getId}`"
  addConstInfo key ctorName
  return ctorName

def toArm : TSyntax ``transmogReprCtor → M Arm
  | `(transmogReprCtor|
      | $name:ident => $[$guard?:transmogReprGuard]? $writes:transmogReprWrites) => do
    let ctorName ← resolveCtor name
    let guard? ← guard?.mapM fun
      | `(transmogReprGuard| guard $cond:term) => return ⟨cond, ← inferGuardWrites cond⟩
      | stx => throwErrorAt stx "invalid guard"
    let (fields, hints) ← toWrites writes
    return { ctor := name, ctorName, guard?, fields, hints }
  | stx => throwErrorAt stx "invalid constructor representation"

/-! ## Coverage validation and body normalization -/

/--
Check that each field of `arm` is declared with the type the constructor gives it, once the
arguments of the source type are substituted in.  A declared type that differs from the actual
one would otherwise fail only inside the generated definitions.
-/
def checkFieldTypes (arm : Arm) : M Unit := do
  let { sourceExpr, .. } ← read
  let ctorName := arm.ctorName
  let ctorInfo ← getConstInfoCtor ctorName
  let us := sourceExpr.getAppFn.constLevels!
  liftTermElabM do
    let ctorTy := ctorInfo.type.instantiateLevelParams ctorInfo.levelParams us
    let ctorTy ← Meta.instantiateForall ctorTy sourceExpr.getAppArgs
    Meta.forallBoundedTelescope ctorTy ctorInfo.numFields fun xs _ => do
      for x in xs, field in arm.fields do
        let expected ← Meta.inferType x
        let declared ← elabTypeStrict field.ty
        unless ← Meta.isDefEq expected declared do
          throwErrorAt field.ty m!"field `{field.name.getId}` of `{.ofConstName ctorName}` has type\
            {indentExpr expected}\nbut is declared with type{indentExpr declared}"

def validateCtorCoverage (arms : Array Arm) : M Unit := do
  let { sourceRef, sourceName, .. } ← read
  let inductInfo ← getConstInfoInduct sourceName
  for arm in arms do
    let ctorInfo ← getConstInfoCtor arm.ctorName
    if arm.fields.size != ctorInfo.numFields then
      throwErrorAt arm.ctor
        m!"constructor `{arm.ctor.getId}` expects {ctorInfo.numFields} payload fields, \
          but the repr clause provides {arm.fields.size}"
    checkFieldTypes arm
  let provided := arms.map (·.ctorName)
  let missing := inductInfo.ctors.filter (!provided.contains ·)
  unless missing.isEmpty do
    throwErrorAt sourceRef
      m!"don't know how to represent the following constructors of \
        `{.ofConstName sourceName}`: {MessageData.ofList (missing.map .ofConstName)}"

/--
Validate a structure body and normalize it to the single unguarded arm of the structure
constructor, with the fields reordered to constructor argument order.
-/
def toStructArm (fields : Array Field) (hints : Array Write) : M Arm := do
  let { sourceRef, sourceName, .. } ← read
  let env ← getEnv
  unless isStructure env sourceName do
    throwErrorAt sourceRef "structure-like repr requires a Lean structure type"
  let expected := getStructureFields env sourceName
  for field in fields do
    let key := field.name.getId
    unless expected.contains key do
      throwErrorAt field.name m!"`{key}` is not a field of structure `{.ofConstName sourceName}`"
  let provided := fields.map (·.name.getId)
  let missing := expected.filter (!provided.contains ·)
  unless missing.isEmpty do
    throwErrorAt sourceRef
      m!"don't know how to represent the following fields of `{.ofConstName sourceName}`: \
        {missing.toList}"
  let ordered := expected.filterMap fun n => fields.find? (·.name.getId == n)
  let ctorName := (getStructureCtor env sourceName).name
  let short := (privateToUserName ctorName).replacePrefix (privateToUserName sourceName) .anonymous
  let arm := { ctor := mkIdent short, ctorName, fields := ordered, hints }
  checkFieldTypes arm
  return arm

def toArms : TSyntax `transmogReprBody → M (Array Arm)
  | stx@`(transmogReprBody| $[$ctorStxs:transmogReprCtor]*) => do
    if ctorStxs.isEmpty then
      throwErrorAt stx "cannot transmogrify types without runtime data"
    let mut arms := #[]
    let mut seenCtors : Array Name := #[]
    let mut unguardedSeen := false
    for ctorStx in ctorStxs do
      let arm ← toArm ctorStx
      let ctorKey := arm.ctor.getId
      if seenCtors.contains ctorKey then
        throwErrorAt arm.ctor m!"duplicate constructor `{ctorKey}`"
      seenCtors := seenCtors.push ctorKey
      if arm.guard?.isNone then
        if unguardedSeen then
          throwErrorAt arm.ctor
            "enum repr can have at most one unguarded constructor, otherwise ambiguous"
        unguardedSeen := true
      arms := arms.push arm
    validateCtorCoverage arms
    return arms
  | stx@`(transmogReprBody| $writes:transmogReprWrites) => do
    let (fields, hints) ← toWrites writes
    if fields.isEmpty then
      throwErrorAt stx "cannot transmogrify types without runtime data"
    return #[← toStructArm fields hints]
  | stx => throwErrorAt stx "invalid representation body"

/-! ## Entrance -/

/--
Elaborate the source type of a `transmog` declaration.  A type with parameters that is left
unapplied is reported as such, since the fix is to apply it rather than to change it.
-/
public meta def elabSourceType (stx : Term) : TermElabM Expr := do
  let e ← Term.withoutErrToSorry <| Term.elabTerm stx (mkSort (← Meta.mkFreshLevelMVar))
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if ← Meta.isType e then
    if e.hasMVar then
      throwErrorAt stx "the type is not fully determined; the representation belongs to one \
        instantiation, so every argument must be given"
    return e
  if ← Meta.isTypeFormerType (← Meta.inferType e) then
    throwErrorAt stx m!"`{e}` has parameters; a type with parameters is represented one \
      instantiation at a time, so apply it to its arguments"
  throwErrorAt stx m!"type expected, got{indentExpr e}"

/-- Convert a declaration over the source type `sourceExpr`, as elaborated from `sourceRef`. -/
public meta def toIR (sourceRef : Term) (sourceExpr : Expr) (spec : TSyntax ``transmogReprSpec)
    (body? : Option (TSyntax `transmogReprBody)) : CommandElabM ReprDecl := do
  let .const sourceName _ := sourceExpr.getAppFn
    | throwErrorAt sourceRef
        m!"expected a type constant applied to its arguments, got{indentExpr sourceExpr}"
  let slots ← toSlots spec
  let arms? ← body?.mapM fun body => do
    let inductInfo ← getConstInfoInduct sourceName
    if inductInfo.isRec then
      throwErrorAt sourceRef "can't transmogrify recursive Lean types"
    unless inductInfo.numIndices == 0 do
      throwErrorAt sourceRef m!"`{.ofConstName sourceName}` is an indexed family, which is not \
        supported"
    M.run ⟨sourceRef, sourceExpr, sourceName, slots⟩ (toArms body)
  return { sourceRef, sourceExpr, sourceName, slots, arms? }

end Transmog.DSL.ToIR

end -- meta section
