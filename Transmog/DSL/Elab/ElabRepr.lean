/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Transmog.DSL.Core.Cast
public meta import Transmog.DSL.Elab.ToIR
public meta import Transmog.DSL.Tactics

/-!
# `DataRepr` elaboration

The emitters fold over the checked IR: every conversion decision was resolved in the `ToIR`
pass, so the code here is plain syntax assembly.  All bodies are arrays of `Arm`s (a structure
is a single unguarded arm), so one set of emitters serves structures and inductives alike.
-/

meta section

namespace Transmog.DSL.ElabRepr

open Lean Parser Elab Command Term

/-! ## Context and monad -/

/--
The generated implementations that a word-backed runtime representation substitutes for the
codecs and their `DataRepr` instance.
-/
public structure RuntimeHooks where
  toReprImpl   : Ident
  fromReprImpl : Ident
  dataReprImpl : Ident

public structure Context where
  decl             : ReprDecl
  sourceTy         : Term
  /-- The namespace holding the generated declarations, as an absolute user-facing name. -/
  pkg              : Name
  toReprName       : Ident
  fromReprName     : Ident
  fromToName       : Ident
  dataReprInstName : Ident
  reprTy           : Term
  /--
  Reinterpret constrained values with `unsafeCast` instead of proving their obligations with
  `transmog_subtype`.  Only the unsafe runtime helpers set this; they are compiler directives,
  not verified conversions.
  -/
  unsafeProof      : Bool := false
  /-- The word-backed implementations to redirect the codecs to, when the type has one. -/
  runtime?         : Option RuntimeHooks := none

public abbrev M := ReaderT Context CommandElabM

public def M.run (ctx : Context) (x : M α) : CommandElabM α := ReaderT.run x ctx

/-!
## Generated names

A name in syntax is a user-facing name, which the elaborator resolves against the current
namespace and then marks private when the scope calls for it; the constant it produces is a
different thing, and under the module system it carries a private prefix that syntax cannot
spell.  The generated declarations are therefore named absolutely, under `_root_`, from the
user-facing name of the package, and the constant a member receives is computed from the scope
when a consumer needs it.
-/

/-- The member `suffix` of the package `pkg`, as a name to declare or reference in syntax. -/
public def pkgMember (pkg suffix : Name) : Ident :=
  mkIdent (`_root_ ++ pkg ++ suffix)

/--
The constant that a declaration named `userName` receives when elaborated in the current scope,
which in a module is private unless the scope is `public`.  The rule is core's
`Visibility.isInferredPublic`, which reads the exporting state the command elaborator initializes
from the scope.
-/
public def declConstName (userName : Name) : CommandElabM Name := do
  let env ← getEnv
  if Visibility.regular.isInferredPublic env then
    return userName
  return mkPrivateName env userName

/-- The member `suffix` of the package, as a name to declare or reference in syntax. -/
public def Context.member (ctx : Context) (suffix : Name) : Ident :=
  pkgMember ctx.pkg suffix

/-- The constant that the member `suffix` of the package receives in the current scope. -/
public def Context.constName (ctx : Context) (suffix : Name) : CommandElabM Name :=
  declConstName (ctx.pkg ++ suffix)

/-! ## Term building helper functions -/

/--
The subtype value `⟨val, _⟩`, with the `.property` of each support injected into the
obligation's local context first (the local-lemma principle applied to in-body obligations:
codegen knows which values justify the predicate).  In an unsafe helper the value is
reinterpreted with `unsafeCast` instead, which is the identity at run time and creates no proof
term, so nothing enters the auxiliary lemma cache that a safe codec could later pick up.
-/
def mkSubtypeWithAll (supports : Array Term) (val : Term) : M Term := do
  if (← read).unsafeProof then
    `($(mkCIdent ``unsafeCast) $val)
  else
    let haves ← supports.mapM fun s => `(tactic| have := ($s).property)
    let tacs := haves.push (← `(tactic| transmog_subtype))
    `(⟨$val, by $[$tacs:tactic]*⟩)

def mkSubtype (val : Term) : M Term :=
  mkSubtypeWithAll #[] val

def mkSubtypeWith (support val : Term) : M Term :=
  mkSubtypeWithAll #[support] val

public def mkTuple : Array Term → CommandElabM Term
  | #[] => unreachable! -- NOTE: there must be at least one slot, otherwise syntax error.
  | #[x] => pure x
  | xs => do
    let init := xs.back!
    xs.pop.foldrM (init := init) fun x acc =>
      `(($x:term, $acc:term))

def mkProd : Array Term → CommandElabM Term
  | #[] => unreachable! -- NOTE: there must be at least one slot, otherwise syntax error.
  | xs => do
    let init := xs.back!
    xs.pop.foldrM (init := init) fun t acc =>
      `(($t:term) × ($acc:term))

/-- Build a term that projects out the `i`-th component from `prod` of size `n`. -/
public def mkProdProj (prod : Term) (i n : Nat) : CommandElabM Term := do
  if i >= n then
    panic! s!"internal error: product projection {i} out of bounds (n={n})"
  let mut res := prod
  for _ in [0:i] do
    res ← `(($res).2)
  if i + 1 < n then `(($res).1) else return res

/-!
## Value emitters

Both directions fold over `CheckedValue` with no elaboration: the conversions are annotations,
and each gadget is interpreted in exactly one place per direction.
-/

/--
The slot-side value type of a checked tree, i.e., the type the value has before any
field-side conversion applies.
-/
partial def shapeValueTy : CheckedValue → M Term
  | .place _ _ p => do
    let slot := (← read).decl.slots[p.slotIdx]!
    mkSlotElemTy slot.ty p.range?
  | .transform .lsbAsBool .. => `(Bool)
  | .transform .cast .. =>
    throwError "nested `cast` is not supported in the Transmog DSL"
  | .prod comps => do
    mkProd (← comps.mapM shapeValueTy)

/-- Convert `place` to a source value term, with the bit range applied. -/
def placeToValueTerm (place : Place) : M Term := do
  match place.range? with
  | .none => return place.name
  | .some range =>
    let start := Syntax.mkNatLit range.start
    let stop := Syntax.mkNatLit range.stop
    `(($place.name).extractSlice $start:num $stop:num)

/--
Apply a leaf conversion in the decode (`fromRepr`) direction: `val` has the slot-side type
`slotSideTy`, and the result has the field-side type.
-/
def applyConvDecode (conv : FieldConversion) (slotSideTy val : Term) : M Term := do
  match conv with
  | .equiv => return val
  | .project => mkSubtype val
  | .inject => `((($val:term : $slotSideTy:term)).val)
  | .reproject => do
    -- Ascribe: `val` may be an anonymous constructor, which cannot elaborate under `.val`
    -- without an expected type.
    let ascribed ← `(($val:term : $slotSideTy:term))
    mkSubtypeWith ascribed (← `(($ascribed:term).val))
  | .reprProject => do
    let carrierVal ← mkSubtype val
    `($(mkCIdent ``DataRepr.fromRepr) $carrierVal:term)
  | .reprReproject => do
    let ascribed ← `(($val:term : $slotSideTy:term))
    let carrierVal ← mkSubtypeWith ascribed (← `(($ascribed:term).val))
    `($(mkCIdent ``DataRepr.fromRepr) $carrierVal:term)
  | .needCast =>
    `($(mkCIdent ``DataCastT.castFrom) (β := $slotSideTy:term) $val:term)

/--
Apply a leaf conversion in the encode (`toRepr`) direction: `val` has the field-side type,
and the result has the slot-side type `slotSideTy`.
-/
def applyConvEncode (conv : FieldConversion) (slotSideTy val : Term) : M Term := do
  match conv with
  | .equiv => return val
  | .project => `(($val:term).val)
  | .inject => do
    let inner ← mkSubtype val
    `(($inner:term : $slotSideTy:term))
  | .reproject => do
    let inner ← mkSubtypeWith val (← `(($val:term).val))
    `(($inner:term : $slotSideTy:term))
  | .reprProject => `(($(mkCIdent ``DataRepr.toRepr) $val:term).val)
  | .reprReproject => do
    let carrierVal ← `($(mkCIdent ``DataRepr.toRepr) $val:term)
    let inner ← mkSubtypeWith carrierVal (← `(($carrierVal:term).val))
    `(($inner:term : $slotSideTy:term))
  | .needCast =>
    `($(mkCIdent ``DataCastT.castTo) (β := $slotSideTy:term) $val:term)

/-- Build the field-side value term of a checked tree, for `fromRepr`. -/
public partial def mkDecodeTerm : CheckedValue → M Term
  | .place conv _ p => do
    let slot := (← read).decl.slots[p.slotIdx]!
    let slotTy ← mkSlotElemTy slot.ty p.range?
    -- Make bit slice subtyping value.
    let placeVal ← if p.range?.isSome then
        mkSubtype (← placeToValueTerm p)
      else placeToValueTerm p
    applyConvDecode conv slotTy placeVal
  | .transform .cast _ _ inner => do
    let innerVal ← mkDecodeTerm inner
    let castTy ← shapeValueTy inner
    `($(mkCIdent ``DataCastT.castFrom) (β := $castTy:term) $innerVal:term)
  | .transform .lsbAsBool conv _ inner => do
    let .place _ _ p := inner
      | throwError "internal error: `lsbAsBool` expects an atomic place"
    let raw ← placeToValueTerm p
    applyConvDecode conv (← `(Bool)) (← `(($raw).lsbAsBool))
  | .prod comps => do
    mkTuple (← comps.mapM mkDecodeTerm)

/--
Generate the `Write`s that write `val` (of the field-side type) to the slots, for
`toRepr`.
-/
public partial def mkEncodeWrites (val : Term) : CheckedValue → M (Array Write)
  | .place conv _ p => do
    let slot := (← read).decl.slots[p.slotIdx]!
    let slotTy ← mkSlotElemTy slot.ty p.range?
    let assignValue ← applyConvEncode conv slotTy val
    let bareValue ←
      if p.range?.isSome then `(($assignValue:term).val) else pure assignValue
    return #[⟨p, bareValue⟩]
  | .transform .cast _ _ inner => do
    let castTy ← shapeValueTy inner
    let innerVal ← `($(mkCIdent ``DataCastT.castTo) (β := $castTy:term) $val:term)
    mkEncodeWrites innerVal inner
  | .transform .lsbAsBool conv _ inner => do
    let .place _ _ p := inner
      | throwError "internal error: `lsbAsBool` expects an atomic place"
    let boolVal ← applyConvEncode conv (← `(Bool)) val
    let slotTy := (← read).decl.slots[p.slotIdx]!.ty
    let .some bitWidth := getUIntBitWidth? slotTy | unreachable!
    let boolToUIntFn := mkCIdent (`Bool ++ .mkSimple s!"toUInt{bitWidth}")
    return #[⟨p, ← `($boolToUIntFn $boolVal)⟩]
  | .prod comps => do
    let mut writes := #[]
    for h : i in [0:comps.size] do
      let valIthProj ← mkProdProj val i comps.size
      writes := writes ++ (← mkEncodeWrites valIthProj comps[i])
    return writes

/--
Collect the support terms recorded by the check pass, the values whose `.property` the proofs
inject, mirroring the product decomposition used by the body emitters.  A field placed through
its representation is supported by that representation.
-/
partial def collectSupports (t : Term) : CheckedValue → M (Array Term)
  | .place conv needsProp _ | .transform _ conv needsProp _ => do
    unless needsProp do return #[]
    if conv.viaRepr then
      return #[← `($(mkCIdent ``DataRepr.toRepr) $t)]
    return #[t]
  | .prod comps => do
    let mut acc := #[]
    for h : i in [0:comps.size] do
      let proj ← mkProdProj t i comps.size
      acc := acc ++ (← collectSupports proj comps[i])
    return acc

/-! ## Write validation -/

/--
The bit span `[start, stop)` a write occupies in its slot; a write with no range replaces
the whole slot value.
-/
def writeSpan (slots : Array Slot) (w : Write) : Nat × Nat :=
  match w.place.range? with
  | .some r => (r.start, r.stop)
  | .none => (0, slots[w.place.slotIdx]!.width)

/--
Reject overlapping writes within one encode scope (an arm).  Two writes to the same span with
syntactically identical values are allowed ; that is the legitimate `guard tag = 0` plus
`tag := 0` duplication.  Everything else would be silently last-wins in slot assembly and only
surface much later as an opaque round-trip failure.
-/
def validateWrites (writes : Array Write) : M Unit := do
  let slots := (← read).decl.slots
  for h₁ : i in [0:writes.size] do
    for h₂ : j in [i+1:writes.size] do
      let w₁ := writes[i]
      let w₂ := writes[j]
      unless w₁.place.slotIdx == w₂.place.slotIdx do
        continue
      let (s₁, e₁) := writeSpan slots w₁
      let (s₂, e₂) := writeSpan slots w₂
      if e₁ ≤ s₂ ∨ e₂ ≤ s₁ then
        continue
      if s₁ == s₂ && e₁ == e₂ then
        unless w₁.value.raw.structEq w₂.value.raw do
          throwErrorAt w₂.place.name
            m!"conflicting writes to `{w₂.place.name.getId}`: this write and an \
              earlier one target the same bits with different values"
      else
        throwErrorAt w₂.place.name
          m!"overlapping bit-range writes to slot `{w₂.place.name.getId}`: \
            [{s₂}:{e₂}) overlaps an earlier write to [{s₁}:{e₁})"

/-! ## Slot assembly and unpack -/

def writePlace (slotVals : NameMap Term) (place : Place) (value : Term) : M Term := do
  match place.range? with
  | .none => return value
  | .some range =>
    let .some old := slotVals.find? place.name.getId
      | panic! s!"internal error: missing generated slot value for `{place.name.getId}`"
    let start := Syntax.mkNatLit range.start
    let stop := Syntax.mkNatLit range.stop
    `(($old).insertSlice $start:num $stop:num $value:term)

/--
The representation tuple assembled from `writes`; a constrained slot is wrapped into its
subtype with the `.property` of each support in scope.
-/
public def buildReprTerm (writes : Array Write) (supports : Array Term := #[]) : M Term := do
  let slots := (← read).decl.slots
  let mut slotVals : NameMap Term := {}
  for slot in slots do
    let ty := mkCIdent slot.ty
    let zero ← `((0 : $ty:ident))
    slotVals := slotVals.insert slot.name.getId zero
  for ⟨place, value⟩ in writes do
    let newVal ← writePlace slotVals place value
    slotVals := slotVals.insert place.name.getId newVal
  let elems ← slots.mapM fun slot => do
    let some raw := slotVals.find? slot.name.getId
      | panic! s!"internal error: missing generated slot value for `{slot.name.getId}`"
    if slot.allProps.isEmpty then
      return raw
    else
      mkSubtypeWithAll supports raw
  mkTuple elems

/--
Unpack slot values and subtype properties (if exist) from `arg`, the term for the argument
of `fromRepr`.
-/
public def unpackSlotTerm (arg body : Term) : M Term := do
  let slots := (← read).decl.slots
  let n := slots.size
  slots.zipIdx.foldrM (init := body) fun (slot, i) acc => do
    let proj ← mkProdProj arg i n
    let name := slot.name
    let ty := mkCIdent slot.ty
    if slot.allProps.isEmpty then
      `(let $name:ident : $ty:ident := $proj:term; $acc:term)
    else
      `(let ⟨$name:ident, _⟩ := $proj:term
        $acc:term)

/-! ## Arm emission -/

/--
The writes of one arm: the guard-inferred writes, the explicit hints, then the field
writes.
-/
public def armWrites (arm : Arm) : M (Array Write) := do
  let guardWrites := arm.guard?.map (·.writes) |>.getD #[]
  let mut fieldWrites := #[]
  for field in arm.fields do
    fieldWrites := fieldWrites ++ (← mkEncodeWrites field.name field.val)
  let writes := guardWrites ++ arm.hints ++ fieldWrites
  validateWrites writes
  return writes

-- `Id.run` supplies the monad expected by the following do block.
set_option linter.hazel.style.preferDotNotation false in
/--
Split the arms into the guarded ones (in declaration order) and the at-most-one unguarded
fallback, with the invariant carried by the types.
-/
public def splitArms (arms : Array Arm) : Array (Guard × Arm) × Option Arm := Id.run do
  let mut guarded := #[]
  let mut unguarded? := .none
  for arm in arms do
    match arm.guard? with
    | .some g => guarded := guarded.push (g, arm)
    -- NOTE: at most one unguarded arm, otherwise already rejected in `ToIR`.
    | .none => unguarded? := .some arm
  return (guarded, unguarded?)

/-- The supports of the fields of one arm, in field order. -/
def armSupports (arm : Arm) : M (Array Term) := do
  arm.fields.foldlM (init := #[]) fun acc field =>
    return acc ++ (← collectSupports field.name field.val)

/-- The constructor application decoding one arm. -/
def armApp (arm : Arm) : M Term := do
  let args ← arm.fields.mapM (mkDecodeTerm ·.val)
  return Syntax.mkApp (mkCIdent arm.ctorName) args

def mkDecodeChain (guarded : List (Guard × Arm)) (unguarded? : Option Arm) : M Term := do
  match guarded with
  | [] => match unguarded? with
    | .some unguarded => armApp unguarded
    | .none => `(unreachable!) -- fallback branch where all guards missed
  | (g, arm) :: rest =>
    let app ← armApp arm
    let restTerm ← mkDecodeChain rest unguarded?
    `(if h : $g.cond:term then $app:term else $restTerm:term)

/-! ## Command generators -/

/--
The attribute each codec carries.  A word-backed type redirects them to the packed-word
implementations, which also keeps the logical bodies from being inlined anywhere.
-/
def codecAttrs : M (TSyntax ``Term.attrInstance × TSyntax ``Term.attrInstance) := do
  match (← read).runtime? with
  | .none => return (← `(Term.attrInstance| inline), ← `(Term.attrInstance| inline))
  | .some hooks =>
    return (← `(Term.attrInstance| implemented_by $hooks.toReprImpl),
            ← `(Term.attrInstance| implemented_by $hooks.fromReprImpl))

def armCommands (arms : Array Arm) : M Command := do
  let { sourceTy, reprTy, toReprName, fromReprName, .. } ← read
  let (guarded, unguarded?) := splitArms arms
  if unguarded?.isNone then
    liftTermElabM do
      let inhTy ← Meta.mkAppM ``Inhabited #[← ToIR.elabTypeStrict sourceTy]
      match ← Meta.trySynthInstance inhTy with
      | .some _ => pure ()
      | _ => throwError m!"\
          every constructor of `{sourceTy}` is guarded, so the generated \
          `fromRepr` needs `Inhabited {sourceTy}` for its fallback branch; \
          add a `deriving Inhabited` clause, provide an instance, or leave \
          one constructor unguarded"
  let alts ← arms.mapM fun arm => do
    let fieldPats := arm.fields.map (·.name)
    let reprExpr ← buildReprTerm (← armWrites arm) (← armSupports arm)
    let pat := Syntax.mkApp (mkCIdent arm.ctorName) fieldPats
    `(matchAltExpr| | $pat:term => $reprExpr:term)
  let reprParam := mkIdent <| ← liftCoreM <| mkFreshUserName `repr
  let fromBody ← unpackSlotTerm reprParam (← mkDecodeChain guarded.toList unguarded?)
  let (toAttr, fromAttr) ← codecAttrs
  return ← `(
    @[$toAttr:attrInstance, expose] def $toReprName : $sourceTy → $reprTy
      $[$alts:matchAlt]*
    @[$fromAttr:attrInstance, expose] def $fromReprName ($reprParam : $reprTy) : $sourceTy :=
      $fromBody
  )

def typeAliasCommands : M Command := do
  let { sourceTy, reprTy, toReprName, fromReprName, .. } ← read
  let conv ← liftTermElabM do
    let α ← ToIR.elabTypeStrict sourceTy
    let β ← ToIR.elabTypeStrict reprTy
    ToIR.classifyFieldConversionExpr α β
  match conv with
  | .equiv =>
    return ← `(
      @[inline, expose] def $toReprName:ident : $sourceTy:term → $reprTy:term := id
      @[inline, expose] def $fromReprName:ident : $reprTy:term → $sourceTy:term := id
    )
  | .project =>
    return ← `(
      @[inline, expose] def $toReprName:ident (x : $sourceTy:term) : $reprTy:term :=
        x.val
      @[inline, expose] def $fromReprName:ident (x : $reprTy:term) : $sourceTy:term :=
        ⟨x, by transmog_subtype⟩
    )
  | .inject =>
    return ← `(
      @[inline, expose] def $toReprName:ident (x : $sourceTy:term) : $reprTy:term :=
        ⟨x, by transmog_subtype⟩
      @[inline, expose] def $fromReprName:ident (x : $reprTy:term) : $sourceTy:term :=
        x.val
    )
  | .reproject =>
    return ← `(
      @[inline, expose] def $toReprName:ident (x : $sourceTy:term) : $reprTy:term :=
        ⟨x.val, by have := x.property; transmog_subtype⟩
      @[inline, expose] def $fromReprName:ident (x : $reprTy:term) : $sourceTy:term :=
        ⟨x.val, by have := x.property; transmog_subtype⟩
    )
  | .reprProject =>
    return ← `(
      @[inline, expose] def $toReprName:ident (x : $sourceTy:term) : $reprTy:term :=
        ($(mkCIdent ``DataRepr.toRepr) x).val
      @[inline, expose] def $fromReprName:ident (x : $reprTy:term) : $sourceTy:term :=
        $(mkCIdent ``DataRepr.fromRepr) ⟨x, by transmog_subtype⟩
    )
  | .reprReproject =>
    let carrierVal ← `($(mkCIdent ``DataRepr.toRepr) x)
    return ← `(
      @[inline, expose] def $toReprName:ident (x : $sourceTy:term) : $reprTy:term :=
        ⟨($carrierVal:term).val, by have := ($carrierVal:term).property; transmog_subtype⟩
      @[inline, expose] def $fromReprName:ident (x : $reprTy:term) : $sourceTy:term :=
        $(mkCIdent ``DataRepr.fromRepr) ⟨x.val, by have := x.property; transmog_subtype⟩
    )
  | .needCast =>
    return ← `(
      @[inline, expose] def $toReprName:ident (x : $sourceTy:term) : $reprTy:term :=
        $(mkCIdent ``DataCastT.castTo) x
      @[inline, expose] def $fromReprName:ident (x : $reprTy:term) : $sourceTy:term :=
        $(mkCIdent ``DataCastT.castFrom) x
    )

/-! ## Context construction -/

public def mkContext (decl : ReprDecl) : CommandElabM Context := do
  let sourceName := decl.sourceName
  let sourceTy := decl.sourceRef
  let reprTy ← mkProd (← decl.slots.mapM (·.mkType))
  let instName ← mkInstanceName #[] (← `(DataRepr $sourceTy $reprTy))
  -- A bare type holds its package in its own namespace, as `T.Repr`.  An instantiation has no
  -- namespace of its own, and its instance name is the one name the declaration is guaranteed
  -- to own, so the package lives under it and is reached through the class.
  let pkg ← if decl.sourceExpr.isConst then
      pure (privateToUserName sourceName ++ `Repr)
    else
      pure ((← getCurrNamespace) ++ instName)
  let toReprName := pkgMember pkg `toRepr
  let fromReprName := pkgMember pkg `fromRepr
  let fromToName := pkgMember pkg `from_to
  let dataReprInstName : Ident := mkIdent instName
  return {
    decl
    sourceTy
    pkg
    toReprName
    fromReprName
    fromToName
    dataReprInstName
    reprTy
  }

/-! ## Round-trip proof generation -/

/--
Build the tactic block for one arm's case.  Property `have`s for the arm's supports, then the
finisher.
-/
def mkCaseTacticBlock (arm : Arm) : M Term := do
  let { toReprName, fromReprName, .. } ← read
  let mut tacs : Array (TSyntax `tactic) := #[]
  for s in ← armSupports arm do
    tacs := tacs.push (← `(tactic| have := ($s:term).property))
  tacs := tacs.push
    (← `(tactic| transmog_from_to_case [$toReprName:ident, $fromReprName:ident]))
  `(by $[$tacs:tactic]*)

/-- Build the default `from_to` proof term. -/
def mkFromToProof : M Term := do
  let { decl, toReprName, fromReprName, .. } ← read
  match decl.arms? with
  | .none =>
    `(by transmog_from_to [$toReprName:ident, $fromReprName:ident])
  | .some arms =>
    let alts ← arms.mapM fun arm => do
      let fieldPats := arm.fields.map (·.name)
      let pat := Syntax.mkApp (mkCIdent arm.ctorName) fieldPats
      let caseBlock ← mkCaseTacticBlock arm
      `(matchAltExpr| | $pat:term => $caseBlock:term)
    `(fun x => match x with $alts:matchAlt*)

/-! ## Entrance -/

/--
Run a nested command and report whether it elaborated cleanly.  Nested elaboration failures are
logged, not thrown, so the message-log delta is the way to observe them (the same mechanism
`#guard_msgs` builds on).  When errors were already present the delta cannot be attributed, so
the command is optimistically reported clean rather than double-suppressed.

The report is meaningful for definitions and instances only.  The body of a nested `theorem` is
elaborated in a separate task under `Elab.async`, and its messages reach the snapshot tree
rather than this log.
-/
public def elabCommandOk (cmd : Command) : CommandElabM Bool := do
  let hadErrors := (← get).messages.hasErrors
  elabCommand cmd
  return hadErrors || !(← get).messages.hasErrors

open Tactic in
/--
Elaborates the full `DataRepr` package for `decl`.  The returned flag is `false` when a generated
definition or the instance failed to elaborate; downstream clause handlers (`derive_layout`) must
skip in that case, since their output would only cascade noise onto the targeted error.  The
round-trip theorem is checked asynchronously and reports on its own; nothing downstream depends
on its proof, only on its name.

`runtime` runs between the naming context and the codecs, which is where a word-backed runtime
representation has to install its helpers: everything it emits must be compiled before any code
that eliminates on the type, and the codecs are the first such code.
-/
public def elabRepr (decl : ReprDecl) (correctBy? : Option (TSyntax ``tacticSeq) := none)
    (runtime : Context → CommandElabM (Option RuntimeHooks) := fun _ => pure none) :
    CommandElabM (Context × Bool) := do
  let ctx ← mkContext decl
  let ctx := { ctx with runtime? := ← runtime ctx }
  let toReprFromReprDef ← (match decl.arms? with
    | .none => typeAliasCommands
    | .some arms => armCommands arms).run ctx
  let { sourceTy, toReprName, fromReprName, fromToName,
        dataReprInstName, reprTy, .. } := ctx
  -- Elaborate the definitions eagerly, before even building the proof syntax: on a misdesigned
  -- layout the targeted error lives here (e.g. an unprovable `transmog_subtype` obligation),
  -- and the round-trip theorem and instance over broken definitions only cascade kernel noise.
  unless ← elabCommandOk toReprFromReprDef do
    return (ctx, false)
  let proof ← match correctBy? with
    | .some tacs => `(by $tacs:tacticSeq)
    | .none => mkFromToProof.run ctx
  elabCommand <| ← `(
    theorem $fromToName : ∀ x : $sourceTy, $fromReprName ($toReprName x) = x :=
      $proof:term
  )

  let instCmd ← match ctx.runtime? with
    | .none => `(
        instance $dataReprInstName:ident : $(mkCIdent ``DataRepr) $sourceTy ($reprTy) where
          toRepr := $toReprName
          fromRepr := $fromReprName
          from_to := $fromToName
      )
    | .some hooks => `(
        @[implemented_by $hooks.dataReprImpl]
        instance $dataReprInstName:ident : $(mkCIdent ``DataRepr) $sourceTy ($reprTy) where
          toRepr := $toReprName
          fromRepr := $fromReprName
          from_to := $fromToName
      )
  return (ctx, ← elabCommandOk instCmd)

end Transmog.DSL.ElabRepr

end -- meta section
