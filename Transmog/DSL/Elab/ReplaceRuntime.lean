/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Compiler.CSimpAttr
public meta import Lean.Compiler.LCNF.PhaseExt
public meta import Lean.Compiler.LCNF.ToImpureType
public meta import Lean.Meta.Constructions.CtorIdx
public meta import Transmog.DSL.Elab.ElabRepr
public meta import Transmog.DSL.Runtime.Basic
public meta import Transmog.DSL.Runtime.Retag

/-!
# The `replace_runtime` clause

Generates the helpers that mediate between an inductive and its packed-word runtime
representation, and registers them so that the code generator passes can route every construction
and elimination through them.

All helpers are derived from the same `transmog` declaration the codecs are derived from, so one
description fixes the packing.  The helpers that reinterpret a value, and those that recover a
constrained field without re-deriving its invariant, are `unsafe`: they are compiler directives at
the same level of trust as `implemented_by`, not verified conversions.  What stays kernel-checked
is the `transmog` declaration itself, including its round-trip theorem.

Helpers are emitted in two batches.  The first holds everything that only computes on the packed
word, which must exist before the representation is registered; the second holds the declarations
that eliminate on the type, which must be compiled after it, so that the lowering pass rewrites
them.

The compiler classifies each inductive into an IR type when it is declared, and a type whose every
constructor carries a field is classified as a definite heap reference, on which the backend
performs reference counting without testing for a scalar.  A boxed word does not survive that, so
such a type is rejected unless `transmog.replaceRuntime.overrideClassification` is set, in which
case the clause overrides the classification to `tagged` before compiling anything that mentions
the type.
The override is a point of no return, so every check runs before it.
-/

meta section

namespace Transmog.DSL.ReplaceRuntime

open Lean Parser Elab Command Term
open Transmog.Runtime (ReprInfo registerReprInfo)

/-! ## Packing -/

/-- How the representation slots are laid out inside one machine word. -/
structure Packing where
  /-- The unsigned integer type holding the packed value. -/
  carrier : Name
  /-- Bit width of the carrier. -/
  bits : Nat
  /-- Bit offset of each slot within the carrier. -/
  offsets : Array Nat
  /-- Number of carrier bits each slot occupies. -/
  widths : Array Nat
  /-- Total number of carrier bits in use. -/
  total : Nat

/--
The number of carrier bits a slot occupies.  A ranged slot is written at its declared bit
positions, so it occupies everything up to the top of its range.
-/
def slotWidth (slot : Slot) : Nat :=
  match slot.range? with
  | .some range => range.stop
  | .none => slot.width

/-- The carriers a word-backed representation may use, smallest first. -/
def carrierCandidates : Array (Name × Nat) :=
  #[(``UInt8, 8), (``UInt16, 16), (``UInt32, 32)]

def mkPacking (ref : Syntax) (slots : Array Slot) (carrier? : Option Ident) :
    CommandElabM Packing := do
  let widths := slots.map slotWidth
  let mut offsets := #[]
  let mut total := 0
  for w in widths do
    offsets := offsets.push total
    total := total + w
  let (carrierName, bits) ← match carrier? with
    | .some given =>
      let givenName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo given
      let some entry := carrierCandidates.find? (·.1 == givenName)
        | throwErrorAt given m!"invalid carrier `{.ofConstName givenName}`, expected `UInt8`, \
            `UInt16`, or `UInt32`; a wider carrier allocates when boxed"
      pure entry
    | .none =>
      let some entry := carrierCandidates.find? (total ≤ ·.2)
        | throwErrorAt ref m!"the representation needs {total} bits, but a word-backed runtime \
            representation is limited to 32; `UInt64` and `USize` always allocate when boxed"
      pure entry
  if total > bits then
    throwErrorAt ref m!"the representation needs {total} bits, which does not fit the \
      {bits}-bit carrier `{.ofConstName carrierName}`"
  return { carrier := carrierName, bits, offsets, widths, total }

/-! ## Packed-word terms -/

def natLitOf (ty : Name) (n : Nat) : CommandElabM Term := do
  let lit : TSyntax `num := ⟨Syntax.mkNatLit n⟩
  `(($lit:num : $(mkCIdent ty)))

/-- Convert between two unsigned integer types; the conversions truncate or zero-extend. -/
def convertUInt (src tgt : Name) (e : Term) : CommandElabM Term := do
  if src == tgt then
    return e
  let some bits := getUIntBitWidth? tgt
    | throwError m!"`{.ofConstName tgt}` is not an unsigned integer type"
  return Syntax.mkApp (mkCIdent (src ++ .mkSimple s!"toUInt{bits}")) #[e]

/--
The value of slot `i` recovered from the packed word `raw`.  The topmost slot needs no mask
because `pack` leaves every bit above the total width clear, and a narrowing conversion masks on
its own.
-/
def slotRawTerm (pk : Packing) (slots : Array Slot) (raw : Ident) (i : Nat) :
    CommandElabM Term := do
  let slot := slots[i]!
  let offset := pk.offsets[i]!
  let width := pk.widths[i]!
  let shifted : Term ← if offset == 0 then pure raw else
    `($raw >>> $(← natLitOf pk.carrier offset))
  let converted ← convertUInt pk.carrier slot.ty shifted
  let some slotBits := getUIntBitWidth? slot.ty
    | throwError m!"`{.ofConstName slot.ty}` is not an unsigned integer type"
  if i + 1 == slots.size || width ≥ slotBits then
    return converted
  else
    `($converted &&& $(← natLitOf slot.ty (2 ^ width - 1)))

/-- Assemble the packed word from a representation value. -/
def packBody (pk : Packing) (slots : Array Slot) (reprVal : Ident) : CommandElabM Term := do
  let mut parts := #[]
  for h : i in [0:slots.size] do
    let slot := slots[i]
    let proj ← ElabRepr.mkProdProj reprVal i slots.size
    let bare ← if slot.allProps.isEmpty then pure proj else `(($proj).val)
    let converted ← convertUInt slot.ty pk.carrier bare
    let shifted : Term ← if pk.offsets[i]! == 0 then pure converted else
      `($converted <<< $(← natLitOf pk.carrier pk.offsets[i]!))
    parts := parts.push shifted
  parts.pop.foldrM (init := parts.back!) fun part acc => `($part ||| $acc)

/--
Take a representation value apart from the packed word.  A constrained slot is reinterpreted
with `unsafeCast` rather than proved, as in `ElabRepr.mkSubtypeWithAll`.
-/
def unpackBody (pk : Packing) (slots : Array Slot) (raw : Ident) : CommandElabM Term := do
  let elems ← slots.mapIdxM fun i slot => do
    let value ← slotRawTerm pk slots raw i
    if slot.allProps.isEmpty then pure value else `($(mkCIdent ``unsafeCast) $value)
  ElabRepr.mkTuple elems

/-- Bind every slot name to its value in the packed word, as the `transmog` body expects them. -/
def bindSlots (pk : Packing) (slots : Array Slot) (raw : Ident) (body : Term) :
    CommandElabM Term := do
  slots.zipIdx.foldrM (init := body) fun (slot, i) acc => do
    let value ← slotRawTerm pk slots raw i
    `(let $(slot.name):ident : $(mkCIdent slot.ty):ident := $value; $acc)

/-! ## Generated names -/

/-- The names of one type's generated helpers, in syntax and as constants. -/
structure Names where
  /-- The namespace holding the helpers, as an absolute user-facing name. -/
  pkg : Name
  /-- The prefix of the constants the helpers receive in the current scope. -/
  constBase : Name

/-- The helper `suffix`, as a name to declare or reference in syntax. -/
def Names.rel (ns : Names) (suffix : Name) : Ident := ElabRepr.pkgMember ns.pkg suffix

/-- The constant that the helper `suffix` receives. -/
def Names.full (ns : Names) (suffix : Name) : Name := ns.constBase ++ suffix

def ctorSuffix (role : String) (ctor : Name) : Name :=
  .mkSimple s!"{role}_{ctor}"

def fieldSuffix (ctor field : Name) : Name :=
  .mkSimple s!"field_{ctor}_{field}"

/-! ## Validation -/

register_option experimental.transmog.replaceRuntime : Bool := {
  defValue := false
  descr := "acknowledge that the `replace_runtime` clause is experimental and subject to change; \
    `true` silences the warning that each clause reports"
}

register_option transmog.replaceRuntime.overrideClassification : Bool := {
  defValue := false
  descr := "let `replace_runtime` reclassify each type it applies to as a tagged scalar in the \
    compiler's IR, which admits structures and inductives whose every constructor carries a \
    field, and removes reference counting on all of them. WARNING: setting this option to true \
    may corrupt memory, because the compiler takes the classification on trust; a value that \
    turns out to be a heap object after all is freed by nobody or dereferenced as a scalar, \
    without any error. The override also writes to a table that is private to the compiler, so \
    it depends on the pinned toolchain"
}

register_option debug.transmog.skipStaleCheck : Bool := {
  defValue := false
  descr := "skip the check that rejects declarations compiled before a `replace_runtime` clause, \
    leaving the code generator's verification pass as the only guard; this exists to test that \
    pass"
}

/-- The module holding the code generator passes; consumers need its IR to install them. -/
def passModule : Name := `Transmog.DSL.Runtime.Pass

/--
Whether the pass module is reachable through exported imports with a `meta` edge, which is what
makes the passes available to every module that imports this one.
-/
partial def reachesPassModule (env : Environment) : Bool :=
  go (exportedEdges env.header.imports false) {}
where
  /-- The reachable next states of an import list, carrying whether a `meta` edge was crossed. -/
  exportedEdges (imports : Array Import) (viaMeta : Bool) : Array (Name × Bool) :=
    imports.filterMap fun imp =>
      if imp.isExported then some (imp.module, viaMeta || imp.isMeta) else none
  go (queue : Array (Name × Bool)) (visited : Std.HashSet (Name × Bool)) : Bool :=
    match queue.back? with
    | .none => false
    | .some entry@(mod, viaMeta) =>
      let queue := queue.pop
      if visited.contains entry then
        go queue visited
      else if mod == passModule && viaMeta then
        true
      else
        match env.getModuleIdx? mod with
        | .none => go queue (visited.insert entry)
        | .some idx =>
          let next := exportedEdges env.header.moduleData[idx]!.imports viaMeta
          go (queue ++ next) (visited.insert entry)

/-- Whether already-compiled code touches the native layout of `typeName`. -/
def codeTouchesType (ctors : NameSet) (typeName : Name) (code : Compiler.LCNF.Code .pure) :
    Bool :=
  let scan : StateM Bool Unit := code.forM fun c => do
    match c with
    | .cases cs => if cs.typeName == typeName then set true
    | .let d _ =>
      match d.value with
      | .const declName .. => if ctors.contains declName then set true
      | .proj structName .. => if structName == typeName then set true
      | _ => pure ()
    | _ => pure ()
  (scan.run false).run.2

/--
Whether `name` is one of the declarations Lean generates together with the inductive `typeName`,
by kind rather than by name, so that a user definition placed in the type's namespace is not
mistaken for one.
-/
def isInductiveAuxiliary (env : Environment) (typeName name : Name) : Bool :=
  typeName.isPrefixOf name &&
    (isAuxRecursor env name || isCasesOnLike env name || isRecCore env name ||
      isNoConfusion env name || (isCtorIdxCore? env name).isSome || env.isProjectionFn name ||
      name == typeName ++ `noConfusionType || name.isInternal)

/--
Declarations of this module that were already compiled against the native layout.  Auxiliaries of
the type itself come with the inductive and are unavoidable; anything else is a user declaration
that has to move after the clause.
-/
def scanStale (typeName : Name) (ctors : NameSet) : CommandElabM (Array Name × Array Name) := do
  let env ← getEnv
  let state := Compiler.LCNF.baseExt.getState env
  let entries := state.foldl (init := #[]) fun acc name decl => acc.push (name, decl)
  let mut auxiliaries := #[]
  let mut offenders := #[]
  for (name, decl) in entries do
    let .code code := decl.value | continue
    unless codeTouchesType ctors typeName code do continue
    if isInductiveAuxiliary env typeName name then
      auxiliaries := auxiliaries.push name
    else
      offenders := offenders.push name
  return (auxiliaries, offenders)

/--
Whether a constructor field of mono type `type` is stored with the IR classification of
`typeName`, either because it is `typeName` itself or because it is a structure the compiler
erases to its single relevant field and that field is.  This is the descent the compiler performs
when it lays out a constructor.
-/
partial def storesAs (typeName : Name) (type : Expr) : CoreM Bool := do
  let .const name _ := type.getAppFn | return false
  if name == typeName then return true
  let some info ← Compiler.LCNF.hasTrivialImpureStructure? name | return false
  let ctorType ← Compiler.LCNF.getOtherDeclBaseType info.ctorName []
  let ctorType ← Compiler.LCNF.instantiateForall ctorType type.getAppArgs[*...info.numParams]
  let fieldType := (Compiler.LCNF.getParamTypes ctorType)[info.fieldIdx]!
  storesAs typeName (← Compiler.LCNF.toMonoType fieldType)

/--
Inductives of this module that store a field with the IR classification of `typeName` and were
declared before the clause.  A constructor layout is frozen when its inductive is declared, so
after the classification changes these containers would still count references on the word.
Structures the compiler erases to a single field have no layout of their own and are exempt.
-/
def scanStaleContainers (typeName : Name) : CommandElabM (Array Name) := do
  let env ← getEnv
  let mut offenders := #[]
  for (name, info) in env.constants.map₂.toList do
    let .inductInfo indInfo := info | continue
    if name == typeName then continue
    let stale ← liftCoreM do
      if (← Compiler.LCNF.hasTrivialImpureStructure? name).isSome then return false
      indInfo.ctors.anyM fun ctorName => do
        let ctorInfo ← getConstInfoCtor ctorName
        Meta.MetaM.run' <| Meta.forallTelescopeReducing ctorInfo.type fun xs _ => do
          for x in xs[ctorInfo.numParams...*] do
            let lcnfType ← Compiler.LCNF.toLCNFType (← Meta.inferType x)
            if ← storesAs typeName (← Compiler.LCNF.toMonoType lcnfType) then return true
          return false
    if stale then
      offenders := offenders.push name
  return offenders

/-! ## Eliminator implementations -/

/--
Redefine `srcName`, an eliminator of `typeName` that the code generator either rejects or compiled
against the native layout, in terms of `casesOn`, which the lowering pass rewrites.  The
replacement equality holds by reflexivity and is kernel-checked.
-/
def mkEliminatorImpl (typeName srcName targetName thmName : Name) : CommandElabM Unit :=
  -- As for a definition without `@[expose]`, the body is not exported.
  liftTermElabM <| withoutExporting do
    let info ← getConstInfo srcName
    let levelParams := info.levelParams
    let us := levelParams.map mkLevelParam
    let value ← Meta.forallTelescope info.type fun xs _ => do
      let motive := xs[0]!
      let mut major? := none
      let mut minors := #[]
      for x in xs[1...*] do
        if major?.isNone && (← Meta.inferType x).getAppFn == Lean.mkConst typeName then
          major? := some x
        else
          minors := minors.push x
      let some major := major?
        | throwError m!"`{.ofConstName srcName}` does not eliminate a value of \
            `{.ofConstName typeName}`"
      let body := mkAppN (Lean.mkConst (typeName ++ `casesOn) us) (#[motive, major] ++ minors)
      Meta.mkLambdaFVars xs body
    addDecl <| .defnDecl {
      name := targetName, levelParams, type := info.type, value
      hints := .abbrev, safety := .safe
    }
    Meta.setInlineAttribute targetName
    compileDecls #[targetName]
    let lhs := Lean.mkConst srcName us
    addDecl <| .thmDecl {
      name := thmName, levelParams
      type := ← Meta.mkEq lhs (Lean.mkConst targetName us)
      value := ← Meta.mkEqRefl lhs
    }
    Compiler.CSimp.add thmName .global

/-! ## Entrance -/

/--
Elaborate the `replace_runtime` clause for the `transmog` declaration described by `ctx`, and return
the implementations the codecs should be redirected to.  Returns `none` after reporting a
precondition failure, in which case the type keeps the ordinary object layout.
-/
public def generate (ctx : ElabRepr.Context) (ref : Syntax) (carrier? : Option Ident) :
    CommandElabM (Option ElabRepr.RuntimeHooks) := do
  let decl := ctx.decl
  let typeName := decl.sourceName
  let sourceTy := ctx.sourceTy
  let env ← getEnv
  if (env.getModuleIdxFor? typeName).isSome then
    logErrorAt ref m!"`{.ofConstName typeName}` is not declared in this module; `replace_runtime` \
      changes how the type is compiled everywhere, so it must appear where the type is declared"
    return none
  if env.header.isModule && !(← getScope).isPublic then
    logErrorAt ref m!"`{sourceTy}` is private, and so would be the `csimp` lemmas that \
      `replace_runtime` emits, which must be public; make the type public, in a \
      `public section` and without `private`"
    return none
  let some arms := decl.arms?
    | logErrorAt ref m!"`replace_runtime` needs a constructor-by-constructor representation"
      return none
  let indInfo ← getConstInfoInduct typeName
  unless indInfo.numParams == 0 && indInfo.numIndices == 0 && indInfo.levelParams.isEmpty do
    logErrorAt ref m!"`{.ofConstName typeName}` has parameters, indices or universe parameters, \
      which a word-backed representation does not support; the compiler represents an inductive \
      type the same way for all of its instantiations, so none of them can be word-backed on its \
      own"
    return none
  if (← liftCoreM <| Compiler.LCNF.hasTrivialImpureStructure? typeName).isSome then
    logErrorAt ref m!"`{.ofConstName typeName}` has one constructor with one relevant field, so \
      the compiler already represents it by that field alone; `replace_runtime` has nothing to add"
    return none
  let retag := transmog.replaceRuntime.overrideClassification.get (← getOptions)
  let impureType ← liftCoreM <| Compiler.LCNF.nameToImpureType typeName
  if impureType == Compiler.LCNF.ImpureType.object then
    unless retag do
      logErrorAt ref m!"every constructor of `{.ofConstName typeName}` carries a field, so the \
        compiler represents it as a definite heap reference and counts references on it without \
        testing \
        for a scalar, which a boxed word does not survive.  Setting \
        `transmog.replaceRuntime.overrideClassification` lets `replace_runtime` override that \
        classification; read the option's description before enabling it"
      return none
  else if impureType != Compiler.LCNF.ImpureType.tobject then
    logErrorAt ref m!"every constructor of `{.ofConstName typeName}` is already fieldless, so the \
      compiler already represents it as a scalar; `replace_runtime` has nothing to add"
    return none
  -- Proof and type fields have no runtime value to recover from the word.
  for ctorName in indInfo.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let bad ← liftTermElabM <| Meta.forallTelescope ctorInfo.type fun xs _ => do
      for x in xs[ctorInfo.numParams...*] do
        let ty ← Meta.inferType x
        if (← Meta.isProp ty) || (← Meta.isTypeFormerType ty) then return true
      return false
    if bad then
      logErrorAt ref m!"constructor `{.ofConstName ctorName}` carries a proof or type field, which \
        a word-backed representation cannot recover from the packed word"
      return none
  if env.header.isModule && !reachesPassModule env then
    logErrorAt ref m!"this module does not re-export a path to `{passModule}`, so modules \
      importing it would compile `{.ofConstName typeName}` without the runtime representation \
      passes; import Transmog with `public import Transmog.DSL`"
    return none
  unless experimental.transmog.replaceRuntime.get (← getOptions) do
    let retagNote : MessageData := if retag then
      m!", and overrides the compiler's IR classification of `{.ofConstName typeName}` as \
        `transmog.replaceRuntime.overrideClassification` requests" else ""
    logWarningAt ref m!"The `replace_runtime` clause is experimental and depends on how the \
      current Lean compiler lowers inductive types; it gives up the object layout of \
      `{.ofConstName typeName}` for a boxed machine word, at the same level of trust as \
      `implemented_by`{retagNote}; \
      `set_option experimental.transmog.replaceRuntime true` acknowledges its experimental status \
      and silences this warning."
  let pk ← mkPacking ref decl.slots carrier?
  -- Report code that was compiled before the clause; it still uses the object layout.
  let ctorSet : NameSet := indInfo.ctors.foldl (·.insert ·) {}
  let (staleAux, offenders) ← scanStale typeName ctorSet
  unless debug.transmog.skipStaleCheck.get (← getOptions) || offenders.isEmpty do
    logErrorAt ref m!"the following declarations were compiled before `replace_runtime` and \
      still use the object layout of `{.ofConstName typeName}`: \
      {MessageData.ofList (offenders.toList.map .ofConstName)}\n\n\
      Move them after the `transmog` declaration, including any `deriving` clause written on the \
      `inductive` itself, or declare the type with `transmog enum`, whose `deriving` clause runs \
      after the clause"
    return none
  -- A container laid out before the classification changes would count references on the word.
  -- No later pass can see this, so the check is not subject to `debug.transmog.skipStaleCheck`.
  if retag then
    let containers ← scanStaleContainers typeName
    unless containers.isEmpty do
      logErrorAt ref m!"the following inductives were declared before `replace_runtime` and \
        store a field of `{.ofConstName typeName}` under its previous IR classification: \
        {MessageData.ofList (containers.toList.map .ofConstName)}\n\n\
        Move them after the `transmog` declaration"
      return none

  let pkg := privateToUserName typeName ++ `Runtime
  let names : Names := { pkg, constBase := ← ElabRepr.declConstName pkg }

  let slots := decl.slots
  let carrier := mkCIdent pk.carrier
  let reprTy := ctx.reprTy
  let wordName := names.rel `word
  let ofWordName := names.rel `ofWord
  let packName := names.rel `pack
  let unpackName := names.rel `unpack
  let valueIdent := mkIdent (← liftCoreM <| mkFreshUserName `x)
  let rawIdent := mkIdent (← liftCoreM <| mkFreshUserName `raw)
  let reprIdent := mkIdent (← liftCoreM <| mkFreshUserName `repr)

  -- Batch one: everything that only computes on the packed word.
  let mut wordCommands : Array Command := #[]
  wordCommands := wordCommands.push <| ← `(
    @[inline] unsafe def $wordName ($valueIdent : $sourceTy) : $carrier:ident :=
      $(mkCIdent ``unsafeCast) $valueIdent
    @[inline] unsafe def $ofWordName ($rawIdent : $carrier:ident) : $sourceTy :=
      $(mkCIdent ``unsafeCast) $rawIdent
    @[inline] def $packName ($reprIdent : $reprTy) : $carrier:ident :=
      $(← packBody pk slots reprIdent)
    @[inline] unsafe def $unpackName ($rawIdent : $carrier:ident) : $reprTy :=
      $(← unpackBody pk slots rawIdent)
    @[inline] unsafe def $(names.rel `toReprImpl) ($valueIdent : $sourceTy) : $reprTy :=
      $unpackName ($wordName $valueIdent)
    @[inline] unsafe def $(names.rel `fromReprImpl) ($reprIdent : $reprTy) : $sourceTy :=
      $ofWordName ($packName $reprIdent)
    @[inline, instance_reducible] unsafe def $(names.rel `dataReprImpl) :
        $(mkCIdent ``DataRepr) $sourceTy ($reprTy) where
      toRepr := $(names.rel `toReprImpl)
      fromRepr := $(names.rel `fromReprImpl)
      from_to := $(mkCIdent ``lcProof)
  )

  let unsafeCtx := { ctx with unsafeProof := true }
  let mut ctorImpls := #[]
  let mut tests := #[]
  let mut fieldNames := #[]
  let mut order := #[]
  let mut unguarded? := none
  for cidx in [0:indInfo.ctors.length] do
    let ctorName := indInfo.ctors[cidx]!
    let short := (privateToUserName ctorName).replacePrefix (privateToUserName typeName) .anonymous
    let some arm := arms.find? (·.ctorName == ctorName)
      | logErrorAt ref m!"internal error: no representation for `{.ofConstName ctorName}`"
        return none
    let ctorImpl := names.rel (ctorSuffix "ctor" short)
    ctorImpls := ctorImpls.push (names.full (ctorSuffix "ctor" short))
    let binders ← arm.fields.mapM fun field =>
      `(bracketedBinderF| ($(field.name) : $(field.ty)))
    let armTerm : ElabRepr.M Term := do ElabRepr.buildReprTerm (← ElabRepr.armWrites arm)
    let reprExpr ← armTerm.run unsafeCtx
    wordCommands := wordCommands.push <| ← `(
      @[inline] unsafe def $ctorImpl $binders* : $sourceTy :=
        $ofWordName ($packName $reprExpr)
    )
    match arm.guard? with
    | .some g =>
      let testName := names.rel (ctorSuffix "test" short)
      tests := tests.push (some (names.full (ctorSuffix "test" short)))
      order := order.push cidx
      wordCommands := wordCommands.push <| ← `(
        @[inline] def $testName ($rawIdent : $carrier:ident) : Bool :=
          $(← bindSlots pk slots rawIdent (← `(decide $(g.cond))))
      )
    | .none =>
      tests := tests.push none
      unguarded? := some cidx
    let mut perField := #[]
    for field in arm.fields do
      let suffix := fieldSuffix short field.name.getId
      let fieldName := names.rel suffix
      perField := perField.push (names.full suffix)
      let decoded ← (ElabRepr.mkDecodeTerm field.val).run unsafeCtx
      wordCommands := wordCommands.push <| ← `(
        @[inline] unsafe def $fieldName ($rawIdent : $carrier:ident) : $(field.ty) :=
          $(← bindSlots pk slots rawIdent decoded)
      )
    fieldNames := fieldNames.push perField

  -- Every check has passed.  From here on the type is classified as a boxed scalar, so nothing
  -- that mentions it may be compiled against the object layout again; a failure below is an
  -- internal error, and the module must not go on as if the clause had merely been rejected.
  if retag then
    liftCoreM <| Transmog.Runtime.retagAsTagged typeName
  for cmd in wordCommands do
    trace[Transmog.replaceRuntime] cmd
    unless (← ElabRepr.elabCommandOk cmd) do
      if retag then
        throwErrorAt ref m!"internal error: a helper of the runtime representation of \
          `{.ofConstName typeName}` failed to elaborate after its IR classification was overridden"
      return none

  let info : ReprInfo := {
    carrier := pk.carrier
    ctors := indInfo.ctors.toArray
    word := names.full `word
    ctorImpls
    tests
    fields := fieldNames
    order
    unguarded?
    forbidden := staleAux
      |>.push (typeName ++ `rec)
      |>.push (← ctx.constName `toRepr)
      |>.push (← ctx.constName `fromRepr)
  }
  liftCoreM <| registerReprInfo typeName info

  -- Batch two: the declarations that eliminate on the type, now that the pass will rewrite them.
  let ctorIdxName := typeName ++ `ctorIdx
  if env.contains ctorIdxName then
    let ctorIdxImpl := names.rel `ctorIdxImpl
    let alts ← indInfo.ctors.toArray.mapIdxM fun cidx ctorName => do
      let ctorInfo ← getConstInfoCtor ctorName
      let holes ← (Array.range ctorInfo.numFields).mapM fun _ => `(_)
      let pat := Syntax.mkApp (mkCIdent ctorName) holes
      let lit : TSyntax `num := ⟨Syntax.mkNatLit cidx⟩
      `(matchAltExpr| | $pat:term => $lit:num)
    let cmd ← `(
      def $ctorIdxImpl : $sourceTy → Nat
        $[$alts:matchAlt]*
      @[csimp] theorem $(names.rel `ctorIdx_eq) :
          @$(mkCIdent ctorIdxName) = @$ctorIdxImpl := by
        funext x
        cases x <;> rfl
    )
    trace[Transmog.replaceRuntime] cmd
    elabCommand cmd
  for src in [`rec, `recOn] do
    let srcName := typeName ++ src
    if env.contains srcName then
      mkEliminatorImpl typeName srcName (names.full (.mkSimple s!"{src}Impl"))
        (names.full (.mkSimple s!"{src}_eq"))

  return some {
    toReprImpl := names.rel `toReprImpl
    fromReprImpl := names.rel `fromReprImpl
    dataReprImpl := names.rel `dataReprImpl
  }

initialize registerTraceClass `Transmog.replaceRuntime

end Transmog.DSL.ReplaceRuntime

end -- meta section
