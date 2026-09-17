/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean.Compiler.LCNF.Passes
public meta import Transmog.DSL.Runtime.Basic

/-!
# Code generator passes for word-backed runtime representations

Two passes implement the representation change.  The lowering pass runs immediately after `init`,
while every elimination is still a uniform `cases` node tagged with its inductive type, every
structure projection still names its structure, and every construction is still a saturated
application of a constructor.  Rewriting there is independent of which eliminator the frontend
happened to produce, so plain `casesOn`, sparse `casesOn`s, the per-constructor eliminators,
inlined matchers and projection functions are all covered at once.

The verification pass runs at the last point of the mono phase open to installed passes, after
lambda lifting.  By then every structure projection has been turned into a `cases` that names its
type, and the passes that remain before the lowering to the impure phase inline nothing that the
earlier ones would not have, so the constructions and eliminations still present are the ones
that will be emitted.  Anything left that touches the native layout of a registered type becomes
a compile error in the module that contains it, rather than memory corruption at run time.  A
second check at the end of the impure phase backs this up for the forms that are still
recognisable there, namely constructor allocations, alternatives on a constructor, and calls to
declarations compiled against the object layout.
-/

public meta section

namespace Transmog.Runtime

open Lean Compiler LCNF

/-! ## Lowering -/

namespace Lower

/-- The registry is read once per declaration. -/
structure Context where
  reg : Registry

/-- The state flag records whether the declaration was rewritten at all. -/
abbrev M := ReaderT Context (StateRefT Bool CompilerM)

/--
Rebind a constructor alternative's fields as extractions from the packed word.  The parameters
keep their free variables, so the alternative's body needs no substitution.
-/
def bindFields (info : ReprInfo) (cidx : Nat) (raw : FVarId) (params : Array (Param .pure))
    (code : Code .pure) : CompilerM (Code .pure) := do
  eraseParams params
  let extractors := info.fields[cidx]!
  let mut decls := #[]
  for h : i in [0:params.size] do
    let param := params[i]
    let value : LetValue .pure :=
      if param.type.isErased || i ≥ extractors.size then
        .erased
      else
        .const extractors[i]! [] #[.fvar raw]
    let decl : LetDecl .pure :=
      { fvarId := param.fvarId, binderName := param.binderName, type := param.type, value }
    modifyLCtx fun lctx => lctx.addLetDecl decl
    decls := decls.push decl
  return decls.foldr (init := code) fun decl acc => .let decl acc

/--
Replace a `cases` on a word-backed type by a first-match chain of guard tests on the packed word.
`alts` are the already-visited alternatives of `c`.
-/
def lowerCases (info : ReprInfo) (c : Cases .pure) (alts : Array (Alt .pure)) :
    CompilerM (Code .pure) := do
  let mut default? : Option (Code .pure) := none
  let mut explicit : NameMap (Alt .pure) := {}
  for alt in alts do
    match alt with
    | .default code => default? := some code
    | .alt ctorName .. => explicit := explicit.insert ctorName alt
    | .ctorAlt .. => return .cases (c.updateAlts alts)
  if explicit.isEmpty then
    -- A `cases` whose only alternative is the catch-all does not inspect the value at all.
    return default?.getD (.unreach c.resultType)
  let rawDecl ← mkLetDecl `raw (mkConst info.carrier) (.const info.word [] #[.fvar c.discr])
  let jp? ← default?.mapM fun code => do mkFunDecl (← mkFreshJpName) c.resultType #[] code
  let fallback : Code .pure :=
    match jp? with
    | some jp => .jmp jp.fvarId #[]
    | none => .unreach c.resultType
  let armBody (cidx : Nat) : CompilerM (Option (Code .pure)) := do
    let some ctorName := info.ctors[cidx]? | return none
    let some (.alt _ params code _) := explicit.find? ctorName | return none
    return some (← bindFields info cidx rawDecl.fvarId params code)
  let mut els := fallback
  let mut elsIsFallback := true
  if let some cidx := info.unguarded? then
    if let some body ← armBody cidx then
      els := body
      elsIsFallback := false
  for cidx in info.order.reverse do
    let body? ← armBody cidx
    if body?.isNone && elsIsFallback then
      continue
    let some (some test) := info.tests[cidx]? | continue
    let testDecl ← mkLetDecl `isCtor (mkConst ``Bool) (.const test [] #[.fvar rawDecl.fvarId])
    let alts := #[Alt.alt ``Bool.true #[] (body?.getD fallback), Alt.alt ``Bool.false #[] els]
    els := .let testDecl (.cases ⟨``Bool, c.resultType, testDecl.fvarId, alts⟩)
    elsIsFallback := false
  match jp? with
  | some jp => return .let rawDecl (.jp jp els)
  | none => return .let rawDecl els

/--
Replace a projection out of a word-backed structure by an extraction from the packed word.  A
structure has one constructor, so its extractors are the first entry of `fields`, and the
projection index counts the same fields they do.
-/
def lowerProj (info : ReprInfo) (idx : Nat) (struct : FVarId) (decl : LetDecl .pure)
    (k : Code .pure) : CompilerM (Code .pure) := do
  let extractors := info.fields[0]!
  if decl.type.isErased || idx ≥ extractors.size then
    return .let (← decl.updateValue .erased) k
  let rawDecl ← mkLetDecl `raw (mkConst info.carrier) (.const info.word [] #[.fvar struct])
  let decl ← decl.updateValue (.const extractors[idx]! [] #[.fvar rawDecl.fvarId])
  return .let rawDecl (.let decl k)

mutual

partial def visitCode (code : Code .pure) : M (Code .pure) := do
  match code with
  | .let decl k =>
    let k ← visitCode k
    match decl.value with
    | .const declName _ args =>
      if let some (typeName, cidx) := (← read).reg.ctors.find? declName then
        let some info := (← read).reg.types.find? typeName | unreachable!
        set true
        let decl ← decl.updateValue (.const info.ctorImpls[cidx]! [] args)
        return .let decl k
    | .proj typeName idx struct =>
      if let some info := (← read).reg.types.find? typeName then
        set true
        return ← lowerProj info idx struct decl k
    | _ => pure ()
    return code.updateLet! decl k
  | .fun decl k | .jp decl k =>
    let decl ← decl.updateValue (← visitCode decl.value)
    return code.updateFun! decl (← visitCode k)
  | .cases c =>
    let alts ← c.alts.mapM visitAlt
    match (← read).reg.types.find? c.typeName with
    | some info =>
      set true
      lowerCases info c alts
    | none => return code.updateAlts! alts
  | .jmp .. | .return .. | .unreach .. => return code

partial def visitAlt (alt : Alt .pure) : M (Alt .pure) := do
  return alt.updateCode (← visitCode alt.getCode)

end

/-- Lower every construction and elimination of a word-backed type in `decl`. -/
def visitDecl (decl : Decl .pure) : CompilerM (Decl .pure) := do
  let reg := getRegistry (← getEnv)
  if reg.isEmpty then return decl
  let (value, changed) ← (decl.value.mapCodeM (visitCode · |>.run { reg })).run false
  unless changed do return decl
  let decl := { decl with value }
  -- `init` snapshotted the pre-rewrite body for cross-declaration inlining; refresh it.
  decl.saveBase
  return decl

end Lower

/-! ## Verification -/

namespace Verify

/-- Report a construction or elimination that still uses the native layout of a word-backed type. -/
def fail (declName typeName : Name) (what : MessageData) : CoreM Unit :=
  throwError m!"`{.ofConstName declName}` still {what} through the object layout of \
    `{.ofConstName typeName}`, whose runtime representation was replaced.\n\n\
    This usually means the code was compiled before the `replace_runtime` clause ran, and was \
    then inlined here.  Move every definition that mentions `{.ofConstName typeName}` after the \
    clause."

/--
Check one mono declaration against the registry.  A `cases` still names its type here, a
construction or a call is still an application of a named constant, and a projection, should one
have survived `structProjCases`, still names its structure.
-/
def checkMonoDecl (reg : Registry) (decl : Decl .pure) : CoreM Unit :=
  decl.value.forCodeM fun code => code.forM fun c => do
    match c with
    | .cases cs =>
      if reg.types.contains cs.typeName then
        fail decl.name cs.typeName "eliminates"
    | .let d _ =>
      match d.value with
      | .const declName .. =>
        if let some (typeName, _) := reg.ctors.find? declName then
          fail decl.name typeName "allocates"
        if let some typeName := reg.forbidden.find? declName then
          fail decl.name typeName m!"calls `{.ofConstName declName}`, which operates"
      | .proj typeName .. =>
        if reg.types.contains typeName then
          fail decl.name typeName "projects"
      | _ => return ()
    | _ => return ()

/--
Check one impure declaration against the registry.  Lowering to the impure phase replaces a
`cases`' type name by its IR type and turns a single-alternative `cases` into bare field reads,
so only the constructors named in the remaining alternatives and allocations identify the
inductive here.
-/
def checkImpureDecl (reg : Registry) (decl : Decl .impure) : CoreM Unit :=
  decl.value.forCodeM fun code => code.forM fun c => do
    match c with
    | .cases cs =>
      for alt in cs.alts do
        if let .ctorAlt info _ := alt then
          if let some (typeName, _) := reg.ctors.find? info.name then
            fail decl.name typeName "eliminates"
    | .let d _ =>
      match d.value with
      | .ctor info _ | .reuse _ info _ _ =>
        if let some (typeName, _) := reg.ctors.find? info.name then
          fail decl.name typeName "allocates"
      | .fap fn _ | .pap fn _ =>
        if let some typeName := reg.forbidden.find? fn then
          fail decl.name typeName m!"calls `{fn}`, which operates"
      | _ => return ()
    | _ => return ()

end Verify

/-! ## Passes -/

/-- Rewrites word-backed constructions and eliminations into packed-word arithmetic. -/
def lowerRuntimeRepr : Pass :=
  .mkPerDeclaration `Transmog.lowerRuntimeRepr .base Lower.visitDecl

/-- Rejects code that would construct or inspect a word-backed value through the object layout. -/
def verifyRuntimeRepr : Pass where
  phase := .mono
  name := `Transmog.verifyRuntimeRepr
  run decls := do
    let reg := getRegistry (← getEnv)
    unless reg.isEmpty do
      decls.forM fun decl => Verify.checkMonoDecl reg decl
    return decls

/-- The backstop of `verifyRuntimeRepr` for the forms the impure phase still names. -/
def verifyRuntimeReprImpure : Pass where
  phase := .impure
  name := `Transmog.verifyRuntimeReprImpure
  run decls := do
    let reg := getRegistry (← getEnv)
    unless reg.isEmpty do
      decls.forM fun decl => Verify.checkImpureDecl reg decl
    return decls

@[cpass] def installLowerRuntimeRepr : PassInstaller :=
  .installAfter .base `init fun _ => lowerRuntimeRepr

@[cpass] def installVerifyRuntimeRepr : PassInstaller :=
  .installAtEnd .mono verifyRuntimeRepr

@[cpass] def installVerifyRuntimeReprImpure : PassInstaller :=
  .installAtEnd .impure verifyRuntimeReprImpure

initialize
  registerTraceClass `Compiler.Transmog.lowerRuntimeRepr (inherited := true)
  registerTraceClass `Compiler.Transmog.verifyRuntimeRepr (inherited := true)
  registerTraceClass `Compiler.Transmog.verifyRuntimeReprImpure (inherited := true)

end Transmog.Runtime

end -- public meta section
