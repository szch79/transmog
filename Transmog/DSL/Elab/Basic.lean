/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean.Elab.Command
public meta import Transmog.DSL.Elab.DeriveLayout
public meta import Transmog.DSL.Elab.ElabRepr
public meta import Transmog.DSL.Elab.ReplaceRuntime
public meta import Transmog.DSL.Elab.ToIR

/-! # Transmog DSL elaboration -/

public meta section

namespace Transmog.DSL

open Lean Elab Command

elab_rules : command
  | `(command| transmog $[$tys]* as $spec:transmogReprSpec
        $[where $body?:transmogReprBody]? $[$suffixes?:transmogSuffixes]?) => do
  let ty := Syntax.mkApp tys[0]! (tys.extract 1 tys.size)
  -- The source type is resolved in the default view, in which a private type is visible, and
  -- the generated declarations follow its visibility, as the deriving handlers do.
  let sourceExpr ← liftTermElabM <| ToIR.elabSourceType ty
  let isPrivateSource := (sourceExpr.find? fun e => e.isConst && isPrivateName e.constName!).isSome
  withScope (fun sc => { sc with isPublic := sc.isPublic && !isPrivateSource }) do
  -- As `elabDeclaration` does, so that the user's types are elaborated in the view the generated
  -- declarations are elaborated in, and the visibility rule has a single owner.
  withExporting (isExporting := (← getScope).isPublic) do
  let ir ← ToIR.toIR ty sourceExpr spec body?

  let mut deriveLayoutSpecs? :
    Option (Syntax × Array (TSyntax ``transmogLayoutSpec)) := none
  let mut correctByTacs? : Option (TSyntax ``Parser.Tactic.tacticSeq) := none
  let mut replaceRuntime? : Option (Syntax × Option Ident) := none
  if let .some suffixes := suffixes? then
    let `(transmogSuffixes|
          $[$rr?:transmogReplaceRuntime]?
          $[$dl?:transmogDeriveLayout]?
          $[$cb?:transmogCorrectBy]?) := suffixes
      | throwErrorAt suffixes "invalid Transmog clauses"
    if let .some rr := rr? then
      let `(transmogReplaceRuntime| replace_runtime $[as $carrier?:ident]?) := rr
        | throwErrorAt rr "invalid `replace_runtime` clause"
      replaceRuntime? := some (rr, carrier?)
    if let .some dl := dl? then
      let `(transmogDeriveLayout| derive_layout $specs:transmogLayoutSpec,*) := dl
        | throwErrorAt dl "invalid `derive_layout` clause"
      deriveLayoutSpecs? := some (dl, specs.getElems)
    if let .some cb := cb? then
      let `(transmogCorrectBy| correct_by $tacs) := cb
        | throwErrorAt cb "invalid `correct_by` clause"
      correctByTacs? := some tacs

  let runtime (ctx : ElabRepr.Context) : CommandElabM (Option ElabRepr.RuntimeHooks) := do
    let .some (ref, carrier?) := replaceRuntime? | return none
    ReplaceRuntime.generate ctx ref carrier?
  let (ctx, ok) ← ElabRepr.elabRepr ir (correctBy? := correctByTacs?) (runtime := runtime)
  if let .some (ref, specs) := deriveLayoutSpecs? then
    -- A layout over a broken repr only adds noise to the targeted error.
    if ok then
      DeriveLayout.elabDeriveLayout ctx ref specs

end Transmog.DSL

end -- public meta section
