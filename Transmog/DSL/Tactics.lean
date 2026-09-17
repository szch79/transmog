/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean.Elab.Tactic.Basic
public meta import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect
public meta import Transmog.DSL.Core.Cast
public meta import Transmog.DSL.Core.UInt
-- The reflected expression `bv_decide` compiles is an ordinary definition, so its constructors
-- are needed outside meta code as well.
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic

/-!
# Transmog Proof Automation

Two automation entry points discharge the obligations involved in `DataRepr`:
- `transmog_subtype` closes the side condition emitted for subtypes carrying the guard
conditions and other invariants (e.g., `fitsBits`);
- `transmog_from_to_case` closes one constructor case of the round-trip law
`fromRepr (toRepr x) = x`; `transmog_from_to` is the whole-theorem form for
declarations without subtype-typed payloads.

## The local-lemma principle

Neither tactic recovers information from the goal.  Universal facts (the
generic slice lemmas, class round-trip laws, `Subtype.eta`) live in the
`transmog_norm` custom simp set, and the ones whose side condition is a fit
are keyed for `grind` as well, together with the arithmetic reading
`fitsBits w x ↔ x.toNat < 2 ^ w`, so that a fit which is only an arithmetic
consequence of the hypotheses still closes.  Per-declaration facts (subtype
properties of payload binders, and the carrier property `(toRepr f).property`
of a field placed through its representation) are injected by codegen as
`have h := f.property` hypotheses in the generated proof, where `simp_all`
splits and keys their conjuncts and `grind` reads them from the context.

## The finisher ladder

`transmog_from_to_case` is two rungs plus a diagnostic:
1.  `simp_all +decide [transmog_norm, ...]` ; the alignment contract: for a
   layout whose guard conjuncts are stated in the same form as the subtype
   properties, this closes with no search.
2.  `grind` ; moral-match tolerance: bridges predicate synonyms
   (`0 < a` vs `a ≠ 0`), conjunct regrouping, and linear-arithmetic
   consequences, consuming the property hypotheses from the local context.
   Only runs when rung 1 leaves residue.
-/

public meta section

namespace Transmog

open Lean Parser Elab Tactic Meta

/-!
## Subtyping proofs

Transmog uses subtyping for type-safe conversion.  The subtyping obligations are expected to
be bit range constraints and enum guard conditions.
-/

/--
The extensible finisher ladder behind `transmog_subtype`, mirroring core's
`get_elem_tactic_extensible`: the entry points below are fixed, and this is the extension
point - add a `macro_rules` alternative to teach the automation a new obligation shape.
Deliberately global (not `scoped`): it is expanded inside proofs that `derive_layout` emits
into user modules, where no Transmog namespace is open.
-/
syntax "transmog_subtype_trivial" : tactic

-- NOTE: tactic ladder is LIFO, thus declaring expensive ones first.
macro_rules
  | `(tactic| transmog_subtype_trivial) =>
    `(tactic| (simp [transmog_subtype_simps] <;> bv_decide))
macro_rules
  | `(tactic| transmog_subtype_trivial) =>
    `(tactic| (simp only [transmog_subtype_simps] at * <;> bv_decide))
macro_rules
  | `(tactic| transmog_subtype_trivial) => `(tactic| bv_decide)
-- Range arithmetic: `fitsBits` reads as `toNat < 2 ^ w` for `grind`, so a bound that follows
-- from the slot constraints and the guards closes here, before any SAT call.
macro_rules
  | `(tactic| transmog_subtype_trivial) => `(tactic| grind)
-- Keyed fast path: `fitsBits` obligations close via the generic slice lemmas
-- (`fitsBits_extractSlice`, `fitsBits_val`, ...) without unfolding or SAT.
macro_rules
  | `(tactic| transmog_subtype_trivial) =>
    `(tactic| (simp_all +decide [transmog_norm]; done))
macro_rules
  | `(tactic| transmog_subtype_trivial) => `(tactic| assumption)
macro_rules
  | `(tactic| transmog_subtype_trivial) => `(tactic| rfl)

/--
Close a `DataRepr` subtype obligation, trying `ts` before the default
`transmog_subtype_trivial` ladder.
-/
macro "transmog_subtype_with " ts:tacticSeq : tactic =>
  `(tactic|
    first
    | done
    | $ts
    | constructor <;> transmog_subtype_trivial
    | fail "failed to prove Transmog `DataRepr` subtype obligation")

/--
Close a `DataRepr` subtype obligation (bit-range constraints and enum guards); the entry
point used by generated code and `correct_by` proofs.  Extend via `transmog_subtype_trivial`.
-/
macro "transmog_subtype" : tactic =>
  `(tactic| transmog_subtype_with first | transmog_subtype_trivial)

/-! ## Round-trip proofs -/

/--
Close one constructor case of the round-trip law `fromRepr (toRepr x) = x` (internal:
invoked by the proofs `derive_layout` emits, after codegen injects the per-field
`have := f.property` hypotheses).
-/
syntax "transmog_from_to_case" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| transmog_from_to_case [$args,*]) =>
    `(tactic|
      (try simp_all +decide [transmog_norm, $args,*]) <;>
      first
      | done
      | grind
      | fail "failed to prove Transmog `DataRepr` round-trip obligation: \
          goal constituents did not align; restate guard conjuncts in the \
          same form as the field subtype properties, or provide `correct_by`")

/--
Close the whole round-trip law `∀ x, fromRepr (toRepr x) = x` for declarations without
subtype-typed payloads; also usable from `correct_by`.
-/
syntax "transmog_from_to" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| transmog_from_to [$args,*]) =>
    `(tactic| (intro x; try cases x) <;> transmog_from_to_case [$args,*])

end Transmog

end -- public meta section
