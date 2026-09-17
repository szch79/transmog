/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Init.Data.Iterators.Consumers
public import Init.Data.Iterators.ToIterator
public import Transmog.Data.CompactArray.Basic

/-! # Finite iterators over compact arrays -/

@[expose] public section

open Std Std.Iterators

namespace Transmog.CompactArray

variable {α : Type u} {ρ : Type v} {k : Nat} [DataRepr α ρ] [HasLayout α ρ k]

namespace Internal

/-- The state of a compact-array iterator. -/
structure IterState (α : Type u) {ρ : Type v} {k : Nat} [DataRepr α ρ] [HasLayout α ρ k] : Type u where
  array : CompactArray α
  pos : Nat

@[inline]
instance : Std.Iterator (IterState α) Id α where
  IsPlausibleStep it
    | .yield it' out => it.internalState.array = it'.internalState.array ∧
      it'.internalState.pos = it.internalState.pos + 1 ∧
      ∃ h : it.internalState.pos < it.internalState.array.size,
        it.internalState.array[it.internalState.pos]'h = out
    | .skip _ => False
    | .done => it.internalState.pos ≥ it.internalState.array.size
  step it := pure <| .deflate <| if h : it.internalState.pos < it.internalState.array.size then
      .yield ⟨⟨it.internalState.array, it.internalState.pos + 1⟩⟩
        it.internalState.array[it.internalState.pos] ⟨rfl, rfl, h, rfl⟩
    else .done (Nat.not_lt.mp h)

private def finitenessRelation : FinitenessRelation (IterState α) Id where
  Rel := InvImage WellFoundedRelation.rel
    (fun it => it.internalState.array.size - it.internalState.pos)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, hp⟩ := h
    cases step
    · cases h
      obtain ⟨ha, hi, hb, rfl⟩ := hp
      rw [ha] at hb
      simp only [ha, hi]
      omega
    · cases hp
    · cases h

instance : Finite (IterState α) Id := .of_finitenessRelation finitenessRelation

@[inline] instance [Monad m] : IteratorLoop (IterState α) Id m := .defaultImplementation

end Internal

/-- Returns a finite iterator starting at the specified element index. -/
@[inline] def iterFromIdx (xs : CompactArray α) (start : Nat) :
    Iter (α := Internal.IterState α) α :=
  (⟨⟨xs, start⟩⟩ : IterM (α := Internal.IterState α) Id α).toIter

/-- Returns a finite iterator over the elements in increasing index order. -/
@[inline] def iter (xs : CompactArray α) : Iter (α := Internal.IterState α) α :=
  xs.iterFromIdx 0

@[inline, instance_reducible]
instance : ToIterator (CompactArray α) Id (Internal.IterState α) α :=
  ToIterator.of _ (fun xs => xs.iter)

end Transmog.CompactArray
