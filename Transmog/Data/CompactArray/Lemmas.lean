/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.Data.CompactArray.Basic
import Init.Data.ByteArray.Lemmas
import Init.Data.List.OfFn
import Transmog.DSL.Core.Lemmas
import Transmog.Data.ByteArray.Lemmas

/-!
# `CompactArray` lemmas

The collection laws follow from the layout's serialization and locality laws.  Canonical
slot encodings make equality extensional in the decoded elements.
-/

public section

namespace Transmog

set_option linter.listVariables true
set_option linter.indexVariables true


namespace CompactArray

variable {α : Type u} {ρ : Type v} {align : Nat} [DataRepr α ρ] [HasLayout α ρ align]

/-! ## Empty / capacity -/

-- At present the preferred normal form for empty compact arrays is `CompactArray.empty`.
@[simp]
theorem emptyc_eq_empty :
    (∅ : CompactArray α) = CompactArray.empty := rfl

@[simp]
theorem emptyWithCapacity_eq_empty (c : Nat) :
    (CompactArray.emptyWithCapacity c : CompactArray α) =
      CompactArray.empty := rfl

@[simp]
theorem data_empty :
    (CompactArray.empty (α := α)).data = ByteArray.empty := rfl

@[simp]
theorem size_empty :
    (CompactArray.empty (α := α)).size = 0 := rfl

@[simp]
theorem size_eq_zero_iff {xs : CompactArray α} :
    xs.size = 0 ↔ xs = CompactArray.empty := by
  refine ⟨fun h => ?_, fun h => h ▸ CompactArray.size_empty⟩
  apply CompactArray.ext
  · -- xs.data = empty.data; size_data + size=0 forces data.size = 0.
    have hs : xs.data.size = 0 := by
      rw [xs.size_data, h, Nat.zero_mul]
    have : xs.data = ByteArray.empty := by
      rwa [← ByteArray.size_eq_zero_iff]
    rw [this, data_empty]
  · rw [h, size_empty]

/-! ## Size lemmas: push / set / set! / uset / append / extract -/

@[simp, grind =]
theorem size_push {xs : CompactArray α} :
    (xs.push x).size = xs.size + 1 := rfl

@[simp, grind =]
theorem size_set {xs : CompactArray α}
    {h : i < xs.size} :
    (xs.set i x h).size = xs.size := rfl

@[simp, grind =]
theorem size_set! {xs : CompactArray α} {i : Nat} :
    (xs.set! i x).size = xs.size := by
  unfold CompactArray.set!
  split <;> rfl

@[simp, grind =]
theorem size_uset {xs : CompactArray α}
    {h : i.toNat < xs.size} :
    (xs.uset i x h).size = xs.size := rfl

@[simp, grind =]
theorem size_append {xs ys : CompactArray α} :
    (xs ++ ys).size = xs.size + ys.size := rfl

@[simp]
theorem size_extract {xs : CompactArray α} :
    (xs.extract b e).size = min e xs.size - b := rfl

/-! ## `data` lemmas -/

@[simp]
theorem data_append {xs ys : CompactArray α} :
    (xs ++ ys).data = xs.data ++ ys.data := rfl

/-! ## `List.toCompactArray` -/

@[simp]
theorem _root_.List.toCompactArray_nil :
    ([] : List α).toCompactArray = CompactArray.empty := rfl

private theorem size_toCompactArray_loop (xs : List α) (acc : CompactArray α) :
    (List.toCompactArray.loop xs acc).size = acc.size + xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [List.toCompactArray.loop, ih, Nat.add_comm, Nat.add_left_comm]

@[simp]
theorem _root_.List.size_toCompactArray {xs : List α} : xs.toCompactArray.size = xs.length := by
  simp [List.toCompactArray, size_toCompactArray_loop]

/-! ## `extract` -/

@[simp]
theorem extract_zero_size {xs : CompactArray α} :
    xs.extract 0 xs.size = xs := by
  apply CompactArray.ext
  · show xs.data.extract _ _ = xs.data
    rw [Nat.zero_mul]
    have : xs.size *
        (HasLayout.layout (α := α)).size = xs.data.size := xs.size_data.symm
    rw [this]; simp
  · show min xs.size xs.size - 0 = xs.size
    simp

@[simp]
theorem extract_same {xs : CompactArray α} :
    xs.extract i i = CompactArray.empty := by
  apply CompactArray.ext
  · let L : Layout ρ align := HasLayout.layout (α := α)
    show xs.data.extract (i * L.size) (i * L.size) = ByteArray.empty
    rw [← ByteArray.size_eq_zero_iff, ByteArray.size_extract]
    omega
  · show min i xs.size - i = 0
    omega

/-! ## Append lemmas -/

@[simp]
theorem empty_append {xs : CompactArray α} :
    CompactArray.empty ++ xs = xs := by
  apply CompactArray.ext
  · show ByteArray.empty ++ xs.data = xs.data
    simp
  · show 0 + xs.size = xs.size
    omega

@[simp]
theorem append_empty {xs : CompactArray α} :
    xs ++ CompactArray.empty = xs := by
  apply CompactArray.ext
  · show xs.data ++ ByteArray.empty = xs.data
    simp
  · show xs.size + 0 = xs.size
    omega

@[simp]
theorem append_eq_empty_iff {xs ys : CompactArray α} :
    xs ++ ys = CompactArray.empty ↔ xs = CompactArray.empty ∧ ys = CompactArray.empty := by
  simp [← size_eq_zero_iff]

/-! ## `getElem` bridges -/

@[simp] theorem get_eq_getElem {xs : CompactArray α}
    (h : i < xs.size) : xs.get i h = xs[i] := rfl

@[simp] theorem get!_eq_getElem [Inhabited α] {xs : CompactArray α}
     (h : i < xs.size) : xs.get! i = xs[i] := by
  change xs.get! i = xs.get i h
  simp only [CompactArray.get!, get, dite_eq_left h]

/-!
## `USize` bridges

For verification purposes, `simp` replaces the `USize` operations with their `Nat`
counterparts, mirroring `Array.uset_eq_set`/`Array.ugetElem_eq_getElem`; all reasoning then
happens in the `Nat` lemma base.
-/

@[simp, grind =]
theorem uget_eq_get {xs : CompactArray α}
    (h : i.toNat < xs.size) : xs.uget i h = xs.get i.toNat h := rfl

@[simp, grind =]
theorem uset_eq_set {xs : CompactArray α}
    (h : i.toNat < xs.size) : xs.uset i x h = xs.set i.toNat x h := rfl

@[simp]
theorem ugetElem_eq_getElem {xs : CompactArray α} {i : USize}
    (h : i.toNat < xs.size) : xs[i] = xs[i.toNat] := rfl

/--
The byte-level form: `xs[i]` equals `DataRepr.fromRepr` applied to the codec read of the
`i`-th slot of the underlying byte buffer.
-/
theorem getElem_eq_fromRepr_load
    {xs : CompactArray α} (h : i < xs.size) :
    xs[i] = DataRepr.fromRepr
      ((HasLayout.layout (α := α)).load xs.data
        (i * (HasLayout.layout (α := α)).size)
        (xs.slot_le_size h)) := rfl

/-! ## Element access after updates -/

/--
Reading back the slot just written returns the written element.  This is the principal
codec law for `CompactArray`.
-/
@[simp]
theorem getElem_set_self {xs : CompactArray α}
    (h : i < xs.size) :
    (xs.set i x h)[i]'(by simpa using h) = x := by
  simp only [getElem_eq_fromRepr_load, set, Layout.fromRepr_load_store_toRepr]

/-- Reading back a slot other than the one just written returns the unchanged value. -/
@[simp]
theorem getElem_set_ne {xs : CompactArray α}
    (hi : i < xs.size) (hj : j < xs.size) (hij : i ≠ j) :
    (xs.set i x hi)[j]'(by simpa using hj) = xs[j] := by
  have hd := slot_disjoint_of_ne (α := α) hij
  simp only [getElem_eq_fromRepr_load, set]
  simp only [(HasLayout.layout (α := α)).load_store_disjoint hd]

@[grind =]
theorem getElem_set {xs : CompactArray α}
    (hi : i < xs.size)   (hj : j < (xs.set i x hi).size) :
    (xs.set i x hi)[j] = if i = j then x else xs[j]'(by simpa using hj) := by
  have hj' : j < xs.size := by simpa using hj
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    exact getElem_set_self hi
  · rw [ite_eq_right hij]
    exact getElem_set_ne hi hj' hij

/-- Reading back the last slot of a `push` returns the just-pushed element. -/
@[simp]
theorem getElem_push_eq {xs : CompactArray α} :
    (xs.push x)[xs.size]'(by simp) = x := by
  simp only [getElem_eq_fromRepr_load, push, Layout.fromRepr_load_store_toRepr]

/--
Reading back a slot other than the last after `push` returns the unchanged value.
Uses the locality law (`load_eq_of_extract_eq`) to peel off the buffer extension.
-/
theorem getElem_push_lt {xs : CompactArray α} {i : Nat}
    (h : i < xs.size) :
    (xs.push x)[i]'(by rw [size_push]; omega) = xs[i] := by
  let L := HasLayout.layout (α := α)
  have hd : xs.size * L.size + L.size ≤ i * L.size ∨
      i * L.size + L.size ≤ xs.size * L.size := by
    right
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right L.size h
  simp only [getElem_eq_fromRepr_load, push]
  rw [(HasLayout.layout (α := α)).load_store_disjoint hd]
  simp only [L, Layout.load_eq_extract, ByteArray.extract_append_of_le (xs.slot_le_size h)]

@[grind =]
theorem getElem_push {xs : CompactArray α}
    (h : i < (xs.push x).size) :
    (xs.push x)[i] = if h' : i < xs.size then xs[i] else x := by
  by_cases h' : i < xs.size
  · rw [dite_eq_left h']
    exact getElem_push_lt h'
  · rw [dite_eq_right h']
    have hi : i = xs.size := by
      rw [size_push] at h
      omega
    subst hi
    exact getElem_push_eq

/-! ## Canonical encodings and extensionality -/

/-- The byte window of an element is its canonical serialization. -/
theorem extract_eq_toBytes_getElem {xs : CompactArray α} (h : i < xs.size) :
    xs.data.extract (i * (HasLayout.layout (α := α)).size)
        (i * (HasLayout.layout (α := α)).size + (HasLayout.layout (α := α)).size) =
      (HasLayout.layout (α := α)).toBytes (DataRepr.toRepr xs[i]) := by
  obtain ⟨x, hx⟩ := xs.isCanonical i h
  simp only [getElem_eq_fromRepr_load, Layout.load_eq_extract, hx,
    Layout.fromBytes_toBytes, DataRepr.from_to]

/-- Compact arrays are determined by their lengths and decoded elements. -/
@[ext]
theorem ext_getElem {xs ys : CompactArray α} (hs : xs.size = ys.size)
    (h : ∀ (i : Nat) (hi : i < xs.size) (hi' : i < ys.size), xs[i]'hi = ys[i]'hi') : xs = ys := by
  apply CompactArray.ext
  · apply ByteArray.ext_getElem
    · simp [xs.size_data, ys.size_data, hs]
    · intro j hj hj'
      let L := HasLayout.layout (α := α)
      let i := j / L.size
      have hi : i < xs.size :=
        (Nat.div_lt_iff_lt_mul L.size_pos).mpr (by simpa [xs.size_data] using hj)
      have hi' : i < ys.size := by omega
      have he : xs.data.extract (i * L.size) (i * L.size + L.size) =
          ys.data.extract (i * L.size) (i * L.size + L.size) := by
        rw [xs.extract_eq_toBytes_getElem hi, ys.extract_eq_toBytes_getElem hi', h i hi hi']
      have hm : j % L.size < L.size := j.mod_lt L.size_pos
      have hb := xs.slot_le_size hi
      have hb' := ys.slot_le_size hi'
      have he' := (ByteArray.extract_eq_extract_iff_getElem hb hb').mp he (j % L.size) hm
      simpa only [i, L, Nat.div_add_mod'] using he'
  · assumption

instance : LawfulBEq (CompactArray α) where
  rfl := by
    intro xs
    change (xs.data.data == xs.data.data) = true
    simp
  eq_of_beq := by
    intro xs ys h
    change (xs.data.data == ys.data.data) = true at h
    have hd : xs.data = ys.data := ByteArray.ext (eq_of_beq h)
    apply CompactArray.ext hd
    exact Nat.eq_of_mul_eq_mul_right (HasLayout.layout (α := α)).size_pos
      (xs.size_data.symm.trans ((congrArg ByteArray.size hd).trans ys.size_data))

@[simp] theorem set_getElem_self {xs : CompactArray α} (h : i < xs.size) :
    xs.set i xs[i] h = xs := by
  apply ext_getElem (by simp)
  intro j hj hj'
  by_cases hij : i = j
  · subst j
    exact getElem_set_self h
  · exact getElem_set_ne h hj' hij

/-! ## Views and slices -/

@[simp] theorem data_extract {xs : CompactArray α} :
    (xs.extract start stop).data =
      xs.data.extract (start * (HasLayout.layout (α := α)).size)
        (stop * (HasLayout.layout (α := α)).size) := rfl

@[simp, grind =]
theorem getElem_extract {xs : CompactArray α} (h : i < (xs.extract start stop).size) :
    (xs.extract start stop)[i] = xs[start + i]'(by simp only [size_extract] at h; omega) := by
  let L := HasLayout.layout (α := α)
  have hb : start + i + 1 ≤ stop := by simp only [size_extract] at h; omega
  have hm := Nat.mul_le_mul_right L.size hb
  simp only [getElem_eq_fromRepr_load, data_extract, Layout.load_eq_extract,
    ByteArray.extract_extract]
  rw [Nat.min_eq_left (by simpa [L, Nat.add_mul, Nat.add_assoc] using hm)]
  simp [Nat.add_mul, Nat.add_assoc]

@[simp] theorem getElem_append_left {xs ys : CompactArray α} (hi : i < xs.size) :
    (xs ++ ys)[i]'(by simp; omega) = xs[i] := by
  simp only [getElem_eq_fromRepr_load, data_append, Layout.load_eq_extract,
    ByteArray.extract_append_of_le (xs.slot_le_size hi)]

@[simp] theorem getElem_append_right {xs ys : CompactArray α} (hi : xs.size ≤ i)
    (h : i < (xs ++ ys).size) :
    (xs ++ ys)[i] = ys[i - xs.size]'(by simp only [size_append] at h; omega) := by
  let L := HasLayout.layout (α := α)
  have hm := Nat.mul_le_mul_right L.size hi
  have he : i * L.size + L.size - xs.size * L.size =
      (i - xs.size) * L.size + L.size := by
    rw [Nat.sub_mul]
    omega
  simp only [getElem_eq_fromRepr_load, data_append, Layout.load_eq_extract,
    ByteArray.extract_append_of_ge (a := xs.data)
      (start := i * (HasLayout.layout (α := α)).size) (by simpa [L, xs.size_data] using hm), xs.size_data]
  simp only [← Nat.sub_mul, ← he, L]

@[grind =] theorem getElem_append {xs ys : CompactArray α} (h : i < (xs ++ ys).size) :
    (xs ++ ys)[i] = if hi : i < xs.size then xs[i] else
      ys[i - xs.size]'(by simp only [size_append] at h; omega) := by
  split
  · next hi => exact getElem_append_left hi
  · next hi => exact getElem_append_right (by omega) h

@[simp, grind =] theorem size_copySlice {src dest : CompactArray α} :
    (src.copySlice srcOff dest destOff len exact).size =
      max dest.size (min destOff dest.size + min len (src.size - srcOff)) := rfl

@[simp] theorem length_toList {xs : CompactArray α} : xs.toList.length = xs.size := by
  simp [toList]

@[simp, grind =] theorem getElem_toList {xs : CompactArray α} (h : i < xs.toList.length) :
    xs.toList[i] = xs[i]'(by simpa using h) := by
  simp [toList]

@[simp] theorem toList_inj {xs ys : CompactArray α} : xs.toList = ys.toList ↔ xs = ys := by
  constructor
  · intro h
    have hs : xs.size = ys.size := by simpa using congrArg List.length h
    apply ext_getElem hs
    intro i hi hi'
    have he := congrArg (fun zs : List α => zs[i]?) h
    simpa [hi, hi'] using he
  · intro h
    simp [h]

@[simp] theorem toList_append {xs ys : CompactArray α} :
    (xs ++ ys).toList = xs.toList ++ ys.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [getElem_toList, getElem_append, List.getElem_append, length_toList]

@[simp] theorem toList_extract {xs : CompactArray α} :
    (xs.extract start stop).toList = (xs.toList.drop start).take (stop - start) := by
  apply List.ext_getElem
  · simp
    omega
  · intro i hi hi'
    simp

end CompactArray

end Transmog

end -- public section
