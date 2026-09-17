/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL.Core.Basic

/-!
# Generic layout theorems

The refinement equations `Layout.store_eq_append` and `Layout.load_eq_extract` put every
layout in the *splice* normal form

```
bs.extract 0 off ++ middle ++ bs.extract (off + middle.size) bs.size
```

This file derives, once and for all, the byte-level locality laws every layout satisfies: store
preserves size, store writes exactly its window, load reads exactly its window, and the
round-trip laws that follow.  The first section proves the corresponding facts about the splice
shape itself, generically in the middle chunk.
-/

public section

/-!
## Splice algebra on `ByteArray`

All lemmas abstract the middle size (`hA : A.size = n`), following the upstream idiom of
`ByteArray.extract_append_eq_left`: the statements then match the shapes produced by
`Layout.store_eq_append` purely syntactically, and the layout kit instantiates `hA` with
`Layout.size_toBytes`.
-/

namespace ByteArray

variable {bs A : ByteArray} {off n : Nat}

theorem size_splice (hA : A.size = n) (h : off + n ≤ bs.size) :
    (bs.extract 0 off ++ A ++ bs.extract (off + n) bs.size).size = bs.size := by
  subst hA
  simp only [size_append, size_extract]
  omega

theorem splice_extract_prefix (hA : A.size = n) (h : off + n ≤ bs.size) :
    (bs.extract 0 off ++ A ++ bs.extract (off + n) bs.size).extract 0 (off + n) =
      bs.extract 0 off ++ A := by
  subst hA
  exact extract_append_eq_left (by simp only [size_append, size_extract]; omega)

theorem splice_extract_suffix (hA : A.size = n) (h : off + n ≤ bs.size)
    (hj : off + n ≤ j) :
    (bs.extract 0 off ++ A ++ bs.extract (off + n) bs.size).extract j bs.size =
      bs.extract j bs.size := by
  subst hA
  rw [extract_append]
  have h₁ : (bs.extract 0 off ++ A).extract j bs.size = empty := by
    rw [extract_eq_empty_iff]
    simp only [size_append, size_extract]
    omega
  rw [h₁, empty_append, extract_extract]
  congr 1 <;> (simp only [size_append, size_extract]; omega)

theorem splice_extract_middle (hA : A.size = n) (h : off + n ≤ bs.size) :
    (bs.extract 0 off ++ A ++ bs.extract (off + n) bs.size).extract off (off + n) = A := by
  subst hA
  rw [extract_append,
    extract_append_eq_right
      (by simp only [size_extract]; omega)
      (by simp only [size_extract]; omega)]
  have h₂ : (bs.extract (off + A.size) bs.size).extract
      (off - (bs.extract 0 off ++ A).size)
      (off + A.size - (bs.extract 0 off ++ A).size) = empty := by
    rw [extract_eq_empty_iff]
    simp only [size_append, size_extract]
    omega
  rw [h₂, append_empty]

theorem getElem!_splice_of_notin (hA : A.size = n) (h : off + n ≤ bs.size)
    (hj : j < off ∨ off + n ≤ j) :
    (bs.extract 0 off ++ A ++ bs.extract (off + n) bs.size)[j]! = bs[j]! := by
  subst hA
  by_cases hjs : j < bs.size
  · rw [getElem!_pos _ j (by rwa [size_splice rfl h]), getElem!_pos bs j hjs]
    rcases hj with hj | hj
    · rw [getElem_append_left (by simp only [size_append, size_extract]; omega),
        getElem_append_left (by simp only [size_extract]; omega),
        getElem_extract]
      congr 1
      omega
    · rw [getElem_append_right (by simp only [size_append, size_extract]; omega),
        getElem_extract]
      congr 1
      simp only [size_append, size_extract]
      omega
  · rw [getElem!_neg _ j (by rwa [size_splice rfl h]), getElem!_neg bs j hjs]

/-- Two adjacent splices compose into one splice with the concatenated middle. -/
theorem splice_splice_adjacent
    (hA : A.size = m) (hB : B.size = n) (h : off + m + n ≤ bs.size) :
    (bs.extract 0 off ++ A ++ bs.extract (off + m) bs.size).extract 0 (off + m) ++ B ++
      (bs.extract 0 off ++ A ++ bs.extract (off + m) bs.size).extract (off + m + n)
        (bs.extract 0 off ++ A ++ bs.extract (off + m) bs.size).size =
      bs.extract 0 off ++ (A ++ B) ++ bs.extract (off + m + n) bs.size := by
  subst hA hB
  rw [size_splice rfl (by omega), splice_extract_prefix rfl (by omega),
    splice_extract_suffix rfl (by omega) (by omega),
    append_assoc (a := bs.extract 0 off) (b := A) (c := B)]

end ByteArray

/-!
## The layout theorem kit

Everything below is derived from the two refinement equations, `Layout.size_toBytes`, and
`Layout.fromBytes_toBytes`; no layout has to prove these laws individually.
-/

namespace Transmog.Layout

variable {ρ : Type v} {k : Nat} (L : Layout ρ k)

/-- Storing never changes the size of the byte array. -/
@[simp, grind =]
theorem size_store (h : off + L.size ≤ bs.size) :
    (L.store bs x off h).size = bs.size := by
  rw [L.store_eq_append]
  exact ByteArray.size_splice (L.size_toBytes x) h

/--
The bytes at `[off, off + size)` after a store are exactly
the serialized bytes, independently of the previous contents of `bs`.
-/
@[simp, grind =]
theorem extract_store_self (h : off + L.size ≤ bs.size) :
    (L.store bs x off h).extract off (off + L.size) = L.toBytes x := by
  rw [L.store_eq_append]
  exact ByteArray.splice_extract_middle (L.size_toBytes x) h

/-- Store writes only the bytes in its window `[off, off + size)`. -/
@[simp]
theorem getElem!_store_of_notin (h : off + L.size ≤ bs.size)
    (hj : j < off ∨ off + L.size ≤ j) :
    (L.store bs x off h)[j]! = bs[j]! := by
  rw [L.store_eq_append]
  exact ByteArray.getElem!_splice_of_notin (L.size_toBytes x) h hj

/-- The prefix through the stored window consists of the old prefix and the encoded value. -/
theorem extract_store_prefix (h : off + L.size ≤ bs.size) :
    (L.store bs x off h).extract 0 (off + L.size) = bs.extract 0 off ++ L.toBytes x := by
  rw [L.store_eq_append]
  exact ByteArray.splice_extract_prefix (L.size_toBytes x) h

/-- The suffix from any `j` past the window is untouched by a store at `off`. -/
theorem extract_store_suffix (h : off + L.size ≤ bs.size) (hj : off + L.size ≤ j) :
    (L.store bs x off h).extract j bs.size = bs.extract j bs.size := by
  rw [L.store_eq_append]
  exact ByteArray.splice_extract_suffix (L.size_toBytes x) h hj

/-- Load reads back what store wrote. -/
@[simp, grind =]
theorem load_store_self (h : off + L.size ≤ bs.size) :
    L.load (L.store bs x off h) off (by simpa [L.size_store h] using h) = x := by
  rw [L.load_eq_extract, L.extract_store_self h, L.fromBytes_toBytes]

/-- Load reads only the bytes in its window `[off, off + size)`. -/
theorem load_congr (h : ∀ j, off ≤ j → j < off + L.size → bs[j]! = bs'[j]!)
     :
    L.load bs off h₁ = L.load bs' off h₂ := by
  rw [L.load_eq_extract, L.load_eq_extract]
  congr 1
  rw [ByteArray.extract_eq_extract_iff_getElem h₁ h₂]
  intro m hm
  have hb := h (off + m) (by omega) (by omega)
  rwa [getElem!_pos bs _ (by omega), getElem!_pos bs' _ (by omega)] at hb

/-- Load only depends on the bytes in `[off, off + size)`, extract form. -/
theorem load_eq_of_extract_eq
    (h : bs.extract off (off + L.size) = bs'.extract off (off + L.size)) :
    L.load bs off h₁ = L.load bs' off h₂ := by
  rw [L.load_eq_extract, L.load_eq_extract, h]

/--
A foreign layout's store at a disjoint offset is invisible to load.  This heterogeneous form
is what lets two different layouts sit side by side in a product.
-/
@[simp, grind =]
theorem load_store_of_disjoint (L' : Layout ρ' k')
    {h_in : inOff + L'.size ≤ bs.size}
    {h_un : unOff + L.size ≤ (L'.store bs x inOff h_in).size}
    (h : inOff + L'.size ≤ unOff ∨ unOff + L.size ≤ inOff) :
    L.load (L'.store bs x inOff h_in) unOff h_un =
      L.load bs unOff (by simpa only [L'.size_store] using h_un) := by
  apply L.load_congr
  intro j hj₁ hj₂
  exact L'.getElem!_store_of_notin h_in (by omega)

/-- A store to a disjoint offset does not change the loaded value. -/
@[simp]
theorem load_store_disjoint
    (h : inOff + L.size ≤ unOff ∨ unOff + L.size ≤ inOff) :
    L.load (L.store bs x inOff h_in) unOff h_un =
      L.load bs unOff (by simpa only [L.size_store] using h_un) :=
  L.load_store_of_disjoint L h

/-- A store leaves every disjoint byte window unchanged. -/
@[simp]
theorem extract_store_of_disjoint (h : off + L.size ≤ bs.size)
    (hj : j + n ≤ bs.size) (hd : off + L.size ≤ j ∨ j + n ≤ off) :
    (L.store bs x off h).extract j (j + n) = bs.extract j (j + n) := by
  rw [ByteArray.extract_eq_extract_iff_getElem (by simpa using hj) hj]
  intro i hi
  have he := L.getElem!_store_of_notin (x := x) (j := j + i) h (by omega)
  have hb : j + i < bs.size := by omega
  have hs : j + i < (L.store bs x off h).size := by simpa using hb
  simpa only [getElem!_pos (L.store bs x off h) (j + i) hs,
    getElem!_pos bs (j + i) hb] using he

/-- Equal serialized bytes correspond to equal values. -/
@[simp] theorem toBytes_inj : L.toBytes x = L.toBytes y ↔ x = y := by
  constructor
  · intro h
    have := congrArg L.fromBytes h
    simpa [L.fromBytes_toBytes] using this
  · intro h
    simp [h]

attribute [simp, grind =] Layout.fromBytes_toBytes Layout.uload_eq_load Layout.ustore_eq_store

/--
The byte-level round trip is the identity on the represented type: storing the representation
of `x` and loading it back recovers `x`, for every type with a representation and every layout
of that representation.
-/
theorem fromRepr_load_store_toRepr [DataRepr α ρ] {x : α} (h : off + L.size ≤ bs.size) :
    DataRepr.fromRepr
      (L.load (L.store bs (DataRepr.toRepr x) off h) off (by simpa [L.size_store h] using h)) =
      x := by
  rw [L.load_store_self, DataRepr.from_to]

end Transmog.Layout

end -- public section
