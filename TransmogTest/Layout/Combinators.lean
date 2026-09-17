/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL.Core.Layout

/-!
# Tests for the layout combinators and the layout theorem kit

The scalar codecs and the combinators are computed by the kernel on small buffers, and the
generic locality laws of `Transmog.DSL.Core.Lemmas` are closed by `simp` and `grind` in the
shapes that `CompactArray` and the derived layouts rely on.  Nothing here goes through the DSL.
-/

namespace Transmog.Test.Layout

open Transmog Layout

/-! ## Scalar codecs -/

example : uint8.size = 1 := rfl
example : uint16.size = 2 := rfl
example : uint32.size = 4 := rfl
example : uint64.size = 8 := rfl

example : (uint8.toBytes 0x7F).data = #[0x7F] := by decide
example : (uint16.toBytes 0xABCD).data = #[0xCD, 0xAB] := by decide
example : (uint32.toBytes 0xDEADBEEF).data = #[0xEF, 0xBE, 0xAD, 0xDE] := by decide
example : (uint64.toBytes 0x0102030405060708).data = #[8, 7, 6, 5, 4, 3, 2, 1] := by decide

example : uint8.fromBytes ⟨#[0x7F]⟩ = 0x7F := by decide
example : uint16.fromBytes ⟨#[0xCD, 0xAB]⟩ = 0xABCD := by decide
example : uint32.fromBytes ⟨#[0xEF, 0xBE, 0xAD, 0xDE]⟩ = 0xDEADBEEF := by decide
example : uint64.fromBytes ⟨#[8, 7, 6, 5, 4, 3, 2, 1]⟩ = 0x0102030405060708 := by decide

-- The exec path writes and reads its window at a nonzero offset and touches nothing else.
example : (uint8.store ⟨#[9, 9, 9]⟩ 0x7F 1 (by decide)).data = #[9, 0x7F, 9] := by decide
example : (uint16.store ⟨#[9, 9, 9, 9]⟩ 0xABCD 1 (by decide)).data = #[9, 0xCD, 0xAB, 9] := by
  decide
example : (uint32.store ⟨#[9, 9, 9, 9, 9, 9]⟩ 0xDEADBEEF 1 (by decide)).data =
    #[9, 0xEF, 0xBE, 0xAD, 0xDE, 9] := by decide
example : (uint64.store ⟨#[9, 9, 9, 9, 9, 9, 9, 9, 9]⟩ 0x0102030405060708 1 (by decide)).data =
    #[9, 8, 7, 6, 5, 4, 3, 2, 1] := by decide
example : uint8.load ⟨#[9, 0x7F, 9]⟩ 1 (by decide) = 0x7F := by decide
example : uint16.load ⟨#[9, 0xCD, 0xAB, 9]⟩ 1 (by decide) = 0xABCD := by decide
example : uint32.load ⟨#[9, 0xEF, 0xBE, 0xAD, 0xDE, 9]⟩ 1 (by decide) = 0xDEADBEEF := by decide
example : uint64.load ⟨#[9, 8, 7, 6, 5, 4, 3, 2, 1]⟩ 1 (by decide) = 0x0102030405060708 := by
  decide

/-! ## Masked subtype codecs -/

example : (fits8 4 (by decide)).size = 1 := rfl
example : (fits32 31 (by decide)).size = 4 := rfl

example : ((fits8 4 (by decide)).toBytes ⟨0xF, by decide⟩).data = #[0xF] := by decide
-- Decoding masks the raw scalar to the declared width.
example : ((fits8 4 (by decide)).fromBytes ⟨#[0xAB]⟩).val = 0xB := by decide
example : ((fits16 12 (by decide)).fromBytes ⟨#[0xCD, 0xAB]⟩).val = 0xBCD := by decide
example : ((fits32 31 (by decide)).fromBytes ⟨#[0xFF, 0xFF, 0xFF, 0xFF]⟩).val = 0x7FFFFFFF := by
  decide
example : ((fits64 8 (by decide)).fromBytes ⟨#[0xAB, 0xCD, 0, 0, 0, 0, 0, 0]⟩).val = 0xAB := by
  decide
example : ((fits32 31 (by decide)).load ⟨#[9, 0xFF, 0xFF, 0xFF, 0xFF]⟩ 1 (by decide)).val =
    0x7FFFFFFF := by decide

/-! ## Products with a gap -/

example : (uint8.prodAt uint16 2 (by decide)).size = 4 := rfl
example : ((uint8.prodAt uint16 2 (by decide)).toBytes (1, 0x0203)).data = #[1, 0, 3, 2] := by
  decide
example : (uint8.prodAt uint16 2 (by decide)).fromBytes ⟨#[1, 0xFF, 3, 2]⟩ = (1, 0x0203) := by
  decide
-- The gap is zero-filled on the exec path as well, whatever the buffer held before.
example : ((uint8.prodAt uint16 2 (by decide)).store ⟨#[9, 9, 9, 9, 9, 9]⟩ (1, 0x0203) 1
    (by decide)).data = #[9, 1, 0, 3, 2, 9] := by decide
example : (uint8.prodAt uint16 2 (by decide)).load ⟨#[9, 1, 0xFF, 3, 2, 9]⟩ 1 (by decide) =
    (1, 0x0203) := by decide
-- Adjacent placement has no gap.
example : ((uint8.prodAt uint8 1 (by decide)).toBytes (1, 2)).data = #[1, 2] := by decide

/-! ## Tail padding and alignment -/

example : (uint8.pad 4 2 (by decide) (by decide)).size = 4 := rfl
example : ((uint8.pad 4 2 (by decide) (by decide)).toBytes 7).data = #[7, 0, 0, 0] := by decide
example : (uint8.pad 4 2 (by decide) (by decide)).fromBytes ⟨#[7, 1, 1, 1]⟩ = 7 := by decide
example : ((uint8.pad 4 2 (by decide) (by decide)).store ⟨#[9, 9, 9, 9, 9]⟩ 7 1
    (by decide)).data = #[9, 7, 0, 0, 0] := by decide
example : (uint8.pad 4 2 (by decide) (by decide)).load ⟨#[9, 7, 5, 5, 5]⟩ 1 (by decide) = 7 := by
  decide
-- Padding to the current size is the identity on the bytes.
example : ((uint16.pad 2 1 (by decide) (by decide)).toBytes 0xABCD).data = #[0xCD, 0xAB] := by
  decide

/-! ## Transport along a retraction -/

/-- A `Bool` stored as a byte, any nonzero byte reading back as `true`. -/
abbrev boolLayout : Layout Bool 0 :=
  uint8.ofRetract (fun b => b.toUInt8) (fun x => x != 0) (by decide)

example : boolLayout.size = 1 := rfl
example : (boolLayout.toBytes true).data = #[1] := by decide
example : (boolLayout.toBytes false).data = #[0] := by decide
example : boolLayout.fromBytes ⟨#[5]⟩ = true := by decide
example : boolLayout.fromBytes ⟨#[0]⟩ = false := by decide
example : (boolLayout.store ⟨#[9, 9]⟩ true 1 (by decide)).data = #[9, 1] := by decide

/-! ## A layout from its specification alone -/

/-- Two bytes in order, with the exec fields left to run the specification. -/
abbrev pairLayout : Layout (UInt8 × UInt8) 0 :=
  Layout.ofSpec 2 (by decide) (by decide) (fun x => ⟨#[x.1, x.2]⟩) (fun bs => (bs[0]!, bs[1]!))
    (fun _ => rfl) (fun _ => rfl)

example : pairLayout.size = 2 := rfl
example : (pairLayout.toBytes (1, 2)).data = #[1, 2] := by decide
example : pairLayout.fromBytes ⟨#[1, 2, 3]⟩ = (1, 2) := by decide
example : (pairLayout.store ⟨#[9, 9, 9, 9]⟩ (1, 2) 1 (by decide)).data = #[9, 1, 2, 9] := by
  decide
example : pairLayout.load ⟨#[9, 1, 2, 9]⟩ 1 (by decide) = (1, 2) := by decide

/-! ## The layout theorem kit -/

section

variable {ρ : Type} {k : Nat} (L : Layout ρ k) {bs : ByteArray} {x y : ρ} {off : Nat}

example (h : off + L.size ≤ bs.size) : (L.store bs x off h).size = bs.size := by simp
example (h : off + L.size ≤ bs.size) : (L.store bs x off h).size = bs.size := by grind

example (h : off + L.size ≤ bs.size) :
    L.load (L.store bs x off h) off (by simpa using h) = x := by simp
example (h : off + L.size ≤ bs.size) :
    L.load (L.store bs x off h) off (by simpa using h) = x := by grind

example (h : off + L.size ≤ bs.size) :
    (L.store bs x off h).extract off (off + L.size) = L.toBytes x := by simp

example (h : off + L.size ≤ bs.size) (hj : j < off) : (L.store bs x off h)[j]! = bs[j]! := by
  simp [hj]
example (h : off + L.size ≤ bs.size) (hj : off + L.size ≤ j) :
    (L.store bs x off h)[j]! = bs[j]! := by
  simp [hj]

example (h : off + L.size ≤ bs.size) (hj : j + n ≤ bs.size) (hd : off + L.size ≤ j) :
    (L.store bs x off h).extract j (j + n) = bs.extract j (j + n) := by
  simp [hj, hd]

-- A foreign store at a disjoint offset is invisible to load, which is what lets two layouts sit
-- side by side.
example {L' : Layout ρ' k'} {y : ρ'} (h_in : inOff + L'.size ≤ bs.size)
    (h_un : unOff + L.size ≤ (L'.store bs y inOff h_in).size) (hd : inOff + L'.size ≤ unOff) :
    L.load (L'.store bs y inOff h_in) unOff h_un =
      L.load bs unOff (by simpa using h_un) := by
  simp [hd]
example {L' : Layout ρ' k'} {y : ρ'} (h_in : inOff + L'.size ≤ bs.size)
    (h_un : unOff + L.size ≤ (L'.store bs y inOff h_in).size) (hd : unOff + L.size ≤ inOff) :
    L.load (L'.store bs y inOff h_in) unOff h_un =
      L.load bs unOff (by simpa using h_un) := by
  grind

example : L.toBytes x = L.toBytes y ↔ x = y := by simp
example (h : L.toBytes x = L.toBytes y) : x = y := by simpa using h

example (off : USize) (h : off.toNat + L.size ≤ bs.size) :
    L.ustore bs x off h = L.store bs x off.toNat h := by simp
example (off : USize) (h : off.toNat + L.size ≤ bs.size) :
    L.uload bs off h = L.load bs off.toNat h := by simp

-- The flagship statement, in two generic rewrites from the kit: the byte-level round trip is
-- the identity for every type with a representation and a layout.
example [DataRepr α ρ] (x : α) (h : off + L.size ≤ bs.size) :
    DataRepr.fromRepr
      (L.load (L.store bs (DataRepr.toRepr x) off h) off (by simpa [L.size_store h] using h)) =
      x := by
  rw [L.load_store_self, DataRepr.from_to]
example [DataRepr α ρ] (x : α) (h : off + L.size ≤ bs.size) :
    DataRepr.fromRepr
      (L.load (L.store bs (DataRepr.toRepr x) off h) off (by simpa [L.size_store h] using h)) =
      x := by
  simp

end

/-! ## Axioms -/

-- The byte codecs of the wider scalars rest on the `bv_decide` byte recompositions.
/-- info: 'Transmog.Layout.uint8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Transmog.Layout.uint8

/--
info: 'Transmog.Layout.uint32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.Transmog.Data.ByteArray.Lemmas.0.UInt32.of_le_bytes._native.bv_decide.ax_1_11]
-/
#guard_msgs in
#print axioms Transmog.Layout.uint32

-- The kit itself adds nothing.
/-- info: 'Transmog.Layout.load_store_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Transmog.Layout.load_store_self

/--
info: 'Transmog.Layout.load_store_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Transmog.Layout.load_store_of_disjoint

end Transmog.Test.Layout
