/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL.Core.Basic
public import Transmog.DSL.Core.Lemmas
public import Transmog.DSL.Core.UInt
public import Transmog.Data.ByteArray.Basic
public import Transmog.Data.ByteArray.Lemmas

/-!
# Layout combinator library

A derived layout is a shuffled, padded product of scalar codecs.  The combinators here carry all
the proof content once, so the `derive_layout` elaborator only assembles: primitives for the
`UIntN` scalars, `prodAt` to place two layouts at a relative offset (the gap is zero-filled
padding), `pad` to grow the size and set the struct alignment, and `ofRetract` to transport along
a section-retraction pair (slot reordering, where `Prod` eta makes the round trip `rfl`, and
subtype masking via `fitsN`).

Each combinator gives the spec fields (`toBytes`/`fromBytes` plus their two laws) and overrides
the exec fields with the fast in-place primitives; the two refinement equations are discharged
through the splice normal-form lemmas.  Note that padding is canonical: both the spec and the
exec paths write zero bytes into gaps and tails, so `toBytes` is a function of the value alone
and stored windows support byte-comparison equality.
-/

@[expose] public section

namespace Transmog.Layout

/-! ## Transport along a retraction -/

/--
Transports a layout along functions satisfying `g (f x) = x`.
Values are encoded through `f` and decoded through `g`.
-/
def ofRetract (L : Layout ρ k)
    (f : ρ' → ρ) (g : ρ → ρ') (gf : ∀ x, g (f x) = x) : Layout ρ' k where
  size := L.size
  size_pos := L.size_pos
  size_align := L.size_align
  toBytes x := L.toBytes (f x)
  fromBytes bs := g (L.fromBytes bs)
  size_toBytes x := L.size_toBytes (f x)
  fromBytes_toBytes x := by rw [L.fromBytes_toBytes, gf]
  store bs x off h := L.store bs (f x) off h
  load bs off h := g (L.load bs off h)
  store_eq_append bs x off h := L.store_eq_append bs (f x) off h
  load_eq_extract bs off h := by rw [L.load_eq_extract]
  ustore_eq_store _ _ _ _ := rfl
  uload_eq_load _ _ _ := rfl

/-! ## Padding and alignment -/

/--
Grow a layout to `size'` bytes of zero tail padding and declare alignment `2 ^ k'`.  Both the
spec and the exec write the zero tail, keeping the serialization canonical.
-/
def pad (L : Layout ρ k) (size' k' : Nat)
    (hsz : L.size ≤ size') (hsa : size' % 2 ^ k' = 0) : Layout ρ k' where
  size := size'
  size_pos := Nat.lt_of_lt_of_le L.size_pos hsz
  size_align := hsa
  toBytes x := L.toBytes x ++ ByteArray.replicate (size' - L.size) 0
  fromBytes bs := L.fromBytes (bs.extract 0 L.size)
  size_toBytes x := by
    simp only [ByteArray.size_append, L.size_toBytes, ByteArray.size_replicate]
    omega
  fromBytes_toBytes x := by
    rw [ByteArray.extract_append_eq_left (L.size_toBytes x).symm, L.fromBytes_toBytes]
  store bs x off h :=
    (L.store bs x off (by omega)).setZeros (off + L.size) (size' - L.size)
  load bs off h := L.load bs off (by omega)
  store_eq_append bs x off h := by
    have hb : off + L.size ≤ bs.size := by omega
    have hz : off + L.size + (size' - L.size) ≤ (L.store bs x off hb).size := by
      rw [L.size_store]
      omega
    rw [ByteArray.setZeros_eq_append _ _ _ hz, L.size_store, L.extract_store_prefix hb,
      show off + L.size + (size' - L.size) = off + size' by omega,
      L.extract_store_suffix hb (by omega),
      ByteArray.append_assoc (a := bs.extract 0 off) (b := L.toBytes x)
        (c := ByteArray.replicate (size' - L.size) 0)]
  load_eq_extract bs off h := by
    rw [L.load_eq_extract, ByteArray.extract_extract, Nat.add_zero,
      Nat.min_eq_left (by omega)]
  ustore_eq_store _ _ _ _ := rfl
  uload_eq_load _ _ _ := rfl

/-! ## Product placement -/

/--
Place `L₂` at relative offset `off₂` after `L₁` (at relative offset `0`).  The gap
`[L₁.size, off₂)` is zero-filled field padding, in both the spec and the exec path.  The result
has alignment `1`.
-/
def prodAt (L₁ : Layout ρ₁ k₁)
    (L₂ : Layout ρ₂ k₂) (off₂ : Nat) (hoff : L₁.size ≤ off₂) :
    Layout (ρ₁ × ρ₂) 0 where
  size := off₂ + L₂.size
  size_pos := by have := L₂.size_pos; omega
  size_align := Nat.mod_one _
  toBytes x := L₁.toBytes x.1 ++ ByteArray.replicate (off₂ - L₁.size) 0 ++ L₂.toBytes x.2
  fromBytes bs :=
    (L₁.fromBytes (bs.extract 0 L₁.size), L₂.fromBytes (bs.extract off₂ (off₂ + L₂.size)))
  size_toBytes x := by
    simp only [ByteArray.size_append, L₁.size_toBytes, L₂.size_toBytes, ByteArray.size_replicate]
    omega
  fromBytes_toBytes x := by
    refine Prod.ext ?_ ?_
    · show L₁.fromBytes _ = x.1
      rw [ByteArray.append_assoc, ByteArray.extract_append_eq_left (L₁.size_toBytes x.1).symm,
        L₁.fromBytes_toBytes]
    · show L₂.fromBytes _ = x.2
      rw [ByteArray.extract_append_eq_right
          (by simp only [ByteArray.size_append, L₁.size_toBytes, ByteArray.size_replicate]; omega)
          (by simp only [ByteArray.size_append, L₁.size_toBytes, ByteArray.size_replicate,
            L₂.size_toBytes]; omega),
        L₂.fromBytes_toBytes]
  store bs x off h :=
    L₂.store ((L₁.store bs x.1 off (by have := L₂.size_pos; omega)).setZeros
        (off + L₁.size) (off₂ - L₁.size))
      x.2 (off + off₂)
      (by rw [ByteArray.size_setZeros, L₁.size_store]; omega)
  load bs off h :=
    (L₁.load bs off (by have := L₂.size_pos; omega),
      L₂.load bs (off + off₂) (by omega))
  store_eq_append bs x off h := by
    have hb1 : off + L₁.size ≤ bs.size := by have := L₂.size_pos; omega
    have hM₂ : (L₁.store bs x.1 off hb1).setZeros (off + L₁.size) (off₂ - L₁.size) =
        bs.extract 0 off ++ (L₁.toBytes x.1 ++ ByteArray.replicate (off₂ - L₁.size) 0) ++
          bs.extract (off + off₂) bs.size := by
      have hz : off + L₁.size + (off₂ - L₁.size) ≤ (L₁.store bs x.1 off hb1).size := by
        rw [L₁.size_store]
        omega
      rw [ByteArray.setZeros_eq_append _ _ _ hz, L₁.size_store,
        L₁.extract_store_prefix hb1,
        show off + L₁.size + (off₂ - L₁.size) = off + off₂ by omega,
        L₁.extract_store_suffix hb1 (by omega),
        ByteArray.append_assoc (a := bs.extract 0 off) (b := L₁.toBytes x.1)
          (c := ByteArray.replicate (off₂ - L₁.size) 0)]
    rw [L₂.store_eq_append, hM₂,
      ByteArray.splice_splice_adjacent
        (by simp only [ByteArray.size_append, L₁.size_toBytes, ByteArray.size_replicate]; omega)
        (L₂.size_toBytes x.2) (by omega),
      Nat.add_assoc]
  load_eq_extract bs off h := by
    refine Prod.ext ?_ ?_
    · show L₁.load bs off _ = L₁.fromBytes _
      rw [L₁.load_eq_extract, ByteArray.extract_extract, Nat.add_zero,
        Nat.min_eq_left (by omega)]
    · show L₂.load bs (off + off₂) _ = L₂.fromBytes _
      rw [L₂.load_eq_extract, ByteArray.extract_extract, Nat.min_self, Nat.add_assoc]
  ustore_eq_store _ _ _ _ := rfl
  uload_eq_load _ _ _ := rfl

/-! ## Scalar primitives -/

/-- The 1-byte scalar codec. -/
def uint8 : Layout UInt8 0 where
  size := 1
  size_pos := by decide
  size_align := by decide
  toBytes := UInt8.toLEBytes
  fromBytes := UInt8.ofLEBytes
  size_toBytes := UInt8.size_toLEBytes
  fromBytes_toBytes := UInt8.ofLEBytes_toLEBytes
  store bs v off h := bs.set off v (by omega)
  load bs off h := bs[off]'(by omega)
  store_eq_append bs v off h := ByteArray.set_eq_append bs off v (by omega)
  load_eq_extract bs off h := ByteArray.getElem_eq_ofLEBytes_extract bs off (by omega)
  ustore_eq_store _ _ _ _ := rfl
  uload_eq_load _ _ _ := rfl

/-- The 2-byte little-endian scalar codec. -/
def uint16 : Layout UInt16 1 where
  size := 2
  size_pos := by decide
  size_align := by decide
  toBytes := UInt16.toLEBytes
  fromBytes := UInt16.ofLEBytes
  size_toBytes := UInt16.size_toLEBytes
  fromBytes_toBytes := UInt16.ofLEBytes_toLEBytes
  store bs v off h := bs.set16 off v (by omega)
  load bs off h := bs.get16 off (by omega)
  store_eq_append bs v off h := ByteArray.set16_eq_append bs off v (by omega)
  load_eq_extract bs off h := ByteArray.get16_eq_ofLEBytes_extract bs off (by omega)
  ustore_eq_store _ _ _ _ := rfl
  uload_eq_load _ _ _ := rfl

/-- The 4-byte little-endian scalar codec. -/
def uint32 : Layout UInt32 2 where
  size := 4
  size_pos := by decide
  size_align := by decide
  toBytes := UInt32.toLEBytes
  fromBytes := UInt32.ofLEBytes
  size_toBytes := UInt32.size_toLEBytes
  fromBytes_toBytes := UInt32.ofLEBytes_toLEBytes
  store bs v off h := bs.set32 off v (by omega)
  load bs off h := bs.get32 off (by omega)
  store_eq_append bs v off h := ByteArray.set32_eq_append bs off v (by omega)
  load_eq_extract bs off h := ByteArray.get32_eq_ofLEBytes_extract bs off (by omega)
  ustore_eq_store _ _ _ _ := rfl
  uload_eq_load _ _ _ := rfl

/-- The 8-byte little-endian scalar codec. -/
def uint64 : Layout UInt64 3 where
  size := 8
  size_pos := by decide
  size_align := by decide
  toBytes := UInt64.toLEBytes
  fromBytes := UInt64.ofLEBytes
  size_toBytes := UInt64.size_toLEBytes
  fromBytes_toBytes := UInt64.ofLEBytes_toLEBytes
  store bs v off h := bs.set64 off v (by omega)
  load bs off h := bs.get64 off (by omega)
  store_eq_append bs v off h := ByteArray.set64_eq_append bs off v (by omega)
  load_eq_extract bs off h := ByteArray.get64_eq_ofLEBytes_extract bs off (by omega)
  ustore_eq_store _ _ _ _ := rfl
  uload_eq_load _ _ _ := rfl

/-!
## Masked subtype slots

A ranged repr slot stores `{ x : UIntN // fitsBits w x }`.  Encoding drops to `.val`; decoding
reads the raw scalar and normalizes with `extractSlice 0 w`, whose result fits the declared width and
which is the identity on values satisfying the bound.
-/

/-- Codec for a `w`-bit value stored in a `UInt8`. -/
def fits8 (w : Nat) (hw : w < 8) :
    Layout { x : UInt8 // x.fitsBits w } 0 :=
  uint8.ofRetract Subtype.val
    (fun raw => ⟨raw.extractSlice 0 w,
      UInt8.fitsBits_extractSlice w.sub_zero.symm (by omega) (by omega) raw⟩)
    (fun x => Subtype.ext (UInt8.extractSlice_zero_of_fitsBits hw x.val x.property))

/-- Codec for a `w`-bit value stored in a `UInt16`. -/
def fits16 (w : Nat) (hw : w < 16) :
    Layout { x : UInt16 // x.fitsBits w } 1 :=
  uint16.ofRetract Subtype.val
    (fun raw => ⟨raw.extractSlice 0 w,
      UInt16.fitsBits_extractSlice w.sub_zero.symm (by omega) (by omega) raw⟩)
    (fun x => Subtype.ext (UInt16.extractSlice_zero_of_fitsBits hw x.val x.property))

/-- Codec for a `w`-bit value stored in a `UInt32`. -/
def fits32 (w : Nat) (hw : w < 32) :
    Layout { x : UInt32 // x.fitsBits w } 2 :=
  uint32.ofRetract Subtype.val
    (fun raw => ⟨raw.extractSlice 0 w,
      UInt32.fitsBits_extractSlice w.sub_zero.symm (by omega) (by omega) raw⟩)
    (fun x => Subtype.ext (UInt32.extractSlice_zero_of_fitsBits hw x.val x.property))

/-- Codec for a `w`-bit value stored in a `UInt64`. -/
def fits64 (w : Nat) (hw : w < 64) :
    Layout { x : UInt64 // x.fitsBits w } 3 :=
  uint64.ofRetract Subtype.val
    (fun raw => ⟨raw.extractSlice 0 w,
      UInt64.fitsBits_extractSlice w.sub_zero.symm (by omega) (by omega) raw⟩)
    (fun x => Subtype.ext (UInt64.extractSlice_zero_of_fitsBits hw x.val x.property))

/-!
## The `transmog_bridge` manifest

The complete membership of the closed bridge set (see `register_simp_attr transmog_bridge`):
the combinator unfoldings, the splice/extract and arithmetic algebra those unfoldings expose,
and the literal-arithmetic simprocs.  The emitted `_eq_ref` proofs run
`simp only [transmog_bridge, <the two per-type definitions>]` and nothing else, so a new
combinator (or a new normal-form mismatch) is handled by extending this manifest, never by
widening the emitted tactic.
-/

attribute [transmog_bridge]
  -- combinator unfoldings
  ofRetract pad prodAt uint8 uint16 uint32 uint64 fits8 fits16 fits32 fits64
  -- nested relative offsets and extraction windows
  Nat.add_assoc Nat.min_def Nat.add_le_add_iff_left Nat.le_refl Nat.min_self
  ByteArray.append_assoc ByteArray.extract_extract
  -- degenerate padding
  ByteArray.setZeros_zero ByteArray.replicate_zero ByteArray.append_empty
  ByteArray.empty_append
  -- congruence closers (tuple and subtype components; proofs differ only proof-irrelevantly)
  Prod.mk.injEq Subtype.mk.injEq
  -- conditionals left by `Nat.min_def`
  if_true if_false

-- The literal-arithmetic simprocs (`Nat.reduceAdd`/`reduceSub`/`reduceLeDiff`, `reduceIte`)
-- are listed by name in the emitted tactic (`mkBridgeTactic`): builtin simprocs cannot be
-- tagged into a custom simp set from downstream.

end Transmog.Layout

namespace Transmog

instance : HasLayout UInt8 UInt8 0 := ⟨Layout.uint8⟩
instance : HasLayout UInt16 UInt16 1 := ⟨Layout.uint16⟩
instance : HasLayout UInt32 UInt32 2 := ⟨Layout.uint32⟩
instance : HasLayout UInt64 UInt64 3 := ⟨Layout.uint64⟩

end Transmog

end -- @[expose] public section
