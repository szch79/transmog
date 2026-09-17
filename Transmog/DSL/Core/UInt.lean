/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Std.Tactic.BVDecide
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import Transmog.DSL.Core.Basic
public import Transmog.Data.UInt

/-!
# Unsigned scalar bit operations

Extraction, insertion, and bounded-value predicates for the fixed-width unsigned integers.
The generic slice laws are registered in the representation proof simp sets.
-/

namespace Transmog.Slice

private theorem toNat_one_shiftLeft (hn : n < w) :
    (1#w <<< n).toNat = 2 ^ n := by
  have h1 : (2 : Nat) ^ n < 2 ^ w := Nat.pow_lt_pow_right (by omega) hn
  have h2 : (0 : Nat) < 2 ^ n := n.two_pow_pos
  have h3 : (1 : Nat) < 2 ^ w := by omega
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  simp only [Nat.mod_eq_of_lt h3]
  rw [Nat.one_shiftLeft, Nat.mod_eq_of_lt h1]

private theorem toNat_one_shiftLeft_sub_one (hn : n < w) :
    ((1#w <<< n) - 1#w).toNat = 2 ^ n - 1 := by
  have h1 : (2 : Nat) ^ n < 2 ^ w := Nat.pow_lt_pow_right (by omega) hn
  have h2 : (0 : Nat) < 2 ^ n := n.two_pow_pos
  have h3 : (1 : Nat) < 2 ^ w := by omega
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, toNat_one_shiftLeft hn]
  simp only [Nat.mod_eq_of_lt h3]
  rw [show 2 ^ w - 1 + 2 ^ n = 2 ^ w + (2 ^ n - 1) by omega]
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- The low-`n` mask `1 <<< n - 1` reads back `decide (i < n)` per bit. -/
private theorem getLsbD_one_shiftLeft_sub_one (hn : n < w) (i : Nat) :
    ((1#w <<< n) - 1#w).getLsbD i = decide (i < n) := by
  show ((1#w <<< n) - 1#w).toNat.testBit i = decide (i < n)
  rw [toNat_one_shiftLeft_sub_one hn, Nat.testBit_two_pow_sub_one]

/-- Extract-of-insert round-trips the payload (`BitVec` level). -/
private theorem extract_insert_self (b v : BitVec w)
    (hse : s < e) (he : e ≤ w) (hw : e - s < w)
    (hv : v.toNat < 2 ^ (e - s)) :
    (((b &&& ~~~(((1#w <<< (e - s)) - 1#w) <<< s)) |||
        ((v &&& ((1#w <<< (e - s)) - 1#w)) <<< s)) >>> s) &&&
      ((1#w <<< (e - s)) - 1#w) = v := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    getLsbD_one_shiftLeft_sub_one hw]
  by_cases hlt : i < e - s
  · simp [hlt, hi, show s + i - s = i by omega, show ¬(s + i < s) by omega,
      show s + i < w by omega]
  · have hvi : v.toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega))
    simp [hlt, BitVec.getLsbD, Nat.testBit_lt_two_pow hvi]

/--
The low-`n` mask is the identity on values fitting in `n` bits
(`BitVec` level, stated in the exact shape left by the `toBitVec`
transfer of `extractSlice 0 n`).
-/
private theorem shiftRight_zero_and_mask (hn : n < w)
    (v : BitVec w) (hv : v.toNat < 2 ^ n) :
    (v >>> (0 : Nat)) &&& ((1#w <<< n) - 1#w) = v := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    getLsbD_one_shiftLeft_sub_one hn, Nat.zero_add]
  by_cases hlt : i < n
  · simp [hlt]
  · have hvi : v.toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega))
    simp [hlt, BitVec.getLsbD, Nat.testBit_lt_two_pow hvi]

/-- Disjoint insert is invisible to extract (`BitVec` level). -/
private theorem extract_insert_disjoint
    (b v : BitVec w)
    (hd : e₁ ≤ s₂ ∨ e₂ ≤ s₁)
    (h₁ : s₁ < e₁) (he₁ : e₁ ≤ w) (hw₁ : e₁ - s₁ < w)
    (h₂ : s₂ < e₂) (hw₂ : e₂ - s₂ < w) :
    (((b &&& ~~~(((1#w <<< (e₂ - s₂)) - 1#w) <<< s₂)) |||
        ((v &&& ((1#w <<< (e₂ - s₂)) - 1#w)) <<< s₂)) >>> s₁) &&&
      ((1#w <<< (e₁ - s₁)) - 1#w) =
    (b >>> s₁) &&& ((1#w <<< (e₁ - s₁)) - 1#w) := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    getLsbD_one_shiftLeft_sub_one hw₁,
    getLsbD_one_shiftLeft_sub_one hw₂]
  by_cases hlt : i < e₁ - s₁
  · have hsw : s₁ + i < w := by omega
    by_cases hs2 : s₂ ≤ s₁ + i
    · simp [hsw, show ¬(s₁ + i - s₂ < e₂ - s₂) by omega,
        show ¬(s₁ + i < s₂) from by omega]
    · simp [hsw, show s₁ + i < s₂ by omega]
  · simp [hlt]

end Transmog.Slice

/-! ## Per-type operations and wrappers -/

@[expose] public section

open Lean in
set_option hygiene false in
local macro "declare_transmog_uint_ops" typeName:ident bits:term:arg : command => do
  let typeString := typeName.getId.getString!
  let boolToUInt := mkCIdent (`Bool ++ Name.mkSimple s!"to{typeString}")
  -- Core's `toBitVec` bridge lemmas are `protected`; reference them qualified.
  let tN := typeName.getId
  let tbAnd := mkCIdent (tN ++ `toBitVec_and)
  let tbOr := mkCIdent (tN ++ `toBitVec_or)
  let tbNot := mkCIdent (tN ++ `toBitVec_not)
  let tbShl := mkCIdent (tN ++ `toBitVec_shiftLeft)
  let tbShr := mkCIdent (tN ++ `toBitVec_shiftRight)
  let tbSub := mkCIdent (tN ++ `toBitVec_sub)
  let tbOfNat := mkCIdent (tN ++ `toBitVec_ofNat)
  let tbOfNat' := mkCIdent (tN ++ `toBitVec_ofNat')
  let tbInj := mkCIdent (tN ++ `toBitVec_inj)
  let tbLt := mkCIdent (tN ++ `lt_iff_toBitVec_lt)
  let tnShl := mkCIdent (tN ++ `toNat_shiftLeft)
  let tnOne := mkCIdent (tN ++ `toNat_one)
  let cmds ← Syntax.getArgs <$> `(
namespace $typeName

/-- True when `x` fits in `width` least significant bits. -/
@[transmog_subtype_simps]
def fitsBits (width : Nat) (x : $typeName) : Prop :=
  if width < $bits then x < (1 : $typeName) <<< ofNat width else True

instance : Decidable (fitsBits width x) := by
  dsimp [fitsBits]
  infer_instance

@[simp] theorem fitsBits_of_ge (h : $bits ≤ width) : fitsBits width x := by
  simp [fitsBits, Nat.not_lt.mpr h]

theorem fitsBits_iff_of_lt (h : width < $bits) :
    fitsBits width x ↔ x < (1 : $typeName) <<< ofNat width := by
  simp [fitsBits, h]

/--
The arithmetic reading of `fitsBits`, under which `grind` reasons about it.  The two sides also
agree from the word width on, where both hold.
-/
@[grind =]
theorem fitsBits_iff_toNat_lt : fitsBits width x ↔ x.toNat < 2 ^ width := by
  unfold fitsBits
  split
  · next h =>
    have hw : width % 2 ^ $bits % $bits = width := by omega
    rw [lt_iff_toNat_lt, $tnShl:term, toNat_ofNat', $tnOne:term, Nat.one_shiftLeft, hw,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) h)]
  · next h =>
    have := x.toNat_lt
    have : 2 ^ $bits ≤ 2 ^ width := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [true_iff]
    omega

@[inline, transmog_subtype_simps]
def lsbAsBool (x : $typeName) : Bool :=
  (x &&& (1 : $typeName)) = (1 : $typeName)

/-- Half-open bit extraction helper used by Transmog representation codegen. -/
@[inline, transmog_subtype_simps]
def extractSlice (start stop : Nat) (x : $typeName) : $typeName :=
  x.extractLsb' start (stop - start)

attribute [transmog_subtype_simps] extractLsb'

@[inline, transmog_subtype_simps]
def insertSlice (start stop : Nat) (base payload : $typeName) : $typeName :=
  if start < $bits then
    let mask := lowMask (stop - start)
    (base &&& ~~~(mask <<< ofNat start)) ||| ((payload &&& mask) <<< ofNat start)
  else base

/--
Compiler-only twin of `insertSlice`: the code generator constant-folds `sub`/`shl`/`and` on
scalar literals but has no rule for `complement`, so the `~~~mask` above survives folding as a
runtime once-cell (an atomic guard load per call).  `0 - 1 - x` computes the same bits with
foldable ops; proofs never see this body.
-/
@[inline]
def insertSliceImpl (start stop : Nat) (base payload : $typeName) : $typeName :=
  if start < $bits then
    let mask := lowMask (stop - start)
    (base &&& ((0 : $typeName) - 1 - (mask <<< ofNat start))) |||
      ((payload &&& mask) <<< ofNat start)
  else base

@[csimp]
theorem insertSlice_eq_impl : @insertSlice = @insertSliceImpl := by
  have h : ∀ z : $typeName, ~~~z = (0 : $typeName) - 1 - z := fun z => by bv_decide
  funext start stop base payload
  simp only [insertSlice, insertSliceImpl, h]

@[inline, transmog_subtype_simps]
def packBoolLsb (payload : $typeName) (b : Bool) : $typeName :=
  (payload <<< 1) ||| $boolToUInt:ident b

@[transmog_subtype_simps 1100]
theorem extractSlice_of_start_ge {start stop : Nat} (h : $bits ≤ start)
    (x : $typeName) :
    x.extractSlice start stop = 0 := by
  rw [extractSlice, extractLsb'_of_start_ge h]

@[simp, grind =]
theorem lsbAsBool_packBoolLsb (payload : $typeName) (b : Bool) :
    lsbAsBool (packBoolLsb payload b) = b := by
  simp [lsbAsBool, packBoolLsb]
  cases b <;> bv_decide

@[simp, grind =]
theorem shiftRight_packBoolLsb_subtype
    (s : { x : $typeName // fitsBits ($bits - 1) x }) (b : Bool) :
    packBoolLsb s.val b >>> 1 = s.val := by
  have h := s.property
  simp only [packBoolLsb, fitsBits] at h ⊢
  cases b <;> bv_decide

/-! ### Generic slice lemmas (`transmog_norm`) -/

/-- The canonical slot-subtype property, keyed on `.val`. -/
@[transmog_norm, transmog_subtype_simps]
theorem fitsBits_val {k : Nat} (p : { v : $typeName // fitsBits k v }) :
    fitsBits k p.val := p.property

/-- A bool viewed as a scalar fits in one bit. -/
@[transmog_norm, transmog_subtype_simps, grind! .]
theorem fitsBits_one_toBool (b : Bool) : fitsBits 1 ($boolToUInt:ident b) := by
  cases b <;> decide

/-- `lsbAsBool` inverts the bool-to-scalar view. -/
@[transmog_norm]
theorem lsbAsBool_toBool (b : Bool) : lsbAsBool ($boolToUInt:ident b) = b := by
  cases b <;> decide

/-- An extracted slice fits in its bit width. -/
@[transmog_norm, transmog_subtype_simps]
theorem fitsBits_extractSlice {k s e : Nat} (hk : k = e - s) (hs : s < $bits)
    (hw : e - s < $bits) (x : $typeName) : fitsBits k (extractSlice s e x) := by
  subst hk
  have hb : (($bits : BitVec $bits)).toNat = $bits := rfl
  have hsA : (ofNat s).toBitVec.toNat = s % 2 ^ $bits := by
    rw [$tbOfNat':term, BitVec.toNat_ofNat]
  have hesA : (ofNat (e - s)).toBitVec.toNat = (e - s) % 2 ^ $bits := by
    rw [$tbOfNat':term, BitVec.toNat_ofNat]
  have hsm : s % 2 ^ $bits % $bits = s := by omega
  have hesm : (e - s) % 2 ^ $bits % $bits = e - s := by omega
  rw [fitsBits_iff_of_lt hw, extractSlice, extractLsb'_of_start_lt hs, lowMask_of_lt hw, $tbLt:term]
  simp only [$tbAnd:term, $tbShl:term, $tbShr:term,
    $tbSub:term, $tbOfNat:term]
  simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_umod,
    hsA, hesA, hb, hsm, hesm]
  rw [BitVec.lt_def, BitVec.toNat_and,
    Transmog.Slice.toNat_one_shiftLeft hw,
    Transmog.Slice.toNat_one_shiftLeft_sub_one hw]
  have hle : x.toBitVec.toNat >>> s &&& (2 ^ (e - s) - 1) ≤ 2 ^ (e - s) - 1 :=
    Nat.and_le_right
  have h2 : (0 : Nat) < 2 ^ (e - s) := Nat.two_pow_pos _
  rw [BitVec.toNat_ushiftRight]
  omega

/-- Extracting the lowest `w` bits fixes values that fit in `w` bits. -/
@[transmog_norm, transmog_subtype_simps, grind =]
theorem extractSlice_zero_of_fitsBits {w : Nat} (hw : w < $bits)
    (v : $typeName) (hv : fitsBits w v) :
    extractSlice 0 w v = v := by
  have hs : (0 : Nat) < $bits := by omega
  have hb : (($bits : BitVec $bits)).toNat = $bits := rfl
  have h0A : (ofNat 0).toBitVec.toNat = 0 % 2 ^ $bits := by
    rw [$tbOfNat':term, BitVec.toNat_ofNat]
  have hwA : (ofNat w).toBitVec.toNat = w % 2 ^ $bits := by
    rw [$tbOfNat':term, BitVec.toNat_ofNat]
  have h0m : 0 % 2 ^ $bits % $bits = 0 := by omega
  have hwm : w % 2 ^ $bits % $bits = w := by omega
  rw [extractSlice, extractLsb'_of_start_lt hs, Nat.sub_zero, lowMask_of_lt hw]
  rw [fitsBits_iff_of_lt hw] at hv
  rw [← $tbInj:term]
  rw [$tbLt:term] at hv
  simp only [$tbAnd:term, $tbShl:term, $tbShr:term, $tbSub:term,
    $tbOfNat:term] at hv ⊢
  simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_umod,
    h0A, hwA, hb, h0m, hwm] at hv ⊢
  apply Transmog.Slice.shiftRight_zero_and_mask hw
  have h1n : (BitVec.ofNat $bits 1).toNat = 1 := rfl
  have h1 : (2 : Nat) ^ w < 2 ^ $bits := Nat.pow_lt_pow_right (by omega) hw
  rw [BitVec.lt_def, BitVec.toNat_shiftLeft, h1n, Nat.one_shiftLeft,
    Nat.mod_eq_of_lt h1] at hv
  exact hv

/-- Extract-of-insert round-trips a fitting payload. -/
@[transmog_norm, grind =]
theorem extractSlice_insertSlice_self {s e : Nat}
    (hse : s < e) (he : e ≤ $bits) (hw : e - s < $bits)
    (base v : $typeName) (hv : fitsBits (e - s) v) :
    extractSlice s e (insertSlice s e base v) = v := by
  have hs32 : s < $bits := by omega
  have hsm : s % 2 ^ $bits % $bits = s := by omega
  have hesm : (e - s) % 2 ^ $bits % $bits = e - s := by omega
  simp only [extractSlice, insertSlice, ite_eq_left hs32,
    extractLsb'_of_start_lt hs32, lowMask_of_lt hw]
  rw [fitsBits_iff_of_lt hw] at hv
  rw [← $tbInj:term]
  rw [$tbLt:term] at hv
  have hb : (($bits : BitVec $bits)).toNat = $bits := rfl
  have hsA : (ofNat s).toBitVec.toNat = s % 2 ^ $bits := by
    rw [$tbOfNat':term, BitVec.toNat_ofNat]
  have hesA : (ofNat (e - s)).toBitVec.toNat = (e - s) % 2 ^ $bits := by
    rw [$tbOfNat':term, BitVec.toNat_ofNat]
  simp only [$tbAnd:term, $tbOr:term, $tbNot:term, $tbShl:term,
    $tbShr:term, $tbSub:term, $tbOfNat:term] at hv ⊢
  simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_umod,
    hsA, hesA, hb, hsm, hesm] at hv ⊢
  apply Transmog.Slice.extract_insert_self _ _ hse he hw
  have h1n : (BitVec.ofNat $bits 1).toNat = 1 := rfl
  have h1 : (2 : Nat) ^ (e - s) < 2 ^ $bits := Nat.pow_lt_pow_right (by omega) hw
  rw [BitVec.lt_def, BitVec.toNat_shiftLeft, h1n, Nat.one_shiftLeft,
    Nat.mod_eq_of_lt h1] at hv
  exact hv

/-- An insert into a disjoint range is invisible to extract. -/
@[transmog_norm, grind =]
theorem extractSlice_insertSlice_of_disjoint {s₁ e₁ s₂ e₂ : Nat}
    (hd : e₁ ≤ s₂ ∨ e₂ ≤ s₁)
    (h₁ : s₁ < e₁) (he₁ : e₁ ≤ $bits) (hw₁ : e₁ - s₁ < $bits)
    (h₂ : s₂ < e₂) (he₂ : e₂ ≤ $bits) (hw₂ : e₂ - s₂ < $bits)
    (base payload : $typeName) :
    extractSlice s₁ e₁ (insertSlice s₂ e₂ base payload) =
      extractSlice s₁ e₁ base := by
  have hs₁ : s₁ < $bits := by omega
  have hs₂ : s₂ < $bits := by omega
  have hb : (($bits : BitVec $bits)).toNat = $bits := rfl
  have hm₁ : (ofNat s₁).toBitVec.toNat = s₁ % 2 ^ $bits := by
    rw [$tbOfNat':term, BitVec.toNat_ofNat]
  have hm₂ : (ofNat s₂).toBitVec.toNat = s₂ % 2 ^ $bits := by
    rw [$tbOfNat':term, BitVec.toNat_ofNat]
  have hn₁ : (ofNat (e₁ - s₁)).toBitVec.toNat = (e₁ - s₁) % 2 ^ $bits := by
    rw [$tbOfNat':term, BitVec.toNat_ofNat]
  have hn₂ : (ofNat (e₂ - s₂)).toBitVec.toNat = (e₂ - s₂) % 2 ^ $bits := by
    rw [$tbOfNat':term, BitVec.toNat_ofNat]
  have hm₁' : s₁ % 2 ^ $bits % $bits = s₁ := by omega
  have hm₂' : s₂ % 2 ^ $bits % $bits = s₂ := by omega
  have hn₁' : (e₁ - s₁) % 2 ^ $bits % $bits = e₁ - s₁ := by omega
  have hn₂' : (e₂ - s₂) % 2 ^ $bits % $bits = e₂ - s₂ := by omega
  simp only [extractSlice, insertSlice, ite_eq_left hs₂,
    extractLsb'_of_start_lt hs₁, lowMask_of_lt hw₁, lowMask_of_lt hw₂]
  rw [← $tbInj:term]
  simp only [$tbAnd:term, $tbOr:term, $tbNot:term, $tbShl:term,
    $tbShr:term, $tbSub:term, $tbOfNat:term]
  simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_umod,
    hm₁, hm₂, hn₁, hn₂, hb, hm₁', hm₂', hn₁', hn₂']
  exact Transmog.Slice.extract_insert_disjoint _ _ hd h₁ he₁ hw₁ h₂ hw₂

end $typeName
  )
  return ⟨mkNullNode cmds⟩

declare_transmog_uint_ops UInt8 8
declare_transmog_uint_ops UInt16 16
declare_transmog_uint_ops UInt32 32
declare_transmog_uint_ops UInt64 64

attribute [transmog_norm, transmog_subtype_simps]
  UInt8.pos_iff_ne_zero UInt16.pos_iff_ne_zero UInt32.pos_iff_ne_zero UInt64.pos_iff_ne_zero

end -- public section
