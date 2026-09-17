/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL.Core.UInt
public import Transmog.DSL.Tactics
meta import Transmog.DSL.Core.UInt
meta import Transmog.Data.UInt

/-!
# Tests for the unsigned scalar bit operations

The kernel computes the operations on literals, an interpreter sweep compares `extractLsb'`
against its `BitVec` namesake on every byte and slice, and the lemma base is exercised through
the automation that the generated proofs rely on.
-/

namespace Transmog.Test.UInt

/-! ## `lowMask` -/

example : UInt8.lowMask 0 = 0 := by decide
example : UInt8.lowMask 3 = 7 := by decide
example : UInt8.lowMask 7 = 127 := by decide
example : UInt8.lowMask 8 = 255 := by decide
example : UInt8.lowMask 9 = 255 := by decide
example : UInt16.lowMask 16 = 0xFFFF := by decide
example : UInt32.lowMask 31 = 0x7FFFFFFF := by decide
example : UInt64.lowMask 63 = 0x7FFFFFFFFFFFFFFF := by decide
example : UInt64.lowMask 64 = 0xFFFFFFFFFFFFFFFF := by decide

/-! ## `extractLsb'` -/

example : (255 : UInt8).extractLsb' 0 8 = 255 := by decide
example : (255 : UInt8).extractLsb' 0 9 = 255 := by decide
example : (255 : UInt8).extractLsb' 3 8 = 31 := by decide
example : (255 : UInt8).extractLsb' 8 8 = 0 := by decide
example : (255 : UInt8).extractLsb' 0 0 = 0 := by decide
example : (0xAB : UInt8).extractLsb' 4 4 = 0xA := by decide
example : (0xAB : UInt8).extractLsb' 0 4 = 0xB := by decide
example : (65535 : UInt16).extractLsb' 0 16 = 65535 := by decide
example : (0xABCD : UInt16).extractLsb' 8 4 = 0xB := by decide
example : (0xABCD : UInt16).extractLsb' 16 4 = 0 := by decide
example : (0xFFFFFFFF : UInt32).extractLsb' 0 32 = 0xFFFFFFFF := by decide
example : (0xDEADBEEF : UInt32).extractLsb' 16 16 = 0xDEAD := by decide
example : (0xDEADBEEF : UInt32).extractLsb' 31 1 = 1 := by decide
example : (0xFFFFFFFFFFFFFFFF : UInt64).extractLsb' 0 64 = 0xFFFFFFFFFFFFFFFF := by decide
example : (0x0123456789ABCDEF : UInt64).extractLsb' 32 32 = 0x01234567 := by decide
example : (0x0123456789ABCDEF : UInt64).extractLsb' 64 1 = 0 := by decide

/-! ## `extractSlice` and `insertSlice` -/

example : (0xAB : UInt8).extractSlice 4 8 = 0xA := by decide
example : (0xAB : UInt8).extractSlice 0 4 = 0xB := by decide
example : (0xAB : UInt8).extractSlice 4 4 = 0 := by decide
example : (0xAB : UInt8).extractSlice 8 12 = 0 := by decide
example : (0xDEADBEEF : UInt32).extractSlice 1 32 = 0x6F56DF77 := by decide

example : (17 : UInt8).insertSlice 0 8 255 = 255 := by decide
example : (17 : UInt8).insertSlice 8 16 255 = 17 := by decide
example : (17 : UInt8).insertSlice 3 2 255 = 17 := by decide
example : (0 : UInt8).insertSlice 4 8 0xFF = 0xF0 := by decide
example : (0xFF : UInt8).insertSlice 2 4 0 = 0xF3 := by decide
example : (0 : UInt32).insertSlice 1 32 0x7FFFFFFF = 0xFFFFFFFE := by decide
example : (1 : UInt32).insertSlice 1 32 0x7FFFFFFF = 0xFFFFFFFF := by decide
example : (0 : UInt64).insertSlice 60 64 0xF = 0xF000000000000000 := by decide

-- The compiled twin agrees with the model on a masked write.
#guard (0xFF : UInt8).insertSliceImpl 2 4 0 == (0xFF : UInt8).insertSlice 2 4 0
#guard (0 : UInt32).insertSliceImpl 1 32 0x7FFFFFFF == (0 : UInt32).insertSlice 1 32 0x7FFFFFFF

/-! ## `fitsBits` -/

example : (255 : UInt8).fitsBits 8 := by decide
example : (255 : UInt8).fitsBits 100 := by decide
example : (7 : UInt8).fitsBits 3 := by decide
example : ¬ (8 : UInt8).fitsBits 3 := by decide
example : (0 : UInt8).fitsBits 0 := by decide
example : ¬ (1 : UInt8).fitsBits 0 := by decide
example : (0x7FFFFFFF : UInt32).fitsBits 31 := by decide
example : ¬ (0x80000000 : UInt32).fitsBits 31 := by decide
example : (0x7FFFFFFFFFFFFFFF : UInt64).fitsBits 63 := by decide
example : ¬ (0x8000000000000000 : UInt64).fitsBits 63 := by decide

/-! ## `lsbAsBool` and `packBoolLsb` -/

example : (0 : UInt8).lsbAsBool = false := by decide
example : (1 : UInt8).lsbAsBool = true := by decide
example : (0xFE : UInt8).lsbAsBool = false := by decide
example : (0xFF : UInt8).lsbAsBool = true := by decide
example : UInt8.packBoolLsb 0x7F true = 0xFF := by decide
example : UInt8.packBoolLsb 0x7F false = 0xFE := by decide
example : UInt8.packBoolLsb 0xFF true = 0xFF := by decide
example : UInt32.packBoolLsb 0x12345678 true = 0x2468ACF1 := by decide
example : UInt64.packBoolLsb 0x7FFFFFFFFFFFFFFF false = 0xFFFFFFFFFFFFFFFE := by decide

/-! ## Agreement with `BitVec.extractLsb'` -/

#guard (List.range 256).all fun v =>
  (List.range 12).all fun start =>
    (List.range 12).all fun len =>
      (v.toUInt8.extractLsb' start len).toNat =
        ((v.toUInt8.toBitVec.extractLsb' start len).setWidth 8).toNat

#guard (List.range 256).all fun v =>
  (List.range 12).all fun start =>
    (List.range 12).all fun len =>
      ((v * 0x01010101).toUInt32.extractLsb' start len).toNat =
        (((v * 0x01010101).toUInt32.toBitVec.extractLsb' start len).setWidth 32).toNat

/-! ## The lemma base through the automation the generated proofs use -/

-- Extracting what was inserted, for a fitting payload.
example (base v : UInt32) (h : v.fitsBits 4) :
    (base.insertSlice 4 8 v).extractSlice 4 8 = v := by
  simp_all +decide [transmog_norm]

-- A disjoint insert is invisible to extract.
example (base v : UInt32) :
    (base.insertSlice 8 16 v).extractSlice 0 8 = base.extractSlice 0 8 := by
  simp +decide [transmog_norm]

-- An extracted slice fits its width, and the keyed rung of `transmog_subtype` sees it.
example (x : UInt16) : (x.extractSlice 3 7).fitsBits 4 := by
  simp_all +decide [transmog_norm]

example (x : UInt16) : (x.extractSlice 3 7).fitsBits 4 := by transmog_subtype

-- A bool packed beside a payload reads back on both sides.
example (p : { x : UInt32 // x.fitsBits 31 }) (b : Bool) :
    (UInt32.packBoolLsb p.val b).lsbAsBool = b ∧ UInt32.packBoolLsb p.val b >>> 1 = p.val := by
  simp

-- The arithmetic reading is what `grind` consumes.
example (x : UInt8) (h : x.fitsBits 3) : x.toNat < 8 := by grind
example (x : UInt8) (h : x.toNat < 8) : x.fitsBits 3 := by grind
example (x : UInt8) (h : x.fitsBits 1) : x ≤ 2 := by grind
example (x : UInt32) (h : x.fitsBits 12) : x.fitsBits 16 := by grind

-- Beyond the scalar width every value fits.
example (x : UInt8) : x.fitsBits 8 := by simp
example (x : UInt8) : x.fitsBits 8 := by grind

/-! ## Axioms -/

-- The pure slice algebra needs no native computation.
/-- info: 'UInt32.extractSlice_insertSlice_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UInt32.extractSlice_insertSlice_self

/--
info: 'UInt32.extractSlice_insertSlice_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms UInt32.extractSlice_insertSlice_of_disjoint

/-- info: 'UInt32.fitsBits_iff_toNat_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UInt32.fitsBits_iff_toNat_lt

-- The bool packing lemmas are decided by `bv_decide`, once per `Bool` case, hence by native
-- computation.
/--
info: 'UInt8.lsbAsBool_packBoolLsb' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.Transmog.DSL.Core.UInt.0.UInt8.lsbAsBool_packBoolLsb._native.bv_decide.ax_1_10,
 _private.Transmog.DSL.Core.UInt.0.UInt8.lsbAsBool_packBoolLsb._native.bv_decide.ax_1_5]
-/
#guard_msgs in
#print axioms UInt8.lsbAsBool_packBoolLsb

/--
info: 'UInt32.shiftRight_packBoolLsb_subtype' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.Transmog.DSL.Core.UInt.0.UInt32.shiftRight_packBoolLsb_subtype._native.bv_decide.ax_1_10,
 _private.Transmog.DSL.Core.UInt.0.UInt32.shiftRight_packBoolLsb_subtype._native.bv_decide.ax_1_5]
-/
#guard_msgs in
#print axioms UInt32.shiftRight_packBoolLsb_subtype

end Transmog.Test.UInt
