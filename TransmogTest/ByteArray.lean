/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.Data.ByteArray
meta import Transmog.Data.ByteArray.Basic

/-!
# Tests for the little-endian scalar operations on `ByteArray`

Every fast operation has two implementations: the Lean model that the kernel reduces, and the
inline C or C++ that the compiled code and the interpreter run.  Each case below is checked on
both, by `decide` and by `#guard`, so the two implementations are held to the same contract.
-/

namespace Transmog.Test.ByteArray

/-! ## Little-endian bytes of a scalar -/

example : (0xABCD : UInt16).byte 0 = 0xCD := by decide
example : (0xABCD : UInt16).byte 1 = 0xAB := by decide
example : (0xABCD : UInt16).byte 2 = 0 := by decide
example : (0xABCD : UInt16).byte 100 = 0 := by decide
example : (0xDEADBEEF : UInt32).byte 3 = 0xDE := by decide
example : (0x0102030405060708 : UInt64).byte 7 = 0x01 := by decide
example : (0x0102030405060708 : UInt64).byte 8 = 0 := by decide

example : (0x7F : UInt8).toLEBytes.data = #[0x7F] := by decide
example : (0xABCD : UInt16).toLEBytes.data = #[0xCD, 0xAB] := by decide
example : (0xDEADBEEF : UInt32).toLEBytes.data = #[0xEF, 0xBE, 0xAD, 0xDE] := by decide
example : (0x0102030405060708 : UInt64).toLEBytes.data = #[8, 7, 6, 5, 4, 3, 2, 1] := by decide

example : UInt8.ofLEBytes ⟨#[0x7F, 0xFF]⟩ = 0x7F := by decide
example : UInt16.ofLEBytes ⟨#[0xCD, 0xAB, 0xFF]⟩ = 0xABCD := by decide
example : UInt32.ofLEBytes ⟨#[0xEF, 0xBE, 0xAD, 0xDE]⟩ = 0xDEADBEEF := by decide
example : UInt64.ofLEBytes ⟨#[8, 7, 6, 5, 4, 3, 2, 1]⟩ = 0x0102030405060708 := by decide

-- Missing bytes read as zero.
example : UInt16.ofLEBytes ⟨#[]⟩ = 0 := by decide
example : UInt32.ofLEBytes ⟨#[0x34, 0x12]⟩ = 0x1234 := by decide
example : UInt64.ofLEBytes ⟨#[0x34, 0x12]⟩ = 0x1234 := by decide
#guard UInt64.ofLEBytes ⟨#[0x34, 0x12]⟩ == 0x1234
#guard UInt16.ofLEBytes ByteArray.empty == 0

/-! ## Fills -/

example : (ByteArray.replicate 3 0xAA).data = #[0xAA, 0xAA, 0xAA] := by decide
example : (ByteArray.replicate 0 0xAA).data = #[] := by decide
example : ((ByteArray.replicate 5 0xFF).setZeros 1 3).data = #[0xFF, 0, 0, 0, 0xFF] := by decide
example : ((ByteArray.replicate 2 0xFF).setZeros 1 0).data = #[0xFF, 0xFF] := by decide
example : (ByteArray.empty.pushBytes 3 fun i => i.toUInt8 + 1).data = #[1, 2, 3] := by decide
example : ((⟨#[9, 9, 9, 9]⟩ : ByteArray).setBytes! 1 2 fun i => i.toUInt8).data =
    #[9, 0, 1, 9] := by decide
-- A write that does not fit leaves the array unchanged.
example : ((⟨#[9, 9, 9, 9]⟩ : ByteArray).setBytes! 3 2 fun i => i.toUInt8).data =
    #[9, 9, 9, 9] := by decide

/-! ## Reads -/

example : (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).get16! 1 = 0x0302 := by decide
example : (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).get32! 1 = 0x05040302 := by decide
example : (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).get64! 1 = 0x0908070605040302 := by decide
example : (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).get16 7 (by decide) = 0x0908 := by decide
example : (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).get32 5 (by decide) = 0x09080706 := by
  decide
example : (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).get64 0 (by decide) =
    0x0807060504030201 := by decide

#guard (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).get16! 1 == 0x0302
#guard (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).get32! 1 == 0x05040302
#guard (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).get64! 1 == 0x0908070605040302
#guard (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).get16 7 (by decide) == 0x0908
#guard (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).get32 5 (by decide) == 0x09080706
#guard (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).get64 0 (by decide) == 0x0807060504030201
-- The `USize` twins are the `Nat` operations by definition; a `USize` literal does not reduce
-- in the kernel, so they are checked on the compiled side only.
#guard (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).uget16 7 (by simp [ByteArray.size]) == 0x0908
#guard (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).uget32 5 (by simp [ByteArray.size]) ==
  0x09080706
#guard (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray).uget64 1 (by simp [ByteArray.size]) ==
  0x0908070605040302

-- A read that does not fit yields zero, on both implementations.
example : (⟨#[1, 2, 3]⟩ : ByteArray).get16! 2 = 0 := by decide
example : (⟨#[1, 2, 3]⟩ : ByteArray).get32! 0 = 0 := by decide
example : (⟨#[1, 2, 3]⟩ : ByteArray).get64! (2 ^ 128) = 0 := by decide
#guard (⟨#[1, 2, 3]⟩ : ByteArray).get16! 2 == 0
#guard (⟨#[1, 2, 3]⟩ : ByteArray).get32! 0 == 0
#guard (⟨#[1, 2, 3]⟩ : ByteArray).get64! 0 == 0
#guard (⟨#[1, 2, 3]⟩ : ByteArray).get64! (2 ^ 128) == 0

/-! ## Writes -/

example : ((⟨#[9, 9, 9, 9]⟩ : ByteArray).set16! 1 0xABCD).data = #[9, 0xCD, 0xAB, 9] := by
  decide
example : ((⟨#[9, 9, 9, 9, 9]⟩ : ByteArray).set32! 1 0xDEADBEEF).data =
    #[9, 0xEF, 0xBE, 0xAD, 0xDE] := by decide
example : ((⟨#[9, 9, 9, 9, 9, 9, 9, 9, 9]⟩ : ByteArray).set64! 1 0x0102030405060708).data =
    #[9, 8, 7, 6, 5, 4, 3, 2, 1] := by decide
example : ((⟨#[9, 9, 9, 9]⟩ : ByteArray).set16 2 0xABCD (by decide)).data =
    #[9, 9, 0xCD, 0xAB] := by decide
example : ((⟨#[9, 9, 9, 9]⟩ : ByteArray).set32 0 0xDEADBEEF (by decide)).data =
    #[0xEF, 0xBE, 0xAD, 0xDE] := by decide
example : ((⟨#[9, 9, 9, 9, 9, 9, 9, 9]⟩ : ByteArray).set64 0 0x0102030405060708 (by decide)).data
    = #[8, 7, 6, 5, 4, 3, 2, 1] := by decide

#guard ((⟨#[9, 9, 9, 9]⟩ : ByteArray).set16! 1 0xABCD).data == #[9, 0xCD, 0xAB, 9]
#guard ((⟨#[9, 9, 9, 9, 9]⟩ : ByteArray).set32! 1 0xDEADBEEF).data == #[9, 0xEF, 0xBE, 0xAD, 0xDE]
#guard ((⟨#[9, 9, 9, 9, 9, 9, 9, 9, 9]⟩ : ByteArray).set64! 1 0x0102030405060708).data ==
  #[9, 8, 7, 6, 5, 4, 3, 2, 1]
#guard ((⟨#[9, 9, 9, 9]⟩ : ByteArray).set16 2 0xABCD (by decide)).data == #[9, 9, 0xCD, 0xAB]
#guard ((⟨#[9, 9, 9, 9]⟩ : ByteArray).set32 0 0xDEADBEEF (by decide)).data ==
  #[0xEF, 0xBE, 0xAD, 0xDE]
#guard ((⟨#[9, 9, 9, 9, 9, 9, 9, 9]⟩ : ByteArray).set64 0 0x0102030405060708 (by decide)).data ==
  #[8, 7, 6, 5, 4, 3, 2, 1]
#guard ((⟨#[9, 9, 9, 9]⟩ : ByteArray).uset16 2 0xABCD (by simp [ByteArray.size])).data ==
  #[9, 9, 0xCD, 0xAB]
#guard ((⟨#[9, 9, 9, 9]⟩ : ByteArray).uset32 0 0xDEADBEEF (by simp [ByteArray.size])).data ==
  #[0xEF, 0xBE, 0xAD, 0xDE]
#guard ((⟨#[9, 9, 9, 9, 9, 9, 9, 9]⟩ : ByteArray).uset64 0 0x0102030405060708
  (by simp [ByteArray.size])).data == #[8, 7, 6, 5, 4, 3, 2, 1]

-- A write that does not fit leaves the array unchanged, on both implementations.
example : ((⟨#[9, 9, 9]⟩ : ByteArray).set16! 2 0xABCD).data = #[9, 9, 9] := by decide
example : ((⟨#[9, 9, 9]⟩ : ByteArray).set32! 0 0xDEADBEEF).data = #[9, 9, 9] := by decide
example : ((⟨#[9, 9, 9]⟩ : ByteArray).set64! (2 ^ 128) 99).data = #[9, 9, 9] := by decide
#guard ((⟨#[9, 9, 9]⟩ : ByteArray).set16! 2 0xABCD).data == #[9, 9, 9]
#guard ((⟨#[9, 9, 9]⟩ : ByteArray).set32! 0 0xDEADBEEF).data == #[9, 9, 9]
#guard ((⟨#[9, 9, 9]⟩ : ByteArray).set64! (2 ^ 128) 99).data == #[9, 9, 9]

-- The compiled write copies a shared array instead of mutating it in place.
#guard
  let bs : ByteArray := ⟨#[9, 9, 9, 9]⟩
  let bs' := bs.set16! 0 0xABCD
  bs.data == #[9, 9, 9, 9] && bs'.data == #[0xCD, 0xAB, 9, 9]

/-! ## Pushes -/

example : ((⟨#[1]⟩ : ByteArray).push16 0xABCD).data = #[1, 0xCD, 0xAB] := by decide
example : ((⟨#[1]⟩ : ByteArray).push32 0xDEADBEEF).data = #[1, 0xEF, 0xBE, 0xAD, 0xDE] := by
  decide
example : ((⟨#[1]⟩ : ByteArray).push64 0x0102030405060708).data =
    #[1, 8, 7, 6, 5, 4, 3, 2, 1] := by decide
#guard ((⟨#[1]⟩ : ByteArray).push16 0xABCD).data == #[1, 0xCD, 0xAB]
#guard ((⟨#[1]⟩ : ByteArray).push32 0xDEADBEEF).data == #[1, 0xEF, 0xBE, 0xAD, 0xDE]
#guard ((⟨#[1]⟩ : ByteArray).push64 0x0102030405060708).data == #[1, 8, 7, 6, 5, 4, 3, 2, 1]
#guard (ByteArray.empty.push16 0xABCD).data == #[0xCD, 0xAB]

/-! ## The compiled operations against the codecs, at every offset of a buffer -/

#guard_msgs in
#eval show IO Unit from do
  for seed in [1:30] do
    let bs := ByteArray.replicate 16 0xAA
    let v16 := (seed * 293).toUInt16
    let v32 := (seed * 153491817).toUInt32
    let v64 := (seed * 100000000733).toUInt64
    for i in [0:19] do
      let expected16 := if i + 2 ≤ bs.size then
        bs.extract 0 i ++ v16.toLEBytes ++ bs.extract (i + 2) bs.size else bs
      let expected32 := if i + 4 ≤ bs.size then
        bs.extract 0 i ++ v32.toLEBytes ++ bs.extract (i + 4) bs.size else bs
      let expected64 := if i + 8 ≤ bs.size then
        bs.extract 0 i ++ v64.toLEBytes ++ bs.extract (i + 8) bs.size else bs
      unless bs.set16! i v16 == expected16 do throw (IO.userError s!"set16! at {i}")
      unless bs.set32! i v32 == expected32 do throw (IO.userError s!"set32! at {i}")
      unless bs.set64! i v64 == expected64 do throw (IO.userError s!"set64! at {i}")
      if i + 2 ≤ bs.size then
        unless expected16.get16! i == v16 do throw (IO.userError s!"get16! at {i}")
      if i + 4 ≤ bs.size then
        unless expected32.get32! i == v32 do throw (IO.userError s!"get32! at {i}")
      if i + 8 ≤ bs.size then
        unless expected64.get64! i == v64 do throw (IO.userError s!"get64! at {i}")
    unless bs == ByteArray.replicate 16 0xAA do throw (IO.userError "copy on write")
    unless bs.push16 v16 == bs ++ v16.toLEBytes do throw (IO.userError "push16")
    unless bs.push32 v32 == bs ++ v32.toLEBytes do throw (IO.userError "push32")
    unless bs.push64 v64 == bs ++ v64.toLEBytes do throw (IO.userError "push64")

/-! ## The lemma base -/

example (bs : ByteArray) (v : UInt16) (h : i < bs.size - 1) :
    (bs.set16 i v h).size = bs.size := by simp
example (bs : ByteArray) (v : UInt32) (h : i < bs.size - 3) :
    (bs.set32 i v h).size = bs.size := by simp
example (bs : ByteArray) (v : UInt64) (h : i < bs.size - 7) :
    (bs.set64 i v h).size = bs.size := by grind
example (bs : ByteArray) (h : i < bs.size - 1) : bs.get16! i = bs.get16 i h := by simp [h]
example (bs : ByteArray) (i : USize) (h : i.toNat < bs.size - 3) :
    bs.uget32 i h = bs.get32 i.toNat h := by simp
example (h : i < n) : (ByteArray.replicate n 7)[i]'(by simpa using h) = 7 := by simp
example (bs : ByteArray) (i n : Nat) : (bs.setZeros i n).size = bs.size := by simp

example (v : UInt16) : UInt16.ofLEBytes v.toLEBytes = v := by simp
example (v : UInt64) : v.toLEBytes.size = 8 := by simp

/-! ## Axioms -/

-- The byte recompositions behind the codec round trips are decided by `bv_decide`.
/--
info: 'UInt16.ofLEBytes_toLEBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.Transmog.Data.ByteArray.Lemmas.0.UInt16.of_le_bytes._native.bv_decide.ax_1_9]
-/
#guard_msgs in
#print axioms UInt16.ofLEBytes_toLEBytes

/--
info: 'UInt32.ofLEBytes_toLEBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.Transmog.Data.ByteArray.Lemmas.0.UInt32.of_le_bytes._native.bv_decide.ax_1_11]
-/
#guard_msgs in
#print axioms UInt32.ofLEBytes_toLEBytes

/--
info: 'UInt64.ofLEBytes_toLEBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.Transmog.Data.ByteArray.Lemmas.0.UInt64.of_le_bytes._native.bv_decide.ax_1_15]
-/
#guard_msgs in
#print axioms UInt64.ofLEBytes_toLEBytes

-- The splice normal forms of the fast operations do not.
/-- info: 'ByteArray.set32_eq_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ByteArray.set32_eq_append

/-- info: 'ByteArray.get32_eq_ofLEBytes_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ByteArray.get32_eq_ofLEBytes_extract

end Transmog.Test.ByteArray
