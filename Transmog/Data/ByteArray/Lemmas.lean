/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import Transmog.Data.ByteArray.Basic
import all Init.Data.ByteArray.Extra
import Init.Data.ByteArray.Lemmas
import Init.Data.UInt.Bitwise
import Std.Tactic.BVDecide

/-!
# Fixed-width byte-array laws

Size, indexing, serialization, and locality laws for scalar byte operations.
-/

-- The upstream decoder has no exposed body or characterization theorem.
set_option linter.hazel.header.noImportAll false

public section

private theorem getElem?_getD_zero_eq_getElem! (bs : ByteArray) (i : Nat) :
    bs[i]?.getD 0 = bs[i]! := by
  rw [getElem!_def]
  cases bs[i]? <;> rfl


open Lean Macro in
set_option hygiene false in
/--
Generate lemmas such as
```lean
theorem UInt16.byte0 (v : UInt16) : v.byte 0 = v.toUInt8 := rfl
theorem UInt16.byte1 (v : UInt16) : v.byte 1 = (v >>> 8).toUInt8 := rfl
```
for the `byte` accessor of unsigned integer types other than `UInt8`.
-/
local macro "declare_uint_byte_lemmas" typeName:ident width:num : command => do
  let some widthNat := width.raw.isNatLit? | Macro.throwErrorAt width "expected byte width"
  let mut cmds := #[]
  for i in [0:widthNat] do
    let thm := mkIdentFrom typeName (.str typeName.getId s!"byte{i}")
    let iStx := ⟨Syntax.mkNatLit i⟩
    if i == 0 then
      cmds := cmds.push <| ← `(
        @[simp] theorem $thm (v : $typeName) : v.byte $iStx = v.toUInt8 := rfl)
    else
      let shiftStx : TSyntax `num := ⟨Syntax.mkNatLit (i * 8)⟩
      cmds := cmds.push <| ← `(
        @[simp] theorem $thm (v : $typeName) : v.byte $iStx = (v >>> $shiftStx).toUInt8 := rfl)
  return ⟨mkNullNode cmds⟩

declare_uint_byte_lemmas UInt16 2
declare_uint_byte_lemmas UInt32 4
declare_uint_byte_lemmas UInt64 8

namespace ByteArray

/-- Extracting a window wholly in the left operand does not depend on the right operand. -/
theorem extract_append_of_le {a b : ByteArray} (h : stop ≤ a.size) :
    (a ++ b).extract start stop = a.extract start stop := by
  have hz : b.extract (start - a.size) (stop - a.size) = empty := by
    simp only [extract_eq_empty_iff]
    omega
  simp [extract_append, hz]

/-- Extracting a window after the left operand reads from the right operand. -/
theorem extract_append_of_ge {a b : ByteArray} (h : a.size ≤ start) :
    (a ++ b).extract start stop = b.extract (start - a.size) (stop - a.size) := by
  have hz : a.extract start stop = empty := by
    simp only [extract_eq_empty_iff]
    omega
  simp [extract_append, hz]

/-! ## `setBytesUnchecked!` / `pushBytes` helper lemmas -/

@[simp, grind =]
private theorem size_setBytesUnchecked! (bs : ByteArray) (i n : Nat) (byte : Nat → UInt8) :
    (bs.setBytesUnchecked! i n byte).size = bs.size := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [setBytesUnchecked!, size_set!, ih]

@[grind =]
private theorem getElem!_setBytesUnchecked! (bs : ByteArray) (i n : Nat) (byte : Nat → UInt8)
    (j : Nat) (h : i + n ≤ bs.size) :
    (bs.setBytesUnchecked! i n byte)[j]! =
      if i ≤ j ∧ j < i + n then byte (j - i)
      else bs[j]! := by
  induction n with
  | zero =>
    grind [setBytesUnchecked!]
  | succ n ih =>
    have hprev : i + n ≤ bs.size := by omega
    have hlast : i + n < (bs.setBytesUnchecked! i n byte).size := by
      rw [size_setBytesUnchecked!]
      omega
    rw [setBytesUnchecked!, getElem!_set! _ _ _ _ hlast]
    grind

@[grind =]
private theorem getElem_setBytesUnchecked! (bs : ByteArray) (i n : Nat) (byte : Nat → UInt8)
    (j : Nat) (h : i + n ≤ bs.size) (hj : j < bs.size) :
    (bs.setBytesUnchecked! i n byte)[j]'(by rwa [size_setBytesUnchecked!]) =
      if i ≤ j ∧ j < i + n then byte (j - i)
      else bs[j] := by
  have h' := getElem!_setBytesUnchecked! bs i n byte j h
  rw [getElem!_pos (bs.setBytesUnchecked! i n byte) j (by
    rwa [size_setBytesUnchecked!])] at h'
  by_cases hin : i ≤ j ∧ j < i + n
  · simpa [hin] using h'
  · rw [getElem!_pos bs j hj] at h'
    simpa [hin] using h'

@[simp, grind =]
private theorem size_pushBytes (bs : ByteArray) (n : Nat) (byte : Nat → UInt8) :
    (bs.pushBytes n byte).size = bs.size + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pushBytes, size_push, ih]
    omega

@[grind =]
private theorem getElem!_pushBytes (bs : ByteArray) (n : Nat) (byte : Nat → UInt8)
    (j : Nat) :
    (bs.pushBytes n byte)[j]! =
      if bs.size ≤ j ∧ j < bs.size + n then byte (j - bs.size)
      else bs[j]! := by
  induction n with
  | zero =>
    grind [pushBytes]
  | succ n ih =>
    rw [pushBytes, getElem!_push, size_pushBytes]
    rw [ih]
    grind

@[grind =]
private theorem getElem_pushBytes (bs : ByteArray) (n : Nat) (byte : Nat → UInt8)
    (j : Nat) (hj : j < (bs.pushBytes n byte).size) :
    (bs.pushBytes n byte)[j] =
      if h : j < bs.size then bs[j]'h else byte (j - bs.size) := by
  have h' := getElem!_pushBytes bs n byte j
  rw [getElem!_pos (bs.pushBytes n byte) j hj] at h'
  by_cases hjold : j < bs.size
  · rw [getElem!_pos bs j hjold] at h'
    have hnot : ¬(bs.size ≤ j ∧ j < bs.size + n) := by omega
    simpa [hjold, hnot] using h'
  · have hrange : bs.size ≤ j ∧ j < bs.size + n := by
      rw [size_pushBytes] at hj
      omega
    simpa [hjold, hrange] using h'

end ByteArray

/-!
## Little-endian byte recompositions

`bv_decide` facts recombining the `byte` views of a scalar, in both the `byte` spelling and the
`% 256`-normalized spelling that `simp` produces.  Deliberately not `@[simp]`: their left-hand
sides are generic bitwise patterns on the core `UIntN` types, so a default-set registration
would leak specialized rewrites into every downstream `simp` call.  The `ofLEBytes_toLEBytes`
proofs below name them explicitly.
-/

namespace UInt16

private theorem of_le_bytes (v : UInt16) :
    (v.byte 0).toUInt16 ||| ((v.byte 1).toUInt16 <<< 8) = v := by
  simp [UInt16.byte]
  bv_decide

private theorem of_le_bytes_raw (v : UInt16) :
    v % (256 : UInt16) ||| (v >>> 8 % (256 : UInt16)) <<< 8 = v := by
  simpa [byte] using v.of_le_bytes

end UInt16

namespace UInt32

private theorem of_le_bytes (v : UInt32) :
    (v.byte 0).toUInt32 ||| ((v.byte 1).toUInt32 <<< 8) |||
      ((v.byte 2).toUInt32 <<< 16) ||| ((v.byte 3).toUInt32 <<< 24) = v := by
  simp [UInt32.byte]
  bv_decide

private theorem of_le_bytes_raw (v : UInt32) :
    v % (256 : UInt32) ||| (v >>> 8 % (256 : UInt32)) <<< 8 |||
      (v >>> 16 % (256 : UInt32)) <<< 16 ||| (v >>> 24 % (256 : UInt32)) <<< 24 = v := by
  simpa [byte] using v.of_le_bytes

end UInt32

namespace UInt64

private theorem of_le_bytes (v : UInt64) :
    (v.byte 0).toUInt64 ||| ((v.byte 1).toUInt64 <<< 8) |||
      ((v.byte 2).toUInt64 <<< 16) ||| ((v.byte 3).toUInt64 <<< 24) |||
      ((v.byte 4).toUInt64 <<< 32) ||| ((v.byte 5).toUInt64 <<< 40) |||
      ((v.byte 6).toUInt64 <<< 48) ||| ((v.byte 7).toUInt64 <<< 56) = v := by
  simp [UInt64.byte]
  bv_decide

private theorem of_le_bytes_raw (v : UInt64) :
    v % (256 : UInt64) ||| (v >>> 8 % (256 : UInt64)) <<< 8 |||
      (v >>> 16 % (256 : UInt64)) <<< 16 ||| (v >>> 24 % (256 : UInt64)) <<< 24 |||
      (v >>> 32 % (256 : UInt64)) <<< 32 ||| (v >>> 40 % (256 : UInt64)) <<< 40 |||
      (v >>> 48 % (256 : UInt64)) <<< 48 ||| (v >>> 56 % (256 : UInt64)) <<< 56 = v := by
  simpa [byte] using v.of_le_bytes

end UInt64

namespace ByteArray

variable {bs : ByteArray}

/-! ## Scalar getter normalization -/

@[simp] theorem get16!_eq_get16 (h : i < bs.size - 1) :
    bs.get16! i = bs.get16 i h := by
  simp only [get16!, get16, dite_eq_left h]

@[simp] theorem uget16_eq_get16 (h : i.toNat < bs.size - 1) :
    bs.uget16 i h = bs.get16 i.toNat h := rfl

@[simp] theorem get32!_eq_get32 (h : i < bs.size - 3) :
    bs.get32! i = bs.get32 i h := by
  simp only [get32!, get32, dite_eq_left h]

@[simp] theorem uget32_eq_get32 (h : i.toNat < bs.size - 3) :
    bs.uget32 i h = bs.get32 i.toNat h := rfl

@[simp] theorem get64!_eq_get64 (h : i < bs.size - 7) :
    bs.get64! i = bs.get64 i h := by
  simp only [get64!, get64, dite_eq_left h]

@[simp] theorem uget64_eq_get64 (h : i.toNat < bs.size - 7) :
    bs.uget64 i h = bs.get64 i.toNat h := rfl

/-! ## Size preservation of the fast writes -/

@[simp, grind =]
theorem size_set (bs : ByteArray) (i : Nat) (v : UInt8) (h : i < bs.size) :
    (bs.set i v h).size = bs.size :=
  Array.size_set ..

@[simp, grind =]
theorem size_set16 (bs : ByteArray) (i : Nat) (v : UInt16) (h : i < bs.size - 1) :
    (bs.set16 i v h).size = bs.size :=
  size_setBytesUnchecked! bs i 2 v.byte

@[simp, grind =]
theorem size_set32 (bs : ByteArray) (i : Nat) (v : UInt32) (h : i < bs.size - 3) :
    (bs.set32 i v h).size = bs.size :=
  size_setBytesUnchecked! bs i 4 v.byte

@[simp, grind =]
theorem size_set64 (bs : ByteArray) (i : Nat) (v : UInt64) (h : i < bs.size - 7) :
    (bs.set64 i v h).size = bs.size :=
  size_setBytesUnchecked! bs i 8 v.byte

/-!
## Splice normal forms for the fast operations

Each fast write is a `copySlice`-style splice in disguise, and each fast read deserializes an
extracted window.  The `_eq_append` and `_eq_ofLEBytes_extract` lemmas below put them in the
extract/append normal form that `Transmog.Layout` uses for its refinement equations.
-/

theorem getElem!_extract (bs : ByteArray) (start stop j : Nat)
    (h : j < min stop bs.size - start) :
    (bs.extract start stop)[j]! = bs[start + j]! := by
  rw [getElem!_pos _ j (by simp only [size_extract]; omega),
    getElem_extract, getElem!_pos bs (start + j) (by omega)]

theorem setBytesUnchecked!_eq_append (bs : ByteArray) (i n : Nat) (byte : Nat → UInt8)
    (h : i + n ≤ bs.size) :
    bs.setBytesUnchecked! i n byte =
      bs.extract 0 i ++ ByteArray.empty.pushBytes n byte ++ bs.extract (i + n) bs.size := by
  apply ext_getElem
  · simp only [size_setBytesUnchecked!, size_append, size_extract, size_pushBytes, size_empty]
    omega
  · intro j hj hj'
    have hjs : j < bs.size := by rwa [size_setBytesUnchecked!] at hj
    rw [getElem_setBytesUnchecked! bs i n byte j h hjs]
    by_cases hji : j < i
    · rw [ite_eq_right (by omega),
        getElem_append_left (by
          simp only [size_append, size_extract, size_pushBytes, size_empty]
          omega),
        getElem_append_left (by simp only [size_extract]; omega),
        getElem_extract]
      congr 1
      omega
    · by_cases hjin : j < i + n
      · rw [ite_eq_left ⟨by omega, hjin⟩,
          getElem_append_left (by
            simp only [size_append, size_extract, size_pushBytes, size_empty]
            omega),
          getElem_append_right (by simp only [size_extract]; omega),
          getElem_pushBytes]
        rw [dite_eq_right (by simp)]
        simp only [size_extract, size_empty]
        congr 1
        omega
      · rw [ite_eq_right (by omega),
          getElem_append_right (by
            simp only [size_append, size_extract, size_pushBytes, size_empty]
            omega),
          getElem_extract]
        congr 1
        simp only [size_append, size_extract, size_pushBytes, size_empty]
        omega

/-! ## `replicate` and `setZeros` -/

private theorem replicate_eq_pushBytes (n : Nat) (v : UInt8) :
    replicate n v = ByteArray.empty.pushBytes n fun _ => v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pushBytes, ← ih]
    exact congrArg ByteArray.mk Array.replicate_succ

@[simp, grind =]
theorem size_replicate (n : Nat) (v : UInt8) : (replicate n v).size = n :=
  Array.size_replicate

theorem getElem!_replicate (n : Nat) (v : UInt8) (i : Nat) (h : i < n) :
    (replicate n v)[i]! = v := by
  rw [replicate_eq_pushBytes, getElem!_pushBytes]
  simp [h]

@[simp, grind =]
theorem getElem_replicate (h : i < (replicate n v).size) :
    (replicate n v)[i] = v :=
  Array.getElem_replicate ..

@[simp]
theorem replicate_zero (v : UInt8) : replicate 0 v = ByteArray.empty := rfl

@[simp, grind =]
theorem size_setZeros (bs : ByteArray) (i n : Nat) :
    (bs.setZeros i n).size = bs.size := by
  simp [setZeros]

@[simp]
theorem setZeros_zero (bs : ByteArray) (i : Nat) : bs.setZeros i 0 = bs := rfl

theorem setZeros_eq_append (bs : ByteArray) (i n : Nat) (h : i + n ≤ bs.size) :
    bs.setZeros i n = bs.extract 0 i ++ replicate n 0 ++ bs.extract (i + n) bs.size := by
  rw [replicate_eq_pushBytes]
  exact setBytesUnchecked!_eq_append bs i n (fun _ => 0) h

/-! ## Writes as splices -/

theorem set_eq_append (bs : ByteArray) (i : Nat) (v : UInt8) (h : i < bs.size) :
    bs.set i v h = bs.extract 0 i ++ v.toLEBytes ++ bs.extract (i + 1) bs.size := by
  rw [set_eq_push_extract_append_extract h, ← append_toByteArray_singleton]
  rfl

theorem set16_eq_append (bs : ByteArray) (i : Nat) (v : UInt16) (h : i < bs.size - 1) :
    bs.set16 i v h = bs.extract 0 i ++ v.toLEBytes ++ bs.extract (i + 2) bs.size :=
  setBytesUnchecked!_eq_append bs i 2 v.byte (by omega)

theorem set32_eq_append (bs : ByteArray) (i : Nat) (v : UInt32) (h : i < bs.size - 3) :
    bs.set32 i v h = bs.extract 0 i ++ v.toLEBytes ++ bs.extract (i + 4) bs.size :=
  setBytesUnchecked!_eq_append bs i 4 v.byte (by omega)

theorem set64_eq_append (bs : ByteArray) (i : Nat) (v : UInt64) (h : i < bs.size - 7) :
    bs.set64 i v h = bs.extract 0 i ++ v.toLEBytes ++ bs.extract (i + 8) bs.size :=
  setBytesUnchecked!_eq_append bs i 8 v.byte (by omega)

/-! ## Reads as deserialized windows -/

theorem get16_eq_bytes (bs : ByteArray) (i : Nat) (h : i + 2 ≤ bs.size) :
    bs.get16 i (by omega) = bs[i]!.toUInt16 ||| bs[i + 1]!.toUInt16 <<< 8 := by
  rw [get16,
    getElem!_pos bs i (by omega), getElem!_pos bs (i + 1) (by omega)]

theorem get32_eq_bytes (bs : ByteArray) (i : Nat) (h : i + 4 ≤ bs.size) :
    bs.get32 i (by omega) = bs[i]!.toUInt32 ||| bs[i + 1]!.toUInt32 <<< 8 |||
      bs[i + 2]!.toUInt32 <<< 16 ||| bs[i + 3]!.toUInt32 <<< 24 := by
  rw [get32,
    getElem!_pos bs i (by omega), getElem!_pos bs (i + 1) (by omega),
    getElem!_pos bs (i + 2) (by omega), getElem!_pos bs (i + 3) (by omega)]

theorem get64_eq_bytes (bs : ByteArray) (i : Nat) (h : i + 8 ≤ bs.size) :
    bs.get64 i (by omega) = bs[i]!.toUInt64 ||| bs[i + 1]!.toUInt64 <<< 8 |||
      bs[i + 2]!.toUInt64 <<< 16 ||| bs[i + 3]!.toUInt64 <<< 24 |||
      bs[i + 4]!.toUInt64 <<< 32 ||| bs[i + 5]!.toUInt64 <<< 40 |||
      bs[i + 6]!.toUInt64 <<< 48 ||| bs[i + 7]!.toUInt64 <<< 56 := by
  rw [get64,
    getElem!_pos bs i (by omega), getElem!_pos bs (i + 1) (by omega),
    getElem!_pos bs (i + 2) (by omega), getElem!_pos bs (i + 3) (by omega),
    getElem!_pos bs (i + 4) (by omega), getElem!_pos bs (i + 5) (by omega),
    getElem!_pos bs (i + 6) (by omega), getElem!_pos bs (i + 7) (by omega)]

theorem getElem_eq_ofLEBytes_extract (bs : ByteArray) (i : Nat) (h : i < bs.size) :
    bs[i] = UInt8.ofLEBytes (bs.extract i (i + 1)) := by
  simp only [UInt8.ofLEBytes, getElem?_getD_zero_eq_getElem!]
  rw [getElem!_extract bs i (i + 1) 0 (by omega), Nat.add_zero,
    getElem!_pos bs i h]

theorem get16_eq_ofLEBytes_extract (bs : ByteArray) (i : Nat) (h : i < bs.size - 1) :
    bs.get16 i h = UInt16.ofLEBytes (bs.extract i (i + 2)) := by
  simp only [UInt16.ofLEBytes, getElem?_getD_zero_eq_getElem!]
  rw [get16_eq_bytes bs i (by omega),
    getElem!_extract bs i (i + 2) 0 (by omega), getElem!_extract bs i (i + 2) 1 (by omega)]
  simp only [Nat.add_zero]

theorem get32_eq_ofLEBytes_extract (bs : ByteArray) (i : Nat) (h : i < bs.size - 3) :
    bs.get32 i h = UInt32.ofLEBytes (bs.extract i (i + 4)) := by
  simp only [UInt32.ofLEBytes, getElem?_getD_zero_eq_getElem!]
  rw [get32_eq_bytes bs i (by omega),
    getElem!_extract bs i (i + 4) 0 (by omega), getElem!_extract bs i (i + 4) 1 (by omega),
    getElem!_extract bs i (i + 4) 2 (by omega), getElem!_extract bs i (i + 4) 3 (by omega)]
  simp only [Nat.add_zero]

theorem get64_eq_ofLEBytes_extract (bs : ByteArray) (i : Nat) (h : i < bs.size - 7) :
    bs.get64 i h = UInt64.ofLEBytes (bs.extract i (i + 8)) := by
  simp only [UInt64.ofLEBytes, getElem?_getD_zero_eq_getElem!]
  rw [get64_eq_bytes bs i (by omega),
    getElem!_extract bs i (i + 8) 0 (by omega), getElem!_extract bs i (i + 8) 1 (by omega),
    getElem!_extract bs i (i + 8) 2 (by omega), getElem!_extract bs i (i + 8) 3 (by omega),
    getElem!_extract bs i (i + 8) 4 (by omega), getElem!_extract bs i (i + 8) 5 (by omega),
    getElem!_extract bs i (i + 8) 6 (by omega), getElem!_extract bs i (i + 8) 7 (by omega)]
  simp only [Nat.add_zero]

end ByteArray

/-! ## Little-endian scalar codec lemmas -/

@[simp]
theorem UInt8.size_toLEBytes (v : UInt8) : v.toLEBytes.size = 1 := by
  simp [UInt8.toLEBytes]

@[simp]
theorem UInt16.size_toLEBytes (v : UInt16) : v.toLEBytes.size = 2 := by
  simp [UInt16.toLEBytes]

@[simp]
theorem UInt32.size_toLEBytes (v : UInt32) : v.toLEBytes.size = 4 := by
  simp [UInt32.toLEBytes]

@[simp]
theorem UInt64.size_toLEBytes (v : UInt64) : v.toLEBytes.size = 8 := by
  simp [UInt64.toLEBytes]

@[simp]
theorem UInt8.ofLEBytes_toLEBytes (v : UInt8) : UInt8.ofLEBytes v.toLEBytes = v := by
  simp only [UInt8.ofLEBytes, getElem?_getD_zero_eq_getElem!]
  rw [UInt8.toLEBytes, getElem!_pos _ 0 (by simp)]
  simp

@[simp]
theorem UInt16.ofLEBytes_toLEBytes (v : UInt16) : UInt16.ofLEBytes v.toLEBytes = v := by
  simp only [UInt16.ofLEBytes, getElem?_getD_zero_eq_getElem!]
  rw [UInt16.toLEBytes, ByteArray.getElem!_pushBytes,
    ByteArray.getElem!_pushBytes]
  simp [UInt16.of_le_bytes_raw]

@[simp]
theorem UInt32.ofLEBytes_toLEBytes (v : UInt32) : UInt32.ofLEBytes v.toLEBytes = v := by
  simp only [UInt32.ofLEBytes, getElem?_getD_zero_eq_getElem!]
  rw [UInt32.toLEBytes, ByteArray.getElem!_pushBytes,
    ByteArray.getElem!_pushBytes, ByteArray.getElem!_pushBytes, ByteArray.getElem!_pushBytes]
  simp [UInt32.of_le_bytes_raw]

@[simp]
theorem UInt64.ofLEBytes_toLEBytes (v : UInt64) : UInt64.ofLEBytes v.toLEBytes = v := by
  simp only [UInt64.ofLEBytes, getElem?_getD_zero_eq_getElem!]
  rw [UInt64.toLEBytes, ByteArray.getElem!_pushBytes,
    ByteArray.getElem!_pushBytes, ByteArray.getElem!_pushBytes, ByteArray.getElem!_pushBytes,
    ByteArray.getElem!_pushBytes, ByteArray.getElem!_pushBytes, ByteArray.getElem!_pushBytes,
    ByteArray.getElem!_pushBytes]
  simp [UInt64.of_le_bytes_raw]

/-- The total decoder agrees with the standard decoder on eight-byte inputs. -/
theorem UInt64.ofLEBytes_eq_toUInt64LE! (h : bs.size = 8) :
    UInt64.ofLEBytes (bs : ByteArray) = bs.toUInt64LE! := by
  simp [UInt64.ofLEBytes, ByteArray.toUInt64LE!, h, ByteArray.get!,
    ByteArray.getElem_eq_getElem_data, UInt64.or_assoc, UInt64.or_comm]

end -- public section
