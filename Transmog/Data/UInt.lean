/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Transmog.Init
public import Init.Data.UInt.Bitwise

/-!
# Extra `UInt` APIs

Bit-extraction helpers for the fixed-width unsigned integers, mirroring `BitVec.extractLsb'`.
-/

public section

set_option hygiene false in
local macro "declare_uint_extract" typeName:ident bits:num : command => `(
namespace $typeName

/-- The mask whose lowest `len` bits are set, clipped to the scalar width. -/
@[inline, expose] def lowMask (len : Nat) : $typeName :=
  if len < $bits then ((1 : $typeName) <<< ofNat len) - 1 else -1

@[simp] theorem lowMask_of_lt (h : len < $bits) :
    lowMask len = ((1 : $typeName) <<< ofNat len) - 1 := by
  simp [lowMask, h]

@[simp] theorem lowMask_of_ge (h : $bits ≤ len) : lowMask len = (-1 : $typeName) := by
  simp [lowMask, Nat.not_lt.mpr h]

/--
Extracts `len` bits starting at `start`, with zeroes beyond the scalar width.
The result is represented in the original scalar type.
-/
@[inline, expose] def extractLsb' (start len : Nat) (x : $typeName) : $typeName :=
  if start < $bits then (x >>> ofNat start) &&& lowMask len else 0

theorem extractLsb'_of_start_lt (h : start < $bits) :
    extractLsb' start len x = (x >>> ofNat start) &&& lowMask len := by
  simp [extractLsb', h]

@[simp] theorem extractLsb'_of_start_ge (h : $bits ≤ start) :
    extractLsb' start len x = 0 := by
  simp [extractLsb', Nat.not_lt.mpr h]

end $typeName)

declare_uint_extract UInt8 8
declare_uint_extract UInt16 16
declare_uint_extract UInt32 32
declare_uint_extract UInt64 64

end -- public section
