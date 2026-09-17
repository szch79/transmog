/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL.Core.Cast
meta import Transmog.DSL.Core.Cast

/-!
# Tests for the lawful casts

The base `DataCast` instances between scalars, the reflexive-transitive `DataCastT` closure,
its product and `DataRepr` cases, and the instances that must not be found.
-/

namespace Transmog.Test.DataCast

open Transmog

/-! ## Base casts between scalars -/

-- Widening between unsigned scalars.
example : DataCast.castTo (β := UInt16) (0xAB : UInt8) = 0xAB := by decide
example : DataCast.castFrom (α := UInt8) (0xABCD : UInt16) = 0xCD := by decide
example : DataCast.castTo (β := UInt64) (0xDEADBEEF : UInt32) = 0xDEADBEEF := by decide
example : DataCast.castTo (β := Int64) (-5 : Int16) = -5 := by decide
example : DataCast.castFrom (α := Int16) (-5 : Int64) = -5 := by decide

-- Reinterpretation between the signed and unsigned scalars of one width.
example : DataCast.castTo (β := Int8) (0xFF : UInt8) = -1 := by decide
example : DataCast.castFrom (α := UInt8) (-1 : Int8) = 0xFF := by decide
example : DataCast.castTo (β := UInt32) (-1 : Int32) = 0xFFFFFFFF := by decide
example : DataCast.castTo (β := Int64) (0x8000000000000000 : UInt64) = -9223372036854775808 := by
  decide

-- The word-sized pair, which the kernel cannot compute.
#guard DataCast.castTo (β := ISize) (5 : USize) == 5
#guard DataCast.castFrom (α := USize) (-1 : ISize) == USize.ofNat (USize.size - 1)
#guard DataCast.castTo (β := USize) (-1 : ISize) == USize.ofNat (USize.size - 1)

-- Every base cast is lawful.
example (x : UInt8) : DataCast.castFrom (β := UInt16) (DataCast.castTo x) = x :=
  DataCast.from_to x
example (x : Int32) : DataCast.castFrom (β := UInt32) (DataCast.castTo x) = x := by
  simp [transmog_norm]

/-! ## The reflexive-transitive closure -/

example : DataCastT UInt8 UInt8 := inferInstance
example : DataCastT UInt8 UInt16 := inferInstance
example : DataCastT UInt8 UInt64 := inferInstance
example : DataCastT UInt8 Int64 := inferInstance
example : DataCastT Int8 UInt64 := inferInstance
example : DataCastT (UInt8 × Int8) (UInt16 × UInt64) := inferInstance

-- Identity.
example : DataCastT.castTo (β := UInt32) (5 : UInt32) = 5 := rfl
example : DataCastT.castFrom (α := UInt32) (5 : UInt32) = 5 := rfl

-- Two hops, widening then reinterpreting.
example : DataCastT.castTo (β := Int64) (0xAB : UInt8) = 0xAB := by decide
example : DataCastT.castFrom (α := UInt8) (-1 : Int64) = 0xFF := by decide
-- The closure reinterprets before it widens, so a negative `Int8` zero-extends.
example : DataCastT.castTo (β := UInt64) (-1 : Int8) = 0xFF := by decide

-- Products convert factor-wise.
example : DataCastT.castTo (β := UInt16 × Int8) ((1, 0xFF) : UInt8 × UInt8) = (1, -1) := by decide
example : DataCastT.castFrom (α := UInt8 × UInt8) ((0x0102, -1) : UInt16 × Int8) = (2, 0xFF) := by
  decide

example (x : UInt8) : DataCastT.castFrom (β := Int64) (DataCastT.castTo x) = x :=
  DataCastT.from_to x
example (x : UInt8 × Int8) : DataCastT.castFrom (β := UInt16 × UInt64) (DataCastT.castTo x) = x := by
  simp [transmog_norm]

/-! ## Through a representation -/

@[expose] public section

/-- A byte behind a constructor. -/
structure Byte where
  v : UInt8
deriving DecidableEq

instance : DataRepr Byte UInt8 := ⟨Byte.v, Byte.mk, fun _ => rfl⟩

end

example : DataCastT Byte UInt8 := inferInstance
example : DataCastT Byte UInt16 := inferInstance
example : DataCastT.castTo (β := UInt8) (⟨7⟩ : Byte) = 7 := rfl
example : DataCastT.castFrom (α := Byte) (7 : UInt8) = ⟨7⟩ := rfl
-- The representation carrier composes with a base cast.
example : DataCastT.castTo (β := UInt16) (⟨7⟩ : Byte) = 7 := by decide
example : DataCastT.castFrom (α := Byte) (0x0107 : UInt16) = ⟨7⟩ := by decide
example (x : Byte) : DataCastT.castFrom (β := UInt16) (DataCastT.castTo x) = x := by
  simp [transmog_norm]

/-! ## Errors -/

-- No narrowing between scalars.
/--
error: failed to synthesize instance of type class
  DataCastT UInt32 UInt8

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : DataCastT UInt32 UInt8 := inferInstance

-- No base cast of a scalar to itself; only the closure is reflexive.
/--
error: failed to synthesize instance of type class
  DataCast UInt8 UInt8

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : DataCast UInt8 UInt8 := inferInstance

-- No cast out of a representation carrier back into the type.
/--
error: failed to synthesize instance of type class
  DataCastT UInt8 Byte

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : DataCastT UInt8 Byte := inferInstance

end Transmog.Test.DataCast
