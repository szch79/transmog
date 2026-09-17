/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL.Core.Basic

/-!
# Data casting

`DataCast` is an internal class for generating `DataRepr` definitions.  When the assignment
value type and the target type don't match, a `DataCast` will be inserted.  There are two ways
of casting a data:
- if their bit representations are compatible (e.g., `UInt8` can be casted to `UInt16`);
- if there exists a `DataRepr` instance.

`DataCast` is very similar to `DataRepr`, except that:
- semantically, `DataRepr` chooses the canonical representation, while `DataCast` is about all
possible lawful conversions;
- pragmatically, `DataCast` admits transitive closure and more default cases for basic types,
whereas `DataRepr` doesn't.
-/

public section

namespace Transmog

/-- `DataCast α β` is for lawful casting in Transmog declarations. -/
class DataCast (α : semiOutParam (Type u)) (β : Type v) where
  castTo : α → β
  castFrom : β → α
  from_to : ∀ x : α, castFrom (castTo x) = x

/-- Reflexive-transitive closure. -/
class DataCastT (α : Type u) (β : Type v) where
  castTo   : α → β
  castFrom : β → α
  from_to  : ∀ x, castFrom (castTo x) = x

attribute [transmog_norm] DataCast.from_to
attribute [transmog_norm] DataCastT.from_to
attribute [transmog_norm] DataRepr.from_to
attribute [transmog_norm] Subtype.eta
attribute [transmog_norm] Prod.eta

/-!
## Base cases

A type is allowed to be casted to itself, if the user writes so.  Also, types with `DataRepr`
(which is basically a stricter form of `DataCast` that picks a canonical instance,  since its
target type is `outParam`) are lawfully castable.
-/

instance (priority := low) : DataCastT α α := ⟨id, id, fun _ => rfl⟩

instance (priority := low) [DataCast β γ] [DataCastT α β] : DataCastT α γ where
  castTo x := DataCast.castTo (α := β) (DataCastT.castTo x)
  castFrom x := DataCastT.castFrom (β := β) (DataCast.castFrom x)
  from_to x := by rw [DataCast.from_to, DataCastT.from_to]

instance [DataRepr α ρ] : DataCastT α ρ :=
  ⟨DataRepr.toRepr, DataRepr.fromRepr, DataRepr.from_to⟩

instance [DataCastT α β] [DataCastT γ δ] : DataCastT (α × γ) (β × δ) where
  castTo x := (DataCastT.castTo x.1, DataCastT.castTo x.2)
  castFrom x := (DataCastT.castFrom x.1, DataCastT.castFrom x.2)
  from_to x := by cases x; simp [DataCastT.from_to]

/-!
## Casts for integer scalars

There are two kinds of cast instances for integer scalar types:
- converting between same-size unsigned/signed types, e.g., between `UInt8` and `Int8`;
- converting between compatible sized, same sign types, e.g., from `UInt8` to `UInt16`.

The rest can be inferred by transitivity.
-/

open Lean in
set_option hygiene false in
local macro "declare_bit_compatible_casts" ty:ident bits:num : command => do
  let typeId := ty.getId
  let .some typeBits := bits.raw.isNatLit?
    | Macro.throwErrorAt bits "invalid bit width"
  let typeString := typeId.getString!
  let isSigned := !typeString.startsWith "U"
  let mut cmds := #[]
  for (targetName, targetString, targetBits) in
      #[(`UInt8, "UInt8", 8), (`UInt16, "UInt16", 16),
        (`UInt32, "UInt32", 32), (`UInt64, "UInt64", 64),
        (`Int8, "Int8", 8), (`Int16, "Int16", 16),
        (`Int32, "Int32", 32), (`Int64, "Int64", 64)] do
    let targetSigned := !targetString.startsWith "U"
    -- We generate instances for two cases: 1. same size, but unsigned vs. signed; 2. same
    -- sign but size compatible.
    let emit :=
      if isSigned == targetSigned then typeBits < targetBits
      else typeBits == targetBits
    if emit then
      let target := mkCIdent targetName
      let widen := mkCIdent (typeId ++ Name.mkSimple s!"to{targetString}")
      let narrow := mkCIdent (targetName ++ Name.mkSimple s!"to{typeString}")
      cmds := cmds.push <| ←
        `(instance : DataCast $ty:ident $target:ident :=
            ⟨$widen:ident, $narrow:ident, by intro x; simp⟩)
  return ⟨mkNullNode cmds⟩

declare_bit_compatible_casts UInt8 8
declare_bit_compatible_casts UInt16 16
declare_bit_compatible_casts UInt32 32
declare_bit_compatible_casts UInt64 64
declare_bit_compatible_casts Int8 8
declare_bit_compatible_casts Int16 16
declare_bit_compatible_casts Int32 32
declare_bit_compatible_casts Int64 64

instance : DataCast USize ISize := ⟨USize.toISize, ISize.toUSize, by intro x; simp⟩
instance : DataCast ISize USize := ⟨ISize.toUSize, USize.toISize, by intro x; simp⟩

end Transmog

end -- public section
