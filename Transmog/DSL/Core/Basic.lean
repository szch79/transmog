/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Transmog.Init
public import Init.Data.ByteArray.Lemmas

/-! # Transmog type classes -/

public section

namespace Transmog

/-! ## Data representation API -/

/--
A data representation of type `α` using `ρ`.  That is, a value of type `α` can be converted to and
from a value of `ρ`, and the round-trip gives back the original `α` value.
-/
class DataRepr (α : Type u) (ρ : outParam (Type v)) where
  /-- Converts an `α` value to its representation in `ρ`. -/
  toRepr : α → ρ
  /-- Recover the `α` value from its representation in `ρ`. -/
  fromRepr : ρ → α
  /-- The representation is sound, and the round-trip gives back the original `α` value. -/
  from_to : ∀ x : α, fromRepr (toRepr x) = x

attribute [simp, grind =] DataRepr.from_to

instance : DataRepr UInt8 UInt8 := ⟨id, id, fun _ => rfl⟩
instance : DataRepr UInt16 UInt16 := ⟨id, id, fun _ => rfl⟩
instance : DataRepr UInt32 UInt32 := ⟨id, id, fun _ => rfl⟩
instance : DataRepr UInt64 UInt64 := ⟨id, id, fun _ => rfl⟩

/-!
## Layout API

A `Layout` is a fixed-size byte codec in spec/exec style:
- the *spec* is a materializing codec, `toBytes`/`fromBytes`, together with the size law and the
  round-trip law;
- the *exec* fields `store`/`load` operate in place on a `ByteArray`, tied to the spec by
  two refinement equations phrased in the extract/append normal form.

The exec fields have default values that simply run the spec, in which case the refinement
equations hold by `ByteArray.copySlice_eq_append`; a codec that overrides the exec fields with
faster primitives must prove its own refinement equations.  All byte-level locality reasoning
(storing does not touch bytes outside its window, loading only depends on its window, etc.)
is derived generically from the two refinement equations.
-/

/--
Splicing a `size`-byte array into `bs` at `off` with `copySlice` is appending in disguise.  This
backs the default value of `Layout.store_eq_append`.
-/
theorem copySlice_eq_append_of_size_eq (hsz : tb.size = size)
    (bs : ByteArray) (off : Nat) :
    tb.copySlice 0 bs off size = bs.extract 0 off ++ tb ++ bs.extract (off + size) bs.size := by
  subst hsz
  simp only [ByteArray.copySlice_eq_append, ByteArray.size_data, Nat.zero_add, Nat.sub_zero,
    Nat.min_self, ByteArray.extract_zero_size]

/--
A byte-level layout of `ρ` with alignment `2 ^ k`.  The spec fields `toBytes`/`fromBytes` define
serialization by materializing the bytes; the exec fields `store`/`load` act in place on a
`ByteArray` and agree with the spec by the refinement equations.
-/
structure Layout (ρ : Type u) (k : Nat) where
  /-- Byte size of the layout. -/
  size : Nat
  /-- The layout covers at least one byte. -/
  size_pos : 0 < size
  /-- `size` must be a multiple of the alignment `2 ^ k`. -/
  size_align : size % 2 ^ k = 0
  /-- Specification for the serialization. -/
  toBytes : ρ → ByteArray
  /-- Specification for the deserialization. -/
  fromBytes : ByteArray → ρ
  /-- Serialized byte result must agree with `size`. -/
  size_toBytes : ∀ x, (toBytes x).size = size
  /-- Serialize then deserialize round-trip gives the original value back. -/
  fromBytes_toBytes : ∀ x, fromBytes (toBytes x) = x
  /-- Store a `ρ` value into a byte array `bs` at `off`. -/
  store : (bs : ByteArray) → ρ → (off : Nat) → off + size ≤ bs.size → ByteArray :=
    fun bs x off _ => (toBytes x).copySlice 0 bs off size
  /-- Load a `ρ` value from a byte array `bs` at `off`. -/
  load : (bs : ByteArray) → (off : Nat) → off + size ≤ bs.size → ρ :=
    fun bs off _ => fromBytes (bs.extract off (off + size))
  /--
  `store` with a platform-specific fixed-width offset; a codec may override it with a
  genuinely `USize`-arithmetic fast path (via `implemented_by`, since `bs.size < USize.size` is
  a runtime fact, not a theorem).
  -/
  ustore : (bs : ByteArray) → ρ → (off : USize) → off.toNat + size ≤ bs.size → ByteArray :=
    fun bs x off h => store bs x off.toNat h
  /--
  `load` with a platform-specific fixed-width offset; a codec may override it with a
  genuinely `USize`-arithmetic fast path (via `implemented_by`, since `bs.size < USize.size` is
  a runtime fact, not a theorem).
  -/
  uload : (bs : ByteArray) → (off : USize) → off.toNat + size ≤ bs.size → ρ :=
    fun bs off h => load bs off.toNat h
  /-- `store` splices the serialized bytes into `bs` at `off`. -/
  store_eq_append : ∀ (bs : ByteArray) (x : ρ) (off : Nat) (h : off + size ≤ bs.size),
      store bs x off h = bs.extract 0 off ++ toBytes x ++ bs.extract (off + size) bs.size
  /-- `load` deserializes the `size` bytes of `bs` at `off`. -/
  load_eq_extract : ∀ (bs : ByteArray) (off : Nat) (h : off + size ≤ bs.size),
      load bs off h = fromBytes (bs.extract off (off + size))
  /-- `ustore` is `store` at the `Nat` offset; all reasoning lives on the `Nat` side. -/
  ustore_eq_store : ∀ (bs : ByteArray) (x : ρ) (off : USize) (h : off.toNat + size ≤ bs.size),
      ustore bs x off h = store bs x off.toNat h
  /-- `uload` is `load` at the `Nat` offset; all reasoning lives on the `Nat` side. -/
  uload_eq_load : ∀ (bs : ByteArray) (off : USize) (h : off.toNat + size ≤ bs.size),
      uload bs off h = load bs off.toNat h

/--
Build a `Layout` from the spec fields alone; the exec fields run the spec, and the refinement
equations hold by construction.  A codec that overrides the exec fields with faster primitives
uses the structure constructor directly and proves its own refinement equations.
-/
@[expose] def Layout.ofSpec (size : Nat) (size_pos : 0 < size)
    (size_align : size % 2 ^ k = 0) (toBytes : ρ → ByteArray) (fromBytes : ByteArray → ρ)
    (size_toBytes : ∀ x, (toBytes x).size = size)
    (fromBytes_toBytes : ∀ x, fromBytes (toBytes x) = x) : Layout ρ k where
  size := size
  size_pos := size_pos
  size_align := size_align
  toBytes := toBytes
  fromBytes := fromBytes
  size_toBytes := size_toBytes
  fromBytes_toBytes := fromBytes_toBytes
  store_eq_append bs x off _ := copySlice_eq_append_of_size_eq (size_toBytes x) bs off
  load_eq_extract _ _ _ := rfl
  ustore_eq_store _ _ _ _ := rfl
  uload_eq_load _ _ _ := rfl

/-- A data layout for type `α`, with representation `ρ` and alignment `2 ^ k`. -/
class HasLayout (α : Type u) (ρ : outParam (Type v)) (k : outParam Nat) [DataRepr α ρ] where
  layout : Layout ρ k

end Transmog

/--
Simp set used by data representation subtyping proof automation.  Subtyping is extensively used in
the generated code to carry invariants of data writes that are used for proofs.
-/
register_simp_attr transmog_subtype_simps

/-- Keyed normal-form simp set for `DataRepr.from_to` round-trip proofs. -/
register_simp_attr transmog_norm

/--
Closed simp set for the `_eq_ref` bridge lemmas emitted by `derive_layout` (internal
implementation detail).  It contains exactly what the bridge rewrite needs: the combinator
unfoldings, the splice/extract algebra, and the literal-arithmetic simprocs.  The emitted proofs
use `simp only [transmog_bridge, ...]` so that they never depend on the ambient default simp set.
-/
register_simp_attr transmog_bridge

end -- public section
