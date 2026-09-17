/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL
public import Transmog.Data.CompactArray
meta import Transmog.DSL
meta import Transmog.Data.CompactArray

/-!
# Tests for `derive_layout`

The mode matrix on one three-slot structure, the bytes each mode produces, the exec path at a
nonzero offset on both the `Nat` and the `USize` side, ranged and wide slots, the declarations
a clause generates, the axioms they rest on, and the rejected specs.
-/

-- Deliberately ill-formed declarations follow.
set_option linter.hazel false

namespace Transmog.Test.Derive

open Transmog

@[expose] public section

/-! ## The mode matrix -/

-- Every mode is applied to the same shape: one, four and two bytes, in that order.

structure Packed where
  a : UInt8
  b : UInt32
  c : UInt16
deriving DecidableEq

transmog Packed as [a : UInt8, b : UInt32, c : UInt16] where
  a : UInt8 <= a
  b : UInt32 <= b
  c : UInt16 <= c
derive_layout C packed

example : HasLayout Packed (UInt8 × UInt32 × UInt16) 0 := inferInstance
example : (HasLayout.layout (α := Packed)).size = 7 := rfl
example : ((HasLayout.layout (α := Packed)).toBytes (0x11, 0xDEADBEEF, 0x2233)).data =
    #[0x11, 0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22] := by decide

structure Packed2 where
  a : UInt8
  b : UInt32
  c : UInt16
deriving DecidableEq

transmog Packed2 as [a : UInt8, b : UInt32, c : UInt16] where
  a : UInt8 <= a
  b : UInt32 <= b
  c : UInt16 <= c
derive_layout C packed 2

example : HasLayout Packed2 (UInt8 × UInt32 × UInt16) 1 := inferInstance
example : (HasLayout.layout (α := Packed2)).size = 8 := rfl
example : ((HasLayout.layout (α := Packed2)).toBytes (0x11, 0xDEADBEEF, 0x2233)).data =
    #[0x11, 0, 0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22] := by decide

structure Natural where
  a : UInt8
  b : UInt32
  c : UInt16
deriving DecidableEq

transmog Natural as [a : UInt8, b : UInt32, c : UInt16] where
  a : UInt8 <= a
  b : UInt32 <= b
  c : UInt16 <= c
derive_layout C align 1

-- A gap before `b`, and a tail to the struct alignment of four.
example : HasLayout Natural (UInt8 × UInt32 × UInt16) 2 := inferInstance
example : (HasLayout.layout (α := Natural)).size = 12 := rfl
example : ((HasLayout.layout (α := Natural)).toBytes (0x11, 0xDEADBEEF, 0x2233)).data =
    #[0x11, 0, 0, 0, 0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22, 0, 0] := by decide

structure Aligned8 where
  a : UInt8
  b : UInt32
  c : UInt16
deriving DecidableEq

transmog Aligned8 as [a : UInt8, b : UInt32, c : UInt16] where
  a : UInt8 <= a
  b : UInt32 <= b
  c : UInt16 <= c
derive_layout C align 8

example : HasLayout Aligned8 (UInt8 × UInt32 × UInt16) 3 := inferInstance
example : (HasLayout.layout (α := Aligned8)).size = 16 := rfl
example : ((HasLayout.layout (α := Aligned8)).toBytes (0x11, 0xDEADBEEF, 0x2233)).data =
    #[0x11, 0, 0, 0, 0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22, 0, 0, 0, 0, 0, 0] := by decide

structure Auto2 where
  a : UInt8
  b : UInt32
  c : UInt16
deriving DecidableEq

transmog Auto2 as [a : UInt8, b : UInt32, c : UInt16] where
  a : UInt8 <= a
  b : UInt32 <= b
  c : UInt16 <= c
derive_layout auto packed 2

-- Physical order `b`, `c`, `a`; the representation keeps the declared order.
example : HasLayout Auto2 (UInt8 × UInt32 × UInt16) 1 := inferInstance
example : (HasLayout.layout (α := Auto2)).size = 8 := rfl
example : ((HasLayout.layout (α := Auto2)).toBytes (0x11, 0xDEADBEEF, 0x2233)).data =
    #[0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22, 0x11, 0] := by decide

structure Auto4 where
  a : UInt8
  b : UInt32
  c : UInt16
deriving DecidableEq

transmog Auto4 as [a : UInt8, b : UInt32, c : UInt16] where
  a : UInt8 <= a
  b : UInt32 <= b
  c : UInt16 <= c
derive_layout auto align 4

example : HasLayout Auto4 (UInt8 × UInt32 × UInt16) 2 := inferInstance
example : (HasLayout.layout (α := Auto4)).size = 8 := rfl
example : ((HasLayout.layout (α := Auto4)).toBytes (0x11, 0xDEADBEEF, 0x2233)).data =
    #[0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22, 0x11, 0] := by decide

/-! ## The exec path -/

-- A store at a nonzero offset writes its window, gaps and tail included, and nothing else.
example : ((HasLayout.layout (α := Natural)).store (ByteArray.replicate 14 9)
    (0x11, 0xDEADBEEF, 0x2233) 1 (by decide)).data =
    #[9, 0x11, 0, 0, 0, 0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22, 0, 0, 9] := by decide
example : (HasLayout.layout (α := Natural)).load
    ⟨#[9, 0x11, 7, 7, 7, 0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22, 7, 7, 9]⟩ 1 (by decide) =
    (0x11, 0xDEADBEEF, 0x2233) := by decide
example : ((HasLayout.layout (α := Auto2)).store (ByteArray.replicate 10 9)
    (0x11, 0xDEADBEEF, 0x2233) 1 (by decide)).data =
    #[9, 0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22, 0x11, 0, 9] := by decide
example : (HasLayout.layout (α := Auto2)).load
    ⟨#[9, 0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22, 0x11, 7, 9]⟩ 1 (by decide) =
    (0x11, 0xDEADBEEF, 0x2233) := by decide

-- The `USize` twins are the `Nat` operations by definition, and their compiled forms go through
-- the `USize` scalar primitives.
example (bs : ByteArray) (x : UInt8 × UInt32 × UInt16) (off : USize)
    (h : off.toNat + (HasLayout.layout (α := Natural)).size ≤ bs.size) :
    (HasLayout.layout (α := Natural)).ustore bs x off h =
      (HasLayout.layout (α := Natural)).store bs x off.toNat h := rfl
example (bs : ByteArray) (off : USize)
    (h : off.toNat + (HasLayout.layout (α := Natural)).size ≤ bs.size) :
    (HasLayout.layout (α := Natural)).uload bs off h =
      (HasLayout.layout (α := Natural)).load bs off.toNat h := rfl

#guard ((HasLayout.layout (α := Natural)).ustore (ByteArray.replicate 14 9)
  (0x11, 0xDEADBEEF, 0x2233) 1 (by simp; decide)).data ==
  #[9, 0x11, 0, 0, 0, 0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22, 0, 0, 9]
#guard (HasLayout.layout (α := Natural)).uload
  ⟨#[9, 0x11, 7, 7, 7, 0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22, 7, 7, 9]⟩ 1 (by simp; decide)
  == (0x11, 0xDEADBEEF, 0x2233)
#guard ((HasLayout.layout (α := Auto2)).ustore (ByteArray.replicate 10 9)
  (0x11, 0xDEADBEEF, 0x2233) 1 (by simp; decide)).data ==
  #[9, 0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22, 0x11, 0, 9]

-- The flagship round trip, on a derived layout.
example (x : Natural) (bs : ByteArray) (h : off + (HasLayout.layout (α := Natural)).size ≤ bs.size) :
    DataRepr.fromRepr ((HasLayout.layout (α := Natural)).load
      ((HasLayout.layout (α := Natural)).store bs (DataRepr.toRepr x) off h) off
      (by simpa using h)) = x :=
  Layout.fromRepr_load_store_toRepr _ h

/-! ## Ranged and wide slots -/

structure Masked where
  n : { u : UInt32 // u.fitsBits 20 }
  t : UInt8
deriving DecidableEq

transmog Masked as [n : UInt32[0:20], t : UInt8] where
  n : { u : UInt32 // u.fitsBits 20 } <= n
  t : UInt8 <= t
derive_layout C packed

example : HasLayout Masked ({ n : UInt32 // UInt32.fitsBits 20 n } × UInt8) 0 := inferInstance
example : (HasLayout.layout (α := Masked)).size = 5 := rfl
example : ((HasLayout.layout (α := Masked)).toBytes (⟨0xABCDE, by decide⟩, 6)).data =
    #[0xDE, 0xBC, 0x0A, 0, 6] := by decide
-- Decoding masks the stored scalar to the slot's width.
example : ((HasLayout.layout (α := Masked)).fromBytes ⟨#[0xDE, 0xBC, 0xFA, 0xFF, 6]⟩).1.val =
    0xABCDE := by decide

structure Wide where
  w : UInt64
  b : UInt8
deriving DecidableEq

transmog Wide as [w : UInt64, b : UInt8] where
  w : UInt64 <= w
  b : UInt8 <= b
derive_layout C align 1

example : HasLayout Wide (UInt64 × UInt8) 3 := inferInstance
example : (HasLayout.layout (α := Wide)).size = 16 := rfl
example : ((HasLayout.layout (α := Wide)).toBytes (0x0102030405060708, 9)).data =
    #[8, 7, 6, 5, 4, 3, 2, 1, 9, 0, 0, 0, 0, 0, 0, 0] := by decide

/-! ## Over a `CompactArray` -/

#guard ((CompactArray.empty : CompactArray Natural).push ⟨0x11, 0xDEADBEEF, 0x2233⟩).data.data ==
  #[0x11, 0, 0, 0, 0xEF, 0xBE, 0xAD, 0xDE, 0x33, 0x22, 0, 0]
#guard
  let xs := ([⟨1, 2, 3⟩, ⟨4, 5, 6⟩] : List Auto2).toCompactArray
  xs.data.size == 16 && xs.toList == [⟨1, 2, 3⟩, ⟨4, 5, 6⟩] &&
    (xs.set 0 ⟨7, 8, 9⟩ (by simp [xs])).toList == [⟨7, 8, 9⟩, ⟨4, 5, 6⟩]

set_option maxRecDepth 4096 in
example : (((CompactArray.empty : CompactArray Packed).push ⟨1, 2, 3⟩).push ⟨4, 5, 6⟩)[1] =
    ⟨4, 5, 6⟩ := by decide

/-! ## The generated declarations -/

-- The reference layout is the combinator term: nested products at relative offsets, padded to
-- the size and alignment.
example : Natural.Repr.layoutRef =
    (Layout.uint8.prodAt (Layout.uint32.prodAt Layout.uint16 4 (by decide)) 4 (by decide)).pad
      12 2 (by decide) (by decide) :=
  rfl

-- Reordering is a retraction around the physical layout.
example : Auto2.Repr.layoutRef =
    ((Layout.uint32.prodAt (Layout.uint16.prodAt Layout.uint8 2 (by decide)) 4 (by decide)).pad
      8 1 (by decide) (by decide)).ofRetract (fun x => (x.2.1, x.2.2, x.1))
      (fun y => (y.2.2, y.1, y.2.1)) (fun _ => rfl) :=
  rfl

/-- info: @[expose] def Transmog.Test.Derive.Natural.Repr.layoutRef : Layout (UInt8 × UInt32 × UInt16) 2 -/
#guard_msgs in
#print sig Natural.Repr.layoutRef

-- The flat exec definitions use the scalar primitives at literal offsets and zero the padding.
/--
info: @[expose] def Transmog.Test.Derive.Natural.Repr.store : (bs : ByteArray) →
  UInt8 × UInt32 × UInt16 → (off : Nat) → off + 12 ≤ bs.size → ByteArray :=
fun bs x off h ↦
  ((((bs.set off x.fst ⋯).setZeros (off + 1) 3).set32 (off + 4) x.snd.fst ⋯).set16 (off + 8) x.snd.snd ⋯).setZeros
    (off + 10) 2
-/
#guard_msgs in
#print Natural.Repr.store

/--
info: @[expose] def Transmog.Test.Derive.Natural.Repr.load : (bs : ByteArray) →
  (off : Nat) → off + 12 ≤ bs.size → UInt8 × UInt32 × UInt16 :=
fun bs off h ↦ (bs[off], bs.get32 (off + 4) ⋯, bs.get16 (off + 8) ⋯)
-/
#guard_msgs in
#print Natural.Repr.load

/--
info: @[expose] def Transmog.Test.Derive.Natural.Repr.toBytes : UInt8 × UInt32 × UInt16 → ByteArray :=
fun x ↦
  x.fst.toLEBytes ++ ByteArray.replicate 3 0 ++ x.snd.fst.toLEBytes ++ x.snd.snd.toLEBytes ++ ByteArray.replicate 2 0
-/
#guard_msgs in
#print Natural.Repr.toBytes

/--
info: @[expose] def Transmog.Test.Derive.Natural.Repr.fromBytes : ByteArray → UInt8 × UInt32 × UInt16 :=
fun bs ↦ (UInt8.ofLEBytes (bs.extract 0 1), UInt32.ofLEBytes (bs.extract 4 8), UInt16.ofLEBytes (bs.extract 8 10))
-/
#guard_msgs in
#print Natural.Repr.fromBytes

/--
info: theorem Transmog.Test.Derive.Natural.Repr.store_eq_ref : ∀ (bs : ByteArray) (x : UInt8 × UInt32 × UInt16) (off : Nat)
  (h : off + 12 ≤ bs.size), Natural.Repr.store bs x off h = Natural.Repr.layoutRef.store bs x off h
-/
#guard_msgs in
#print sig Natural.Repr.store_eq_ref

/--
info: theorem Transmog.Test.Derive.Natural.Repr.load_eq_ref : ∀ (bs : ByteArray) (off : Nat) (h : off + 12 ≤ bs.size),
  Natural.Repr.load bs off h = Natural.Repr.layoutRef.load bs off h
-/
#guard_msgs in
#print sig Natural.Repr.load_eq_ref

/--
info: theorem Transmog.Test.Derive.Natural.Repr.toBytes_eq_ref : ∀ (x : UInt8 × UInt32 × UInt16),
  Natural.Repr.toBytes x = Natural.Repr.layoutRef.toBytes x
-/
#guard_msgs in
#print sig Natural.Repr.toBytes_eq_ref

/--
info: theorem Transmog.Test.Derive.Natural.Repr.fromBytes_eq_ref : ∀ (bs : ByteArray),
  Natural.Repr.fromBytes bs = Natural.Repr.layoutRef.fromBytes bs
-/
#guard_msgs in
#print sig Natural.Repr.fromBytes_eq_ref

/--
info: @[expose] def Transmog.Test.Derive.Natural.Repr.ustore : (bs : ByteArray) →
  UInt8 × UInt32 × UInt16 → (off : USize) → off.toNat + 12 ≤ bs.size → ByteArray
-/
#guard_msgs in
#print sig Natural.Repr.ustore

/--
info: @[expose] def Transmog.Test.Derive.Natural.Repr.uload : (bs : ByteArray) →
  (off : USize) → off.toNat + 12 ≤ bs.size → UInt8 × UInt32 × UInt16
-/
#guard_msgs in
#print sig Natural.Repr.uload

/--
info: @[expose] unsafe def Transmog.Test.Derive.Natural.Repr.ustoreImpl : (bs : ByteArray) →
  UInt8 × UInt32 × UInt16 → (off : USize) → off.toNat + 12 ≤ bs.size → ByteArray
-/
#guard_msgs in
#print sig Natural.Repr.ustoreImpl

-- The `USize` twins are compiled through their implementations.
run_meta do
  let env ← Lean.getEnv
  unless Lean.Compiler.getImplementedBy? env ``Natural.Repr.ustore == some ``Natural.Repr.ustoreImpl do
    throwError "ustore is not implemented by ustoreImpl"
  unless Lean.Compiler.getImplementedBy? env ``Natural.Repr.uload == some ``Natural.Repr.uloadImpl do
    throwError "uload is not implemented by uloadImpl"

/-! ## Axioms -/

theorem packed_roundTrip (x : UInt8 × UInt32 × UInt16) :
    (HasLayout.layout (α := Packed)).fromBytes ((HasLayout.layout (α := Packed)).toBytes x) = x :=
  Layout.fromBytes_toBytes _ x

theorem masked_roundTrip (x : { n : UInt32 // UInt32.fitsBits 20 n } × UInt8) :
    (HasLayout.layout (α := Masked)).fromBytes ((HasLayout.layout (α := Masked)).toBytes x) = x :=
  Layout.fromBytes_toBytes _ x

/-- A layout of bytes alone rests on nothing beyond the standard axioms. -/
structure Bytes where
  a : UInt8
  b : UInt8
deriving DecidableEq

transmog Bytes as [a : UInt8, b : UInt8] where
  a : UInt8 <= a
  b : UInt8 <= b
derive_layout C packed

theorem bytes_roundTrip (x : UInt8 × UInt8) :
    (HasLayout.layout (α := Bytes)).fromBytes ((HasLayout.layout (α := Bytes)).toBytes x) = x :=
  Layout.fromBytes_toBytes _ x

/-- info: 'Transmog.Test.Derive.bytes_roundTrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bytes_roundTrip

-- A wider scalar brings in the `bv_decide` byte recompositions.
/--
info: 'Transmog.Test.Derive.packed_roundTrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.Transmog.Data.ByteArray.Lemmas.0.UInt16.of_le_bytes._native.bv_decide.ax_1_9,
 _private.Transmog.Data.ByteArray.Lemmas.0.UInt32.of_le_bytes._native.bv_decide.ax_1_11]
-/
#guard_msgs in
#print axioms packed_roundTrip

/--
info: 'Transmog.Test.Derive.masked_roundTrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.Transmog.Data.ByteArray.Lemmas.0.UInt32.of_le_bytes._native.bv_decide.ax_1_11]
-/
#guard_msgs in
#print axioms masked_roundTrip

-- The representation itself needs none of them.
/-- info: 'Transmog.Test.Derive.Natural.Repr.from_to' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Natural.Repr.from_to

end

/-! ## Errors -/

structure Q where
  x : UInt32

/--
error: `derive_layout` supports exactly one layout spec for now: only one `HasLayout` instance can exist per type
-/
#guard_msgs in
transmog Q as [a : UInt32] where
  x : UInt32 <= a
derive_layout C packed, auto packed

structure R where
  x : UInt32

/--
error: `auto` has no effect under `packed`: without alignment padding there is nothing for reordering to save; use `C packed`
-/
#guard_msgs in
transmog R as [a : UInt32] where
  x : UInt32 <= a
derive_layout auto packed

structure S where
  x : UInt32

/-- error: packed alignment cap must be a positive power of two -/
#guard_msgs in
transmog S as [a : UInt32] where
  x : UInt32 <= a
derive_layout C packed 3

structure T where
  x : UInt32

/-- error: packed alignment cap must be a positive power of two -/
#guard_msgs in
transmog T as [a : UInt32] where
  x : UInt32 <= a
derive_layout C packed 0

structure U where
  x : UInt32

/-- error: alignment must be a positive power of two -/
#guard_msgs in
transmog U as [a : UInt32] where
  x : UInt32 <= a
derive_layout C align 3

structure V where
  x : { u : UInt32 // u ≠ 0 }

/--
error: cannot derive a layout for slot `a`: it carries a custom `//` property, and decoding raw bytes cannot re-establish an arbitrary predicate
-/
#guard_msgs in
transmog V as [a : UInt32 // a ≠ 0] where
  x : { u : UInt32 // u ≠ 0 } <= a
derive_layout C packed

end Transmog.Test.Derive
