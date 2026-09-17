/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog
meta import Transmog.Data.CompactArray

/-!
# Tests for the public names

The public types live directly under `Transmog`, the generated code does not depend on what the
user has opened, and the words of the DSL stay ordinary identifiers.  Nothing is opened in this
file, and it lives outside the `Transmog` namespace, so that no name is reachable through it.
-/

-- Declarations named after the DSL words follow.
set_option linter.hazel false

namespace TransmogTest.Names

@[expose] public section

/-! ## The public types -/

/-- info: Transmog.DataRepr.{u, v} (α : Type u) (ρ : outParam (Type v)) : Type (max u v) -/
#guard_msgs in
#check Transmog.DataRepr

/--
info: Transmog.HasLayout.{u, v} (α : Type u) (ρ : outParam (Type v)) (k : outParam Nat) [Transmog.DataRepr α ρ] : Type v
-/
#guard_msgs in
#check Transmog.HasLayout

/-- info: Transmog.Layout.{u} (ρ : Type u) (k : Nat) : Type u -/
#guard_msgs in
#check Transmog.Layout

/-- info: Transmog.Layout.uint8 : Transmog.Layout UInt8 0 -/
#guard_msgs in
#check Transmog.Layout.uint8

/-- info: Transmog.DataCast.{u, v} (α : semiOutParam (Type u)) (β : Type v) : Type (max u v) -/
#guard_msgs in
#check Transmog.DataCast

/-- info: Transmog.DataCastT.{u, v} (α : Type u) (β : Type v) : Type (max u v) -/
#guard_msgs in
#check Transmog.DataCastT

/--
info: Transmog.CompactArray.{u, v} (α : Type u) {ρ : Type v} {align : Nat} [Transmog.DataRepr α ρ]
  [Transmog.HasLayout α ρ align] : Type
-/
#guard_msgs in
#check Transmog.CompactArray

-- The lemmas of a layout are reached by dot notation.
example (L : Transmog.Layout ρ k) (bs : ByteArray) (x : ρ) (off : Nat)
    (h : off + L.size ≤ bs.size) : (L.store bs x off h).size = bs.size :=
  L.size_store ..

/-! ## The DSL with nothing open -/

structure Point where
  x : UInt32
  y : UInt16

transmog Point as [px : UInt32, py : UInt16] where
  x : UInt32 <= px
  y : UInt16 <= py
derive_layout C packed

example : Transmog.DataRepr Point (UInt32 × UInt16) := inferInstance
example : (Transmog.HasLayout.layout (α := Point)).size = 6 := rfl

transmog enum Flag as [t : UInt8] where
  | off => guard t = 0
  | on => t := 1
derive_layout C packed
deriving DecidableEq, Repr

transmog struct Cell as [f : UInt8, v : UInt32] where
  flag : Flag <= f
  big : { x : UInt32 // x.fitsBits 24 } <= v[0:24]
derive_layout C packed
deriving Repr

example : (Transmog.HasLayout.layout (α := Cell)).size = 5 := rfl
example : (Transmog.DataRepr.toRepr (Cell.mk .on ⟨0x123456, by decide⟩) : UInt8 × UInt32)
    = (1, 0x123456) := rfl

def cells : Transmog.CompactArray Cell :=
  Transmog.CompactArray.empty.push ⟨.on, ⟨7, by decide⟩⟩

/-- info: [{ flag := TransmogTest.Names.Flag.on, big := 7 }] -/
#guard_msgs in
#eval cells.toList

/-- info: 5 -/
#guard_msgs in
#eval cells.data.size

inductive Bit where
  | zero
  | one
deriving DecidableEq, Inhabited

transmog Bit as [b : UInt8] where
  | zero => guard b = 0
  | one => guard b = 1
correct_by
  transmog_from_to []

example : Bit.Repr.fromRepr 1 = .one := by decide

/-! ## The DSL words are identifiers -/

namespace Words

def enum := 1
def struct := 2
def as := 3
def guard := 4
def C := 5
def auto := 6
def packed := 7
def align := 8
def cast := 9
def lsbAsBool := 10
def derive_layout := 11
def replace_runtime := 12
def correct_by := 13

example : enum + struct + as + guard + C + auto + packed + align + cast + lsbAsBool
    + derive_layout + replace_runtime + correct_by = 91 := rfl

/-- info: 5 -/
#guard_msgs in
#eval repr 5

end Words

-- A type named after one of the two declaration words is reached through parentheses.
inductive «enum» where
  | a
  | b

transmog («enum») as [t : UInt8] where
  | a => guard t = 0
  | b => t := 1

example : «enum».Repr.toRepr .b = 1 := rfl

structure «struct» where
  x : UInt8

transmog («struct») as [t : UInt8] where
  x : UInt8 <= t

example : «struct».Repr.toRepr ⟨3⟩ = 3 := rfl

end

end TransmogTest.Names
