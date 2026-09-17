/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL.Core.Layout
public import Transmog.Data.CompactArray
meta import Transmog.DSL.Core.Layout
meta import Transmog.Data.CompactArray

/-!
# Tests for `CompactArray`

The collection API is exercised over the scalar layouts, the two iterator interfaces are run to
completion, the canonicity invariant is checked on a hand-written padded layout, and the lemma
base is exercised through `simp` and `grind`.
-/

namespace Transmog.Test.CompactArray

open Transmog

/-! ## Construction and access -/

#guard (CompactArray.empty : CompactArray UInt64).size == 0
#guard (CompactArray.empty : CompactArray UInt64).isEmpty
#guard (CompactArray.emptyWithCapacity 8 : CompactArray UInt64).size == 0
#guard (CompactArray.emptyWithCapacity 8 : CompactArray UInt64) == CompactArray.empty
#guard (∅ : CompactArray UInt64) == CompactArray.empty
#guard (default : CompactArray UInt64) == CompactArray.empty

#guard ([1, 2, 3] : List UInt64).toCompactArray.size == 3
#guard ([1, 2, 3] : List UInt64).toCompactArray.toList == [1, 2, 3]
#guard !([1, 2, 3] : List UInt64).toCompactArray.isEmpty
#guard ([] : List UInt64).toCompactArray == CompactArray.empty

-- The data is the concatenation of the canonical encodings.
#guard ([0x0201, 0x0403] : List UInt16).toCompactArray.data.data == #[1, 2, 3, 4]
#guard ([1, 2, 3] : List UInt8).toCompactArray.data.data == #[1, 2, 3]
#guard ((CompactArray.empty : CompactArray UInt32).push 0xDEADBEEF).data.data ==
  #[0xEF, 0xBE, 0xAD, 0xDE]

#guard (([1, 2, 3] : List UInt64).toCompactArray.get 1 (by simp)) == 2
#guard (([1, 2, 3] : List UInt64).toCompactArray.get! 1) == 2
#guard (([1, 2, 3] : List UInt64).toCompactArray)[2] == 3
#guard (([1, 2, 3] : List UInt64).toCompactArray)[(2 : USize)] == 3
#guard (([1, 2, 3] : List UInt64).toCompactArray.uget 0 (by simp)) == 1

#guard (([1, 2, 3] : List UInt64).toCompactArray.set 1 9 (by simp)).toList == [1, 9, 3]
#guard (([1, 2, 3] : List UInt64).toCompactArray.set! 1 9).toList == [1, 9, 3]
#guard (([1, 2, 3] : List UInt64).toCompactArray.set! 3 9).toList == [1, 2, 3]
#guard (([1, 2, 3] : List UInt64).toCompactArray.uset 2 9 (by simp)).toList == [1, 2, 9]

-- A compiled update copies a shared array instead of mutating it in place.
#guard
  let xs := ([1, 2, 3] : List UInt64).toCompactArray
  let ys := xs.uset 1 7 (by simp [xs])
  xs.toList == [1, 2, 3] && ys.toList == [1, 7, 3]

#guard (([1, 2, 3] : List UInt64).toCompactArray.push 4).toList == [1, 2, 3, 4]
#guard (([1, 2, 3] : List UInt64).toCompactArray.push 4).usize == 4

/-! ## Slices, concatenation and copies -/

#guard (([1, 2, 3, 4] : List UInt64).toCompactArray.extract 1 3).toList == [2, 3]
#guard (([1, 2, 3, 4] : List UInt64).toCompactArray.extract 1 9).toList == [2, 3, 4]
#guard (([1, 2, 3, 4] : List UInt64).toCompactArray.extract 3 1).toList == []
#guard (([1, 2, 3, 4] : List UInt64).toCompactArray.extract 2 2) == CompactArray.empty
#guard (([1, 2] : List UInt64).toCompactArray ++ ([3] : List UInt64).toCompactArray).toList ==
  [1, 2, 3]
#guard (([1, 2] : List UInt64).toCompactArray ++ CompactArray.empty).toList == [1, 2]

-- `copySlice` clips the source window, the destination offset and the length, and grows the
-- destination when the copy runs past its end.
#guard
  let src := ([1, 2, 3, 4] : List UInt64).toCompactArray
  let dest := ([10, 20, 30] : List UInt64).toCompactArray
  (List.range 7).all fun srcOff => (List.range 7).all fun destOff => (List.range 7).all fun len =>
    let n := min len (src.size - srcOff)
    let expected := dest.toList.take destOff ++ (src.toList.drop srcOff).take len ++
      dest.toList.drop (destOff + n)
    (src.copySlice srcOff dest destOff len).toList == expected

#guard
  let src := ([1, 2, 3, 4] : List UInt64).toCompactArray
  let dest := ([10, 20, 30] : List UInt64).toCompactArray
  (src.copySlice 1 dest 1 2).toList == [10, 2, 3] &&
    (src.copySlice 0 dest 2 4 (exact := false)).toList == [10, 20, 1, 2, 3, 4]

/-! ## Search, folds and loops -/

#guard ([1, 2, 3, 4] : List UInt64).toCompactArray.findIdx? (· == 3) == some 2
#guard ([1, 2, 3, 4] : List UInt64).toCompactArray.findIdx? (· == 1) 1 == none
#guard ([1, 2, 3, 4] : List UInt64).toCompactArray.findIdx? (fun _ => true) 99 == none
#guard (([1, 2, 3, 4] : List UInt64).toCompactArray.findFinIdx? (· == 4)).map (·.val) == some 3
#guard ([1, 2, 3, 4] : List UInt64).toCompactArray.foldl (· + ·) 0 == 10
#guard ([1, 2, 3, 4] : List UInt64).toCompactArray.foldl (· + ·) 0 (start := 1) (stop := 3) == 5
#guard ([1, 2, 3, 4] : List UInt64).toCompactArray.foldl (· + ·) 0 (start := 3) (stop := 99) == 4
#guard ([1, 2, 3, 4] : List UInt64).toCompactArray.foldl (· + ·) 0 (start := 3) (stop := 1) == 0
#guard (([1, 2, 3, 4] : List UInt64).toCompactArray.foldlM (m := Option)
  (fun acc x => if x == 3 then none else some (acc + x)) 0) == none
#guard (([1, 2, 4] : List UInt64).toCompactArray.foldlM (m := Option)
  (fun acc x => if x == 3 then none else some (acc + x)) 0) == some 7

#guard_msgs in
#eval show IO Unit from do
  let mut acc := #[]
  for x in ([1, 2, 3, 4] : List UInt64).toCompactArray do
    if x == 4 then break
    acc := acc.push x
  unless acc == #[1, 2, 3] do throw (IO.userError "for-in")

/-! ## Equality and hashing -/

#guard ([1, 2] : List UInt64).toCompactArray == ([1, 2] : List UInt64).toCompactArray
#guard ([1, 2] : List UInt64).toCompactArray != ([2, 1] : List UInt64).toCompactArray
#guard ([1, 2] : List UInt64).toCompactArray != ([1, 2, 3] : List UInt64).toCompactArray
#guard decide (([1, 2] : List UInt64).toCompactArray = ([1, 2] : List UInt64).toCompactArray)
#guard hash ([1, 2] : List UInt64).toCompactArray == hash ([1, 2] : List UInt64).toCompactArray
#guard hash ([1, 2] : List UInt64).toCompactArray != hash ([2, 1] : List UInt64).toCompactArray

example : LawfulBEq (CompactArray UInt8) := inferInstance

/-! ## The `Std.Iterator` interface -/

#guard ([1, 2, 3, 4] : List UInt64).toCompactArray.iter.toList == [1, 2, 3, 4]
#guard (([1, 2, 3, 4] : List UInt64).toCompactArray.iterFromIdx 0).toList == [1, 2, 3, 4]
#guard (([1, 2, 3, 4] : List UInt64).toCompactArray.iterFromIdx 2).toList == [3, 4]
#guard (([1, 2, 3, 4] : List UInt64).toCompactArray.iterFromIdx 4).toList == []
#guard (([1, 2, 3, 4] : List UInt64).toCompactArray.iterFromIdx 99).toList == []
#guard (([1, 2, 3, 4] : List UInt64).toCompactArray.iter.map (· * 2)).toList == [2, 4, 6, 8]
#guard ([1, 2, 3, 4] : List UInt64).toCompactArray.iter.fold (· + ·) 0 == 10

#guard_msgs in
#eval show IO Unit from do
  let mut acc := 0
  for x in ([1, 2, 3, 4] : List UInt64).toCompactArray.iter do
    acc := acc + x
  unless acc == 10 do throw (IO.userError "for-in over an iterator")

/-! ## The positional `Iterator` -/

#guard
  let it := ([1, 2, 3] : List UInt64).toCompactArray.mkIterator
  it.remaining == 3 && it.hasNext && !it.hasPrev && !it.atEnd && it.curr == 1 && it.pos == 0

#guard
  let it := ([1, 2, 3] : List UInt64).toCompactArray.mkIterator.next
  it.remaining == 2 && it.hasNext && it.hasPrev && it.curr == 2 && it.prev.curr == 1

#guard
  let it := ([1, 2, 3] : List UInt64).toCompactArray.mkIterator.toEnd
  it.remaining == 0 && !it.hasNext && it.atEnd && it.curr == default && it.prev.curr == 3

#guard
  let it := ([1, 2, 3] : List UInt64).toCompactArray.mkIterator
  (it.forward 2).curr == 3 && (it.nextn 2).curr == 3 && ((it.nextn 2).prevn 5).pos == 0 &&
    it.next.prev.pos == 0 && it.prev.pos == 0

#guard
  let it := ([1, 2, 3] : List UInt64).toCompactArray.mkIterator
  it.curr' (by decide) == 1 && (it.next' (by decide)).curr' (by decide) == 2

-- The iterator shrinks in the well-founded measure with every step.
example (it : CompactArray.Iterator (α := UInt64)) (h : it.hasNext) :
    sizeOf it.next < sizeOf it := by
  simp only [CompactArray.Iterator.sizeOf_eq, CompactArray.Iterator.next, CompactArray.Iterator.hasNext,
    decide_eq_true_eq] at *
  omega

/-! ## Canonical padding -/

@[expose] public section

/-- A byte stored in a two-byte slot; the second byte is padding. -/
structure PaddedByte where
  val : UInt8
deriving Inhabited, DecidableEq

instance : DataRepr PaddedByte UInt8 := ⟨PaddedByte.val, PaddedByte.mk, fun _ => rfl⟩
instance : HasLayout PaddedByte UInt8 0 := ⟨Layout.uint8.pad 2 0 (by decide) (by decide)⟩

end

-- The padding byte is zero-filled by the exec path, and a self update leaves the bytes alone.
#guard ((CompactArray.empty : CompactArray PaddedByte).push ⟨42⟩).data.data == #[42, 0]
#guard
  let xs := (CompactArray.empty : CompactArray PaddedByte).push ⟨42⟩
  xs.set 0 (xs[0]'(by decide)) (by decide) == xs

-- A buffer with a dirty padding byte is not a compact array, because no element encodes to it.
example (xs : CompactArray PaddedByte) (hs : xs.size = 1) : xs.data ≠ ⟨#[42, 1]⟩ := by
  intro hd
  obtain ⟨x, hx⟩ := xs.isCanonical 0 (by omega)
  change xs.data.extract 0 2 = [x.val, 0].toByteArray at hx
  rw [hd] at hx
  have he := congrArg (fun bs : ByteArray => bs[1]!) hx
  change (1 : UInt8) = 0 at he
  contradiction

/-! ## The lemma base -/

section

variable [DataRepr α ρ] [HasLayout α ρ k] {xs ys : CompactArray α}

example (h : i < xs.size) : (xs.set i x h)[i]'(by simpa using h) = x := by simp
example (h : i < xs.size) : xs.set i xs[i] h = xs := by simp
example (h : xs.size < (xs.push x).size) : (xs.push x)[xs.size] = x := by simp
example (h : i < xs.size) (h' : i < (xs.push x).size) : (xs.push x)[i] = xs[i] := by
  simp [CompactArray.getElem_push, h]
example : (xs ++ ys).size = xs.size + ys.size := by simp
example : (xs ++ ys).toList = xs.toList ++ ys.toList := by simp
example : xs.toList = ys.toList ↔ xs = ys := by simp
example : xs.toList.length = xs.size := by simp
example (c : Nat) : (CompactArray.emptyWithCapacity c : CompactArray α) = ∅ := by simp
example : xs.size = 0 ↔ xs = CompactArray.empty := by simp
example (i : USize) (h : i.toNat < xs.size) : xs.uset i x h = xs.set i.toNat x h := by simp
example (i : USize) (h : i.toNat < xs.size) : xs[i] = xs[i.toNat] := by simp
example (l : List α) : l.toCompactArray.size = l.length := by simp
example : xs.extract 0 xs.size = xs := by simp
example : (xs.extract start stop).toList = (xs.toList.drop start).take (stop - start) := by simp

example (hi : i < xs.size) (h : i < (xs ++ ys).size) : (xs ++ ys)[i] = xs[i] := by
  grind
example (hi : xs.size ≤ i) (h : i < (xs ++ ys).size) :
    (xs ++ ys)[i] = ys[i - xs.size]'(by simp at h; omega) := by
  grind
example (hi : i < xs.size) (hj : j < (xs.set i x hi).size) :
    (xs.set i x hi)[j] = if i = j then x else xs[j]'(by simpa using hj) := by
  grind

end

end Transmog.Test.CompactArray
