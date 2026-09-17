/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Transmog.DSL.Core.Basic
public import Transmog.Data.ByteArray.Basic
import Init.Data.ByteArray.Lemmas
import Init.Data.List.OfFn
import Transmog.DSL.Core.Lemmas
import Transmog.Data.ByteArray.Lemmas

/-!
# Compact array

`CompactArray α` is like `Array α`, but with a packed run-time representation backed by a
`ByteArray`, using `HasLayout α ρ align` to store each element into `layout.size` bytes.

Each element occupies one fixed-size slot.  Every slot contains the canonical encoding of
an element, so byte equality agrees with elementwise equality.
-/

@[expose] public section

namespace Transmog

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.


/--
`CompactArray α` is like `Array α`, but with a packed run-time representation
backed by a `ByteArray`, using `HasLayout α ρ` to store each element into
`layout.size` bytes.
-/
structure CompactArray (α : Type u) {ρ : Type v} {align : Nat} [DataRepr α ρ]
    [HasLayout α ρ align] where
  /-- The data contained in the compact array, as a packed byte buffer. -/
  data : ByteArray
  /-- The number of elements in the compact array. -/
  size : Nat
  /-- The byte buffer has length `size * layout.size`. -/
  size_data : data.size = size * (HasLayout.layout (α := α)).size
  /-- Every slot contains the serialization of an element. -/
  isCanonical : ∀ i, i < size → ∃ x : α,
    data.extract (i * (HasLayout.layout (α := α)).size)
        (i * (HasLayout.layout (α := α)).size + (HasLayout.layout (α := α)).size) =
      (HasLayout.layout (α := α)).toBytes (DataRepr.toRepr x)

namespace CompactArray

variable {α : Type u} {ρ : Type v} {align : Nat} [DataRepr α ρ] [HasLayout α ρ align]

/-! ## Internal helpers -/

/--
The core slot-bounds arithmetic: if `i < xs.size`, then the byte range `[i*sz, i*sz + sz)`
fits inside `xs.data`.
-/
theorem slot_le_size (xs : CompactArray α)
    (h : i < xs.size) :
    i * (HasLayout.layout (α := α)).size +
        (HasLayout.layout (α := α)).size ≤ xs.data.size := by
  rw [xs.size_data, ← Nat.succ_mul]
  exact Nat.mul_le_mul_right _ h

/--
If `i ≠ j`, the byte ranges `[i*sz, i*sz + sz)` and `[j*sz, j*sz + sz)` are disjoint
(using `0 < sz`).
-/
theorem slot_disjoint_of_ne
     (hij : i ≠ j) :
    i * (HasLayout.layout (α := α)).size +
        (HasLayout.layout (α := α)).size ≤
        j * (HasLayout.layout (α := α)).size ∨
      j * (HasLayout.layout (α := α)).size +
        (HasLayout.layout (α := α)).size ≤
        i * (HasLayout.layout (α := α)).size := by
  have hp : 0 < (HasLayout.layout (α := α)).size :=
    (HasLayout.layout (α := α)).size_pos
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · left
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ h
  · right
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ h

/-! ## Empty array / capacity -/

/-- Constructs a new empty compact array with initial capacity `c`. -/
def emptyWithCapacity (c : @& Nat) : CompactArray α where
  data := .emptyWithCapacity (c * (HasLayout.layout (α := α)).size)
  size := 0
  size_data := by
    show (ByteArray.emptyWithCapacity _).size = 0 * _
    rw [Nat.zero_mul]
    rfl
  isCanonical i h := by omega

/--
Constructs a new empty compact array with initial capacity `0`.

Use `CompactArray.emptyWithCapacity` to create an array with a greater initial capacity.
-/
def empty : CompactArray α := emptyWithCapacity 0

/-! ## Push -/

/--
Adds an element to the end of an array.  The resulting array's size is one greater than the input
array.

This takes amortized `O(1)` time because `ByteArray` is represented by a dynamic array.
-/
@[inline]
def push (xs : CompactArray α) (x : α) :
    CompactArray α :=
  let L : Layout ρ align := HasLayout.layout (α := α)
  let grown : ByteArray := xs.data ++ ByteArray.replicate L.size 0
  have h_grown_size : grown.size = (xs.size + 1) * L.size := by
    show (xs.data ++ ByteArray.replicate L.size 0).size = (xs.size + 1) * L.size
    rw [ByteArray.size_append, xs.size_data, ByteArray.size_replicate, Nat.succ_mul]
  have h_off : xs.size * L.size + L.size ≤ grown.size := by
    rw [h_grown_size, Nat.succ_mul]; exact Nat.le_refl _
  { data := L.store grown (DataRepr.toRepr x) (xs.size * L.size) h_off
    size := xs.size + 1
    size_data := by simpa only [L] using (L.size_store h_off).trans h_grown_size
    isCanonical i hi := by
      by_cases h : i < xs.size
      · obtain ⟨y, hy⟩ := xs.isCanonical i h
        have hb : i * L.size + L.size ≤ xs.data.size := xs.slot_le_size h
        have hd : i * L.size + L.size ≤ xs.size * L.size := by
          simpa only [Nat.succ_mul] using Nat.mul_le_mul_right L.size h
        have hg : i * L.size + L.size ≤ grown.size := by
          simp only [grown, ByteArray.size_append, ByteArray.size_replicate]
          omega
        exact ⟨y, by
          rw [L.extract_store_of_disjoint h_off hg (Or.inr hd)]
          rwa [ByteArray.extract_append_of_le hb]⟩
      · have he : i = xs.size := by omega
        exact ⟨x, by simpa only [he, L] using L.extract_store_self (x := DataRepr.toRepr x) h_off⟩ }

/-- Converts a list of elements into a `CompactArray α`. -/
def _root_.List.toCompactArray (xs : List α) :
    CompactArray α :=
  let rec loop : List α → CompactArray α →
      CompactArray α
    | List.nil,        r => r
    | List.cons x xs', r => loop xs' (r.push x)
  loop xs CompactArray.empty

/-! ## Equality / BEq / DecidableEq -/

/-- Boolean equality on `CompactArray α`. -/
def beq (lhs rhs : @& CompactArray α) : Bool :=
  lhs.data == rhs.data

instance : BEq (CompactArray α) where
  beq := beq

attribute [ext] CompactArray

/-- Decidable equality on `CompactArray α`. -/
def decEq (lhs rhs : @& CompactArray α) : Decidable (lhs = rhs) :=
  decidable_of_decidable_of_iff CompactArray.ext_iff.symm

instance : DecidableEq (CompactArray α) := decEq

instance : Inhabited (CompactArray α) where
  default := empty

instance : EmptyCollection (CompactArray α) where
  emptyCollection := CompactArray.empty

/-! ## `usize` (element count) -/

/--
Retrieves the size of the array as a platform-specific fixed-width integer.

Unlike `ByteArray.usize`, this is the *element count*, matching `Array.usize`.

Because `USize` is big enough to address all memory on every platform that Lean supports, there are
in practice no `CompactArray`s that have more elements than `USize` can count.
-/
@[simp]
def usize (xs : @& CompactArray α) : USize :=
  xs.size.toUSize

/-! ## `get` family -/

/--
An efficient implementation of `CompactArray.uget` that computes the byte offset in `USize`
arithmetic and reads through `Layout.uload`.

We claim this unsafe implementation is correct because an array cannot have more than
`USize.size` elements in our runtime.  This is similar to the `Array` version.
-/
@[inline]
unsafe def ugetUnsafe (xs : CompactArray α) (i : USize)
    (_h : i.toNat < xs.size) : α :=
  let L : Layout ρ align := HasLayout.layout (α := α)
  DataRepr.fromRepr (L.uload xs.data (i * L.size.toUSize) lcProof)

/--
Retrieves the element at the indicated index.  Callers must prove that the index is in bounds.  The
index is represented by a platform-specific fixed-width integer (either 32 or 64 bits).

In compiled code, this is replaced by the more efficient `CompactArray.ugetUnsafe`.
-/
@[implemented_by ugetUnsafe]
def uget (xs : CompactArray α) (i : USize)
    (h : i.toNat < xs.size) : α :=
  let L : Layout ρ align := HasLayout.layout (α := α)
  DataRepr.fromRepr (L.load xs.data (i.toNat * L.size) (xs.slot_le_size h))

/-- Retrieves the element at the indicated index.  Panics if the index is out of bounds. -/
@[inline]
def get! [Inhabited α] (xs : @& CompactArray α) (i : @& Nat) : α :=
  if h : i < xs.size then
    let L : Layout ρ align := HasLayout.layout (α := α)
    DataRepr.fromRepr (L.load xs.data (i * L.size) (xs.slot_le_size h))
  else
    outOfBounds

/--
Retrieves the element at the indicated index.  Callers must prove that the index is in bounds.

Use `uget` for a more efficient alternative or `get!` for a variant that panics if the
index is out of bounds.
-/
@[inline]
def get (xs : CompactArray α) (i : @& Nat)
    (h : i < xs.size := by get_elem_tactic) : α :=
  let L : Layout ρ align := HasLayout.layout (α := α)
  DataRepr.fromRepr (L.load xs.data (i * L.size) (xs.slot_le_size h))

instance : GetElem (CompactArray α) Nat α fun xs i => i < xs.size where
  getElem xs i h := xs.get i h

instance : GetElem (CompactArray α) USize α
    fun xs i => i.toNat < xs.size where
  getElem xs i h := xs.uget i h

/-! ## `set` family -/

/--
Replaces the element at the given index.

No bounds check is performed, but the function requires a proof that the index is in bounds.  This
proof can usually be omitted, and will be synthesized automatically.
-/
@[inline]
def set (xs : CompactArray α) (i : @& Nat) (x : α)
    (h : i < xs.size := by get_elem_tactic) :
    CompactArray α :=
  let L : Layout ρ align := HasLayout.layout (α := α)
  { data := L.store xs.data (DataRepr.toRepr x) (i * L.size) (xs.slot_le_size h)
    size := xs.size
    size_data := by simp [L.size_store, xs.size_data]
    isCanonical j hj := by
      by_cases he : i = j
      · exact ⟨x, by simpa only [← he, L] using L.extract_store_self (x := DataRepr.toRepr x) (xs.slot_le_size h)⟩
      · obtain ⟨y, hy⟩ := xs.isCanonical j hj
        exact ⟨y, by
          rwa [L.extract_store_of_disjoint (xs.slot_le_size h) (xs.slot_le_size hj)
            (slot_disjoint_of_ne he)]⟩ }

/-- Replaces an element if the index is in bounds, and otherwise returns the original array. -/
@[inline]
def set! (xs : CompactArray α) (i : @& Nat) (x : α) : CompactArray α :=
  if h : i < xs.size then xs.set i x h else xs

/--
An efficient implementation of `CompactArray.uset` that computes the byte offset in `USize`
arithmetic and writes through `Layout.ustore`.

We claim this unsafe implementation is correct because an array cannot have more than
`USize.size` elements in our runtime.  This is similar to the `Array` version.
-/
@[inline]
unsafe def usetUnsafe (xs : CompactArray α) (i : USize) (x : α)
    (_h : i.toNat < xs.size) :
    CompactArray α :=
  let L : Layout ρ align := HasLayout.layout (α := α)
  { data := L.ustore xs.data (DataRepr.toRepr x) (i * L.size.toUSize) lcProof
    size := xs.size
    size_data := lcProof
    isCanonical := lcProof }

/--
Replaces the element at the given index.

No bounds check is performed, but the function requires a proof that the index is in bounds.  This
proof can usually be omitted, and will be synthesized automatically.

In compiled code, this is replaced by the more efficient `CompactArray.usetUnsafe`.
-/
@[implemented_by usetUnsafe]
def uset (xs : CompactArray α) (i : USize) (x : α)
    (h : i.toNat < xs.size) :
    CompactArray α :=
  xs.set i.toNat x h

/-! ## Hashing / `isEmpty` -/

/-- Computes a hash for a `CompactArray`. -/
protected def hash (xs : @& CompactArray α) : UInt64 :=
  ByteArray.hash xs.data

instance : Hashable (CompactArray α) where
  hash := CompactArray.hash

/-- Returns `true` when `xs` contains zero elements. -/
def isEmpty (xs : CompactArray α) : Bool :=
  xs.size == 0

/-! ## `copySlice` / `extract` / `append` -/

/--
Copies the elements with indices `b` (inclusive) to `e` (exclusive) to a new `CompactArray`.

Indices are *element* indices.
-/
def extract (xs : CompactArray α) (b e : Nat) :
    CompactArray α :=
  let L : Layout ρ align := HasLayout.layout (α := α)
  let data := xs.data.extract (b * L.size) (e * L.size)
  { data := data
    size := min e xs.size - b
    size_data := by
      show (xs.data.extract (b * L.size) (e * L.size)).size = (min e xs.size - b) * L.size
      rw [ByteArray.size_extract, xs.size_data, Nat.sub_mul, Nat.mul_min_mul_right]
    isCanonical i hi := by
      have hb : b + i < xs.size := by omega
      have he : b + i + 1 ≤ e := by omega
      have hmul := Nat.mul_le_mul_right L.size he
      obtain ⟨x, hx⟩ := xs.isCanonical (b + i) hb
      exact ⟨x, by
        change (xs.data.extract (b * L.size) (e * L.size)).extract
          (i * L.size) (i * L.size + L.size) = L.toBytes (DataRepr.toRepr x)
        rw [ByteArray.extract_extract,
          Nat.min_eq_left (by simpa [Nat.add_mul, Nat.add_assoc] using hmul)]
        simpa [L, Nat.add_mul, Nat.add_assoc] using hx⟩ }

/-- Appends two compact arrays. -/
protected def append (xs ys : CompactArray α) :
    CompactArray α where
  data := xs.data ++ ys.data
  size := xs.size + ys.size
  size_data := by simp [xs.size_data, ys.size_data, Nat.add_mul]
  isCanonical i hi := by
    let L := HasLayout.layout (α := α)
    by_cases h : i < xs.size
    · obtain ⟨x, hx⟩ := xs.isCanonical i h
      exact ⟨x, by rwa [ByteArray.extract_append_of_le (xs.slot_le_size h)]⟩
    · have hge : xs.size ≤ i := by omega
      have hb : i - xs.size < ys.size := by omega
      have hm := Nat.mul_le_mul_right L.size hge
      have hsub : i * L.size + L.size - xs.size * L.size =
          (i - xs.size) * L.size + L.size := by
        rw [Nat.sub_mul]
        omega
      obtain ⟨x, hx⟩ := ys.isCanonical (i - xs.size) hb
      exact ⟨x, by
        rw [ByteArray.extract_append_of_ge (by simpa [xs.size_data] using hm), xs.size_data]
        simpa only [← Nat.sub_mul, ← hsub, L] using hx⟩

instance : Append (CompactArray α) where
  append := CompactArray.append

@[simp]
theorem append_eq {xs ys : CompactArray α} :
    xs.append ys = xs ++ ys := rfl

/--
Copies an element range into another compact array, growing the destination when necessary.
Offsets are clamped to the corresponding array sizes.  When `exact` is false, capacity grows
geometrically.
-/
def copySlice (src : @& CompactArray α) (srcOff : Nat) (dest : CompactArray α)
    (destOff len : Nat) (exact : Bool := true) : CompactArray α :=
  let L := HasLayout.layout (α := α)
  let n := min len (src.size - srcOff)
  let spec := ((dest.extract 0 destOff).append (src.extract srcOff (srcOff + len))).append
    (dest.extract (destOff + n) dest.size)
  let data := src.data.copySlice (srcOff * L.size) dest.data (destOff * L.size)
    (len * L.size) exact
  have hdata : data = spec.data := by
    simp only [data, spec, CompactArray.append, extract, ByteArray.copySlice_eq_append,
      ByteArray.size_data, src.size_data, dest.size_data, L, Nat.zero_mul, Nat.add_mul,
      ← Nat.sub_mul, Nat.mul_min_mul_right, n]
  have hsize : spec.size = max dest.size (min destOff dest.size + n) := by
    change min destOff dest.size + (min (srcOff + len) src.size - srcOff) +
        (min dest.size dest.size - (destOff + n)) = _
    dsimp only [n]
    omega
  { data
    size := max dest.size (min destOff dest.size + n)
    size_data := by rw [hdata, spec.size_data, hsize]
    isCanonical i hi := by
      rw [hdata]
      exact spec.isCanonical i (by simpa [hsize] using hi) }

/-! ## `toList` -/

/-- Converts a packed array of elements to a linked list. -/
def toList (xs : CompactArray α) : List α :=
  List.ofFn fun i : Fin xs.size => xs[i.val]

/-! ## `findFinIdx?` / `findIdx?` -/

/--
Finds the index of the first element in `xs` for which `p` returns `true`.  If no element
in `xs` satisfies `p`, then the result is `none`.

The index is returned along with a proof that it is a valid index in the array.
-/
@[inline]
def findFinIdx? (xs : CompactArray α) (p : α → Bool)
    (start := 0) : Option (Fin xs.size) :=
  loop start
where
  loop (i : Nat) : Option (Fin xs.size) :=
    if h : i < xs.size then
      if p xs[i] then some ⟨i, h⟩ else loop (i + 1)
    else none
termination_by xs.size - i

/--
Finds the index of the first element in `xs` for which `p` returns `true`.  If no element
in `xs` satisfies `p`, then the result is `none`.

The variant `findFinIdx?` additionally returns a proof that the found index is in bounds.
-/
@[inline]
def findIdx? (xs : CompactArray α) (p : α → Bool)
    (start := 0) : Option Nat :=
  (xs.findFinIdx? p start).map Fin.val

/-! ## `forIn` / `foldl` -/

/--
An efficient implementation of `ForIn.forIn` for `CompactArray` that uses `USize`
rather than `Nat` for indices.

We claim this unsafe implementation is correct because an array cannot have more than
`USize.size` elements in our runtime.  This is similar to the `Array` version.
-/
@[inline]
unsafe def forInUnsafe [Monad m]
    (as : CompactArray α) (b : β)
    (f : α → β → m (ForInStep β)) : m β :=
  let sz := as.usize
  let rec @[specialize] loop (i : USize) (b : β) : m β := do
    if i < sz then
      let a := as.uget i lcProof
      match (← f a b) with
      | ForInStep.done  b => pure b
      | ForInStep.yield b => loop (i+1) b
    else
      pure b
  loop 0 b

/--
The reference implementation of `ForIn.forIn` for `CompactArray`.

In compiled code, this is replaced by the more efficient `CompactArray.forInUnsafe`.
-/
@[implemented_by CompactArray.forInUnsafe]
protected def forIn [Monad m]
    (as : CompactArray α) (b : β)
    (f : α → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      have h' : i < as.size := by omega
      have : as.size - 1 - i < as.size := by omega
      match (← f (as.get (as.size - 1 - i) this) b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop as.size (Nat.le_refl _) b

instance  [Monad m] :
    ForIn m (CompactArray α) α where
  forIn := CompactArray.forIn

/--
An efficient implementation of a monadic left fold on for `CompactArray` that uses `USize`
rather than `Nat` for indices.

We claim this unsafe implementation is correct because an array cannot have more than
`USize.size` elements in our runtime.  This is similar to the `Array` version.
-/
@[inline]
unsafe def foldlMUnsafe [Monad m]
    (f : β → α → m β) (init : β) (as : CompactArray α)
    (start := 0) (stop := as.size) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then
      pure b
    else
      fold (i+1) stop (← f b (as.uget i lcProof))
  if start < stop then
    if stop ≤ as.size then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else if start < as.size then
      fold (USize.ofNat start) (USize.ofNat as.size) init
    else
      pure init
  else
    pure init

/--
A monadic left fold on `CompactArray` that iterates over an array from low to high indices,
computing a running value.

Each element of the array is combined with the value from the prior elements using a monadic
function `f`.  The initial value `init` is the starting value before any elements have
been processed.
-/
@[implemented_by foldlMUnsafe]
def foldlM [Monad m]
    (f : β → α → m β) (init : β) (as : CompactArray α)
    (start := 0) (stop := as.size) : m β :=
  let fold (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (i : Nat) (j : Nat) (b : β) : m β := do
      if hlt : j < stop then
        match i with
        | 0    => pure b
        | i'+1 =>
          loop i' (j+1) (← f b (as.get j (Nat.lt_of_lt_of_le hlt h)))
      else
        pure b
    loop (stop - start) start init
  if h : stop ≤ as.size then
    fold stop h
  else
    fold as.size (Nat.le_refl _)

/--
A left fold on `CompactArray` that iterates over an array from low to high indices, computing a
running value.

Each element of the array is combined with the value from the prior elements using a function
`f`.  The initial value `init` is the starting value before any elements have been processed.

`CompactArray.foldlM` is a monadic variant of this function.
-/
@[inline]
def foldl (f : β → α → β) (init : β) (as : CompactArray α)
    (start := 0) (stop := as.size) : β :=
  Id.run <| as.foldlM (pure <| f · ·) init start stop

/-! ## Iterator -/

/--
Iterator over the elements (`α`) of a `CompactArray`.

Typically created by `arr.mkIterator`, where `arr` is a `CompactArray`.

An iterator is *valid* if the position `i` is *valid* for the array `arr`, meaning
`0 ≤ i ≤ arr.size`.

Most operations on iterators return arbitrary values if the iterator is not valid.  The functions in
the `CompactArray.Iterator` API should rule out the creation of invalid iterators, with two
exceptions:

- `Iterator.next iter` is invalid if `iter` is already at the end of the array (`iter.atEnd` is
  `true`)
- `Iterator.forward iter n`/`Iterator.nextn iter n` is invalid if `n` is strictly greater than the
  number of remaining elements.
-/
structure Iterator where
  /-- The array the iterator is for. -/
  array : CompactArray α
  /--
  The current position.

  This position is not necessarily valid for the array, for instance if one keeps calling
  `Iterator.next` when `Iterator.atEnd` is true.  If the position is not valid, then the
  current element is `(default : α)`.
  -/
  idx : Nat

instance : Inhabited (Iterator (α := α)) where
  default := ⟨empty, 0⟩

/-- Creates an iterator at the beginning of an array. -/
def mkIterator (arr : CompactArray α) :
    Iterator (α := α) :=
  ⟨arr, 0⟩

/-- The size of an array iterator is the number of elements remaining. -/
instance : SizeOf (Iterator (α := α)) where
  sizeOf i := i.array.size - i.idx

theorem Iterator.sizeOf_eq (i : Iterator (α := α)) :
    sizeOf i = i.array.size - i.idx := rfl

namespace Iterator

/-- The number of elements remaining in the iterator. -/
def remaining : Iterator (α := α) → Nat
  | ⟨arr, i⟩ => arr.size - i

@[inherit_doc Iterator.idx]
def pos := @Iterator.idx

/-- True if the iterator is past the array's last element. -/
@[inline]
def atEnd : Iterator (α := α) → Bool
  | ⟨arr, i⟩ => i ≥ arr.size

/--
The element at the current position.

On an invalid position, returns `(default : α)`.
-/
@[inline]
def curr [Inhabited α] : Iterator (α := α) → α
  | ⟨arr, i⟩ =>
    if h : i < arr.size then
      arr.get i h
    else
      default

/--
Moves the iterator's position forward by one element, unconditionally.

It is only valid to call this function if the iterator is not at the end of the array, *i.e.*
`Iterator.atEnd` is `false`; otherwise, the resulting iterator will be invalid.
-/
@[inline]
def next : Iterator (α := α) →
    Iterator (α := α)
  | ⟨arr, i⟩ => ⟨arr, i + 1⟩

/--
Decreases the iterator's position.

If the position is zero, this function is the identity.
-/
@[inline]
def prev : Iterator (α := α) →
    Iterator (α := α)
  | ⟨arr, i⟩ => ⟨arr, i - 1⟩

/-- True if the iterator is valid; that is, it is not past the array's last element. -/
@[inline]
def hasNext : Iterator (α := α) → Bool
  | ⟨arr, i⟩ => i < arr.size

/-- The element at the current position. -/
@[inline]
def curr' (it : Iterator (α := α)) (h : it.hasNext) : α :=
  match it with
  | ⟨arr, i⟩ =>
    have : i < arr.size := by
      simpa only [hasNext, decide_eq_true_eq] using h
    arr.get i this

/-- Moves the iterator's position forward by one element. -/
@[inline]
def next' (it : Iterator (α := α)) (_h : it.hasNext) :
    Iterator (α := α) :=
  match it with
  | ⟨arr, i⟩ => ⟨arr, i + 1⟩

/-- True if the position is not zero. -/
@[inline]
def hasPrev : Iterator (α := α) → Bool
  | ⟨_, i⟩ => i > 0

/--
Moves the iterator's position to the end of the array.

Given `i : CompactArray.Iterator`, note that `i.toEnd.atEnd` is always `true`.
-/
@[inline]
def toEnd : Iterator (α := α) →
    Iterator (α := α)
  | ⟨arr, _⟩ => ⟨arr, arr.size⟩

/--
Moves the iterator's position several elements forward.

The resulting iterator is only valid if the number of elements to skip is less than or equal to
the number of elements left in the iterator.
-/
@[inline]
def forward : Iterator (α := α) → Nat →
    Iterator (α := α)
  | ⟨arr, i⟩, f => ⟨arr, i + f⟩

@[inherit_doc forward, inline]
def nextn : Iterator (α := α) → Nat →
    Iterator (α := α) := forward

/--
Moves the iterator's position several elements back.

If asked to go back more elements than available, stops at the beginning of the array.
-/
@[inline]
def prevn : Iterator (α := α) → Nat →
    Iterator (α := α)
  | ⟨arr, i⟩, f => ⟨arr, i - f⟩

end Iterator

end CompactArray

end Transmog

end -- @[expose] public section
