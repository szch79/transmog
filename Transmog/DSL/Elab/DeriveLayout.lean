/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean.Elab.Command
public meta import Transmog.DSL.Elab.ElabRepr
public meta import Transmog.DSL.Elab.LayoutAlg
public import Transmog.DSL.Core.Layout
import Init.Data.Nat.Power2.Bitwise

/-!
# `derive_layout` elaboration

Assembly only: `toMode` validates the spec syntax into a `LayoutMode`, the chosen algorithm
produces a `PhysLayout`, and the emitter turns the entries into a `HasLayout` instance.

Everything about the physical layout is known here at elaboration time, so the exec and spec
functions are emitted *flat*: literal offsets, direct `getN`/`setN`/`extract` calls, explicit
zero-fill of gaps and tails, and the instance is a record literal.  The compiler can then reduce
the instance projections, inline the `@[inline]` definitions into specialized users
(`CompactArray`), and fuse away the repr tuples - none of which is possible when the instance
value is an opaque combinator composition behind a once-cell.

The combinator library from `Core/Layout.lean` still carries all the proof content, exactly
once: the combinator term survives as a noncomputable proof-only reference (`layoutRef`), four
bridge lemmas equate the flat definitions with the reference by a fixed normalization script
(the only mismatches are `Nat.add` reassociation of nested relative offsets, `extract`
recomposition, and degenerate zero-length padding operations), and the instance's laws are the
reference's laws transported through the bridges.
-/

meta section

namespace Transmog.DSL.DeriveLayout

open Lean Elab Command Transmog
open Transmog.DSL.LayoutAlg

/-! ## Layout spec to mode -/

def toMode : TSyntax ``transmogLayoutSpec → CommandElabM LayoutMode
  | `(transmogLayoutSpec| $ord:transmogLayoutOrder $al:transmogLayoutAlign) => do
    let order ←
      match ord with
      | `(transmogLayoutOrder| C) => pure SlotOrder.c
      | `(transmogLayoutOrder| auto) => pure SlotOrder.auto
      | _ => throwErrorAt ord "invalid layout order"
    let mode : LayoutMode ←
      match al with
      | `(transmogLayoutAlign| packed $[$cap?:num]?) => do
        let cap := cap?.map (·.getNat) |>.getD 1
        unless cap.isPowerOfTwo do
          throwErrorAt al "packed alignment cap must be a positive power of two"
        pure { order, fieldCap := some cap }
      | `(transmogLayoutAlign| align $n:num) => do
        unless n.getNat.isPowerOfTwo do
          throwErrorAt n "alignment must be a positive power of two"
        pure { order, structFloor := n.getNat }
      | _ => throwErrorAt al "invalid layout alignment"
    -- With every field alignment capped at 1 there is never padding, so reordering cannot save
    -- anything: a dead request, rejected loudly.
    if order == .auto && mode.fieldCap == some 1 then
      throwErrorAt ord
        "`auto` has no effect under `packed`: without alignment padding there \
          is nothing for reordering to save; use `C packed`"
    return mode
  | stx => throwErrorAt stx "invalid layout spec"

/-! ## Slot validation and physical view -/

/--
A slot is layoutable when its element type is a bare scalar or the range-induced `fitsBits`
subtype.  A custom `//` property has no canonical retraction (nothing rebuilds an arbitrary
predicate from raw bytes), so it is rejected here rather than silently mislaid out.
-/
def validateSlotSupported (slot : Slot) : CommandElabM Unit := do
  unless slot.userProps.isEmpty do
    throwErrorAt slot.name
      m!"cannot derive a layout for slot `{slot.name.getId}`: it carries a \
        custom `//` property, and decoding raw bytes cannot re-establish an \
        arbitrary predicate"

def toPhysSlots (slots : Array Slot) : Array PhysSlot :=
  slots.mapIdx fun i slot =>
    { idx := i, byteSize := slot.width / 8, natAlign := slot.width / 8 }

/--
Recheck the layout invariants the emitted `decide`s rely on, so an algorithm bug fails here
with the layout in hand instead of as an opaque `decide` failure.
-/
def validateLayout (phys : Array PhysSlot) (l : PhysLayout) :
    CommandElabM Unit := do
  let mut slotIdxs := #[]
  let mut cur := 0
  for e in l.entries do
    match e with
    | .slot idx =>
      let .some s := phys[idx]?
        | throwError "internal error: bad slot index in layout {reprStr l}"
      slotIdxs := slotIdxs.push idx
      cur := cur + s.byteSize
    | .pad n =>
      unless n > 0 do
        throwError "internal error: empty padding in layout {reprStr l}"
      cur := cur + n
  unless slotIdxs.toList.mergeSort (· ≤ ·) == List.range phys.size do
    throwError "internal error: malformed layout {reprStr l}"
  unless cur == l.size && l.size % l.align == 0 && decide l.align.isPowerOfTwo do
    throwError "internal error: mis-padded layout {reprStr l}"

/-! ## Term assembly -/

/--
The primitive codec for one slot: the bare scalar, or the masked subtype codec when the slot
carries a bit range.
-/
def mkSlotLayout (slot : Slot) : CommandElabM Term := do
  match slot.range? with
  | .none =>
    match slot.width with
    | 8 => `(Layout.uint8)
    | 16 => `(Layout.uint16)
    | 32 => `(Layout.uint32)
    | 64 => `(Layout.uint64)
    | w => throwError "internal error: unexpected slot width {w}"
  | .some range =>
    let w := Syntax.mkNatLit (range.stop - range.start)
    match slot.width with
    | 8 => `(Layout.fits8 $w:num (by decide))
    | 16 => `(Layout.fits16 $w:num (by decide))
    | 32 => `(Layout.fits32 $w:num (by decide))
    | 64 => `(Layout.fits64 $w:num (by decide))
    | w => throwError "internal error: unexpected slot width {w}"

/--
Fold the placed slots into a right-nested `prodAt` chain (relative offsets; padding entries
have already widened the gaps), then `pad` to the layout's size and alignment exponent.
-/
def mkPhysTerm (slots : Array Slot) (l : PhysLayout)
    (placed : Array (Nat × Nat)) : CommandElabM Term := do
  let n := placed.size
  let mut term ← mkSlotLayout slots[(placed[n - 1]!).1]!
  for i in [1:n] do
    let j := n - 1 - i
    let (idx, off) := placed[j]!
    let outer ← mkSlotLayout slots[idx]!
    let relOff := Syntax.mkNatLit ((placed[j + 1]!).2 - off)
    term ← `(($outer).prodAt $term $relOff:num (by decide))
  let size := Syntax.mkNatLit l.size
  let k := Syntax.mkNatLit l.align.log2
  `(($term).pad $size:num $k:num (by decide) (by decide))

/--
Wrap the physical layout in the reorder retract when the mode shuffled the slots (`perm`
maps physical position to declared index): the section/retraction are tuple shuffles, and `Prod`
eta makes the round trip `rfl`.
-/
def mkReorderRetract (perm : Array Nat) (physTerm : Term) : CommandElabM Term := do
  let n := perm.size
  if perm == Array.range n then
    return physTerm
  -- `f : declared → physical` picks component `perm[p]` for position `p`.
  let x := mkIdent (← liftCoreM <| mkFreshUserName `x)
  let fComps ← perm.mapM fun idx => ElabRepr.mkProdProj x idx n
  let fTup ← ElabRepr.mkTuple fComps
  -- `g : physical → declared` picks, for declared index `i`, the physical position holding it.
  let y := mkIdent (← liftCoreM <| mkFreshUserName `y)
  let mut pos : Array Nat := .replicate n 0
  for p in [0:n] do
    pos := pos.set! perm[p]! p
  let gComps ← pos.mapM fun p => ElabRepr.mkProdProj y p n
  let gTup ← ElabRepr.mkTuple gComps
  `(($physTerm).ofRetract (fun $x:ident => $fTup) (fun $y:ident => $gTup)
      (fun _ => rfl))

/-! ## Flat emission: names -/

/--
The names of the flat layout package emitted per type, all under the same generated
namespace as the `DataRepr` package (`α.Repr.store` etc.).
-/
structure FlatNames where
  layoutRef : Ident
  store : Ident
  load : Ident
  ustore : Ident
  uload : Ident
  ustoreImpl : Ident
  uloadImpl : Ident
  toBytes : Ident
  fromBytes : Ident
  storeEqRef : Ident
  loadEqRef : Ident
  toBytesEqRef : Ident
  fromBytesEqRef : Ident

def mkFlatNames (ctx : ElabRepr.Context) : FlatNames :=
  { layoutRef := ctx.member `layoutRef
    store := ctx.member `store
    load := ctx.member `load
    ustore := ctx.member `ustore
    uload := ctx.member `uload
    ustoreImpl := ctx.member `ustoreImpl
    uloadImpl := ctx.member `uloadImpl
    toBytes := ctx.member `toBytes
    fromBytes := ctx.member `fromBytes
    storeEqRef := ctx.member `store_eq_ref
    loadEqRef := ctx.member `load_eq_ref
    toBytesEqRef := ctx.member `toBytes_eq_ref
    fromBytesEqRef := ctx.member `fromBytes_eq_ref }

/-! ## Flat emission: bodies -/

/--
`off + o` with a literal `o`, in the same normal form the bridge simp produces from the
combinators' nested relative offsets (bare `off` when `o = 0`).
-/
def mkOffset (off : Ident) (o : Nat) : CommandElabM Term := do
  if o == 0 then
    `($off:ident)
  else
    `($off:ident + $(Syntax.mkNatLit o):num)

/--
Wrap a raw scalar read into the range-induced `fitsBits` subtype, mirroring the `fitsN`
retraction of the combinator reference (same normalization by `extractSlice 0 w`, same fitting
lemma), so the bridge closes by beta reduction and proof irrelevance alone.
-/
def mkFitsWrap (slot : Slot) (raw : Term) : CommandElabM Term := do
  match slot.range? with
  | .none => return raw
  | .some range =>
    let w := Syntax.mkNatLit (range.stop - range.start)
    let fitsLem := mkCIdent (slot.ty ++ `fitsBits_extractSlice)
    `(⟨($raw).extractSlice 0 $w:num,
        $fitsLem ($(mkCIdent ``Nat.sub_zero) $w:num).symm (by decide) (by decide) $raw⟩)

/--
The exec read of one slot at absolute offset `o`, matching the corresponding scalar
codec's `load` primitive.
-/
def mkReader (bs off : Ident) (slot : Slot) (o : Nat) : CommandElabM Term := do
  let idx ← mkOffset off o
  let raw : Term ← match slot.width with
    | 8 => `(($bs:ident)[$idx]'(by omega))
    | 16 => `(($bs:ident).get16 $idx (by omega))
    | 32 => `(($bs:ident).get32 $idx (by omega))
    | 64 => `(($bs:ident).get64 $idx (by omega))
    | w => throwError "internal error: unexpected slot width {w}"
  mkFitsWrap slot raw

/-- `load` body: the declared-order tuple of flat reads at absolute offsets. -/
def mkFlatLoadBody (bs off : Ident) (slots : Array Slot) (offs : Array Nat) :
    CommandElabM Term := do
  let comps ← slots.mapIdxM fun i slot => mkReader bs off slot offs[i]!
  ElabRepr.mkTuple comps

/--
`store` body: a left-to-right fold over the physical entries starting from `bs` - slot
writes at literal offsets interleaved with explicit zero-fill of gaps and the tail, in exactly
the operational order of the combinator composition.  Bound side goals after the first write
rewrite the accumulated size back to `bs.size` before `omega`.
-/
def mkFlatStoreBody (bs x off : Ident) (slots : Array Slot) (l : PhysLayout) :
    CommandElabM Term := do
  let n := slots.size
  let mut acc : Term ← `($bs:ident)
  let mut cur := 0
  let mut first := true
  for e in l.entries do
    match e with
    | .slot idx =>
      let slot := slots[idx]!
      let mut v ← ElabRepr.mkProdProj (← `($x:ident)) idx n
      if slot.range?.isSome then
        v ← `(($v).val)
      let bound : Term ←
        if first then
          `((by omega))
        else
          `((by
              simp only [$(mkCIdent ``ByteArray.size_set):term,
                $(mkCIdent ``ByteArray.size_set16):term,
                $(mkCIdent ``ByteArray.size_set32):term,
                $(mkCIdent ``ByteArray.size_set64):term,
                $(mkCIdent ``ByteArray.size_setZeros):term]
              omega))
      let idxT ← mkOffset off cur
      acc ← match slot.width with
        | 8 => `(($acc).set $idxT $v $bound)
        | 16 => `(($acc).set16 $idxT $v $bound)
        | 32 => `(($acc).set32 $idxT $v $bound)
        | 64 => `(($acc).set64 $idxT $v $bound)
        | w => throwError "internal error: unexpected slot width {w}"
      first := false
      cur := cur + slot.width / 8
    | .pad m =>
      acc ← `(($acc).setZeros $(← mkOffset off cur) $(Syntax.mkNatLit m):num)
      cur := cur + m
  return acc

/--
`toBytes` body: the `++` chain of serialized slots and literal zero padding, in physical
order.
-/
def mkFlatToBytesBody (x : Ident) (slots : Array Slot) (l : PhysLayout) :
    CommandElabM Term := do
  let n := slots.size
  let mut acc? : Option Term := none
  for e in l.entries do
    let piece : Term ← match e with
      | .slot idx => do
        let slot := slots[idx]!
        let mut v ← ElabRepr.mkProdProj (← `($x:ident)) idx n
        if slot.range?.isSome then
          v ← `(($v).val)
        `(($v).toLEBytes)
      | .pad m => `(ByteArray.replicate $(Syntax.mkNatLit m):num 0)
    acc? := some (← match acc? with
      | .none => pure piece
      | .some acc => `($acc ++ $piece))
  let .some body := acc? | throwError "internal error: empty layout"
  return body

/-- `fromBytes` body: the declared-order tuple of deserialized windows at absolute offsets. -/
def mkFlatFromBytesBody (bs : Ident) (slots : Array Slot) (offs : Array Nat) :
    CommandElabM Term := do
  let comps ← slots.mapIdxM fun i slot => do
    let o := offs[i]!
    let ofLE := mkCIdent (slot.ty ++ `ofLEBytes)
    let raw ← `($ofLE (($bs:ident).extract $(Syntax.mkNatLit o):num
      $(Syntax.mkNatLit (o + slot.width / 8)):num))
    mkFitsWrap slot raw
  ElabRepr.mkTuple comps

/-!
## Flat emission: `USize` exec bodies

The `USize` twins do genuine `USize` offset arithmetic through the `ugetN`/`usetN` FFI
primitives.  They are `unsafe` (all bound obligations are `lcProof`): `bs.size < USize.size` is
a runtime fact, not a theorem, so the in-range additions cannot be proven non-wrapping.  The
safe models forward to the `Nat` exec path and carry the `implemented_by` attribute, exactly
like core's `forInUnsafe` pattern.
-/

/-- The `USize` exec read of one slot at absolute offset `o`. -/
def mkUReader (bs off : Ident) (slot : Slot) (o : Nat) : CommandElabM Term := do
  let idx ← mkOffset off o
  let lc := mkCIdent ``lcProof
  let raw : Term ← match slot.width with
    | 8 => `(($bs:ident).uget $idx $lc)
    | 16 => `(($bs:ident).uget16 $idx $lc)
    | 32 => `(($bs:ident).uget32 $idx $lc)
    | 64 => `(($bs:ident).uget64 $idx $lc)
    | w => throwError "internal error: unexpected slot width {w}"
  mkFitsWrap slot raw

/-- `uloadImpl` body: the declared-order tuple of `USize`-offset reads. -/
def mkFlatULoadBody (bs off : Ident) (slots : Array Slot) (offs : Array Nat) :
    CommandElabM Term := do
  let comps ← slots.mapIdxM fun i slot => mkUReader bs off slot offs[i]!
  ElabRepr.mkTuple comps

/--
`ustoreImpl` body: the write fold of `mkFlatStoreBody` with `USize`-offset writes; gap and
tail zero-fill drops to the `Nat` `setZeros` at the converted offset.
-/
def mkFlatUStoreBody (bs x off : Ident) (slots : Array Slot) (l : PhysLayout) :
    CommandElabM Term := do
  let n := slots.size
  let lc := mkCIdent ``lcProof
  let mut acc : Term ← `($bs:ident)
  let mut cur := 0
  for e in l.entries do
    match e with
    | .slot idx =>
      let slot := slots[idx]!
      let mut v ← ElabRepr.mkProdProj (← `($x:ident)) idx n
      if slot.range?.isSome then
        v ← `(($v).val)
      let idxT ← mkOffset off cur
      acc ← match slot.width with
        | 8 => `(($acc).uset $idxT $v $lc)
        | 16 => `(($acc).uset16 $idxT $v $lc)
        | 32 => `(($acc).uset32 $idxT $v $lc)
        | 64 => `(($acc).uset64 $idxT $v $lc)
        | w => throwError "internal error: unexpected slot width {w}"
      cur := cur + slot.width / 8
    | .pad m =>
      acc ← `(($acc).setZeros ($(← mkOffset off cur)).toNat $(Syntax.mkNatLit m):num)
      cur := cur + m
  return acc

/-! ## Flat emission: bridges to the combinator reference -/

/--
The fixed normalization script equating a flat definition with the corresponding field of
`layoutRef`: `simp only` with the closed `transmog_bridge` set (whose manifest in
`Transmog/DSL/Core/Layout.lean` carries the combinator unfoldings and the splice/arithmetic
algebra) plus the two per-type definitions.  Emitted proofs never consult the ambient default
simp set, so downstream `@[simp]` churn cannot break `derive_layout` at user sites.
Proof-valued arguments differ only proof-irrelevantly.
-/
def mkBridgeTactic (names : FlatNames) (flatName : Ident) : CommandElabM (TSyntax `tactic) := do
  -- The literal-arithmetic simprocs ride along by name: builtin simprocs cannot be tagged into
  -- a custom simp set from downstream (the attribute requires a `meta` declaration).
  let args : Array Term := #[mkIdent `transmog_bridge, flatName, names.layoutRef,
    mkCIdent ``Nat.reduceAdd, mkCIdent ``Nat.reduceSub, mkCIdent ``Nat.reduceLeDiff,
    mkCIdent ``reduceIte]
  `(tactic| simp only [$[$args:term],*])

/-! ## Entrance -/

public def elabDeriveLayout (ctx : ElabRepr.Context) (ref : Syntax)
    (specs : Array (TSyntax ``transmogLayoutSpec)) : CommandElabM Unit := do
  unless specs.size == 1 do
    throwErrorAt ref
      "`derive_layout` supports exactly one layout spec for now: only one \
        `HasLayout` instance can exist per type"
  let mode ← toMode specs[0]!
  let slots := ctx.decl.slots
  for slot in slots do
    validateSlotSupported slot
  let phys := toPhysSlots slots
  let layout := computeLayout mode phys
  validateLayout phys layout
  let placed := layout.placements phys
  let layoutTerm ←
    mkReorderRetract (placed.map (·.1)) (← mkPhysTerm slots layout placed)
  let k := Syntax.mkNatLit layout.align.log2
  let size := Syntax.mkNatLit layout.size
  let names := mkFlatNames ctx
  let reprTy := ctx.reprTy
  -- Declared index to absolute byte offset.
  let mut offs : Array Nat := .replicate slots.size 0
  for (idx, o) in placed do
    offs := offs.set! idx o
  -- The proof-only combinator reference: never compiled, carries the laws.
  elabCommand <| ← `(
    @[expose] noncomputable def $names.layoutRef : Layout ($reprTy) $k:num := $layoutTerm)
  -- The four flat definitions.  The binders keep plain names, as `casesOn` keeps `motive` and
  -- `t`, since they are the names readers see in the signatures of `load` and `store`; the bodies
  -- splice generated terms only, so no user term can capture them.
  let bs := mkIdent `bs
  let x := mkIdent `x
  let off := mkIdent `off
  let h := mkIdent `h
  let loadBody ← mkFlatLoadBody bs off slots offs
  let storeBody ← mkFlatStoreBody bs x off slots layout
  let toBytesBody ← mkFlatToBytesBody x slots layout
  let fromBytesBody ← mkFlatFromBytesBody bs slots offs
  elabCommand <| ← `(
    @[inline, expose] def $names.load ($bs:ident : ByteArray) ($off:ident : Nat)
        ($h:ident : $off:ident + $size:num ≤ ($bs:ident).size) : $reprTy :=
      $loadBody
    @[inline, expose] def $names.store ($bs:ident : ByteArray) ($x:ident : $reprTy)
        ($off:ident : Nat) ($h:ident : $off:ident + $size:num ≤ ($bs:ident).size) : ByteArray :=
      $storeBody
    @[inline, expose] def $names.toBytes ($x:ident : $reprTy) : ByteArray :=
      $toBytesBody
    @[inline, expose] def $names.fromBytes ($bs:ident : ByteArray) : $reprTy :=
      $fromBytesBody)
  -- The `USize` exec twins: unsafe impls behind safe `Nat`-forwarding models.
  let uloadBody ← mkFlatULoadBody bs off slots offs
  let ustoreBody ← mkFlatUStoreBody bs x off slots layout
  elabCommand <| ← `(
    @[inline] unsafe def $names.uloadImpl ($bs:ident : ByteArray) ($off:ident : USize)
        ($h:ident : ($off:ident).toNat + $size:num ≤ ($bs:ident).size) : $reprTy :=
      $uloadBody
    @[inline] unsafe def $names.ustoreImpl ($bs:ident : ByteArray) ($x:ident : $reprTy)
        ($off:ident : USize) ($h:ident : ($off:ident).toNat + $size:num ≤ ($bs:ident).size) :
        ByteArray :=
      $ustoreBody
    @[implemented_by $names.uloadImpl, expose]
    def $names.uload ($bs:ident : ByteArray) ($off:ident : USize)
        ($h:ident : ($off:ident).toNat + $size:num ≤ ($bs:ident).size) : $reprTy :=
      $names.load $bs:ident ($off:ident).toNat $h:ident
    @[implemented_by $names.ustoreImpl, expose]
    def $names.ustore ($bs:ident : ByteArray) ($x:ident : $reprTy) ($off:ident : USize)
        ($h:ident : ($off:ident).toNat + $size:num ≤ ($bs:ident).size) : ByteArray :=
      $names.store $bs:ident $x:ident ($off:ident).toNat $h:ident)
  -- The four bridge lemmas.
  elabCommand <| ← `(
    theorem $names.loadEqRef ($bs:ident : ByteArray) ($off:ident : Nat)
        ($h:ident : $off:ident + $size:num ≤ ($bs:ident).size) :
        $names.load $bs:ident $off:ident $h:ident =
          ($names.layoutRef).load $bs:ident $off:ident $h:ident := by
      $(← mkBridgeTactic names names.load):tactic
    theorem $names.storeEqRef ($bs:ident : ByteArray) ($x:ident : $reprTy)
        ($off:ident : Nat) ($h:ident : $off:ident + $size:num ≤ ($bs:ident).size) :
        $names.store $bs:ident $x:ident $off:ident $h:ident =
          ($names.layoutRef).store $bs:ident $x:ident $off:ident $h:ident := by
      $(← mkBridgeTactic names names.store):tactic
    theorem $names.toBytesEqRef ($x:ident : $reprTy) :
        $names.toBytes $x:ident = ($names.layoutRef).toBytes $x:ident := by
      $(← mkBridgeTactic names names.toBytes):tactic
    theorem $names.fromBytesEqRef ($bs:ident : ByteArray) :
        $names.fromBytes $bs:ident = ($names.layoutRef).fromBytes $bs:ident := by
      $(← mkBridgeTactic names names.fromBytes):tactic)
  -- The record-literal instance: literal size, flat exec/spec fields, transported laws.
  elabCommand <| ← `(
    instance : HasLayout $(ctx.sourceTy) ($reprTy) $k:num :=
      ⟨{ size := $size:num
         size_pos := by decide
         size_align := by decide
         toBytes := $names.toBytes
         fromBytes := $names.fromBytes
         store := $names.store
         load := $names.load
         ustore := $names.ustore
         uload := $names.uload
         ustore_eq_store := fun _ _ _ _ => rfl
         uload_eq_load := fun _ _ _ => rfl
         size_toBytes := fun x => by
           rw [$names.toBytesEqRef:term]
           exact ($names.layoutRef).size_toBytes x
         fromBytes_toBytes := fun x => by
           rw [$names.fromBytesEqRef:term, $names.toBytesEqRef:term]
           exact ($names.layoutRef).fromBytes_toBytes x
         store_eq_append := fun bs x off h => by
           rw [$names.storeEqRef:term, $names.toBytesEqRef:term]
           exact ($names.layoutRef).store_eq_append bs x off h
         load_eq_extract := fun bs off h => by
           rw [$names.loadEqRef:term, $names.fromBytesEqRef:term]
           exact ($names.layoutRef).load_eq_extract bs off h }⟩)

end Transmog.DSL.DeriveLayout

end -- meta section
