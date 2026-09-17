/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Transmog.Init
meta import Lean.Parser.Attr

/-!
# Extra `ByteArray` operations

Fixed-width scalar get/set/push operations for `ByteArray`, with FFI fast paths, together with
the byte-fill operations (`replicate`, `setZeros`) and the little-endian scalar codecs
(`toLEBytes`/`ofLEBytes`) that serve as their specifications.

Scalar operations use little-endian byte order on every target.  Offsets and lengths are in bytes.
-/

@[expose] public section

/-- Returns the `i`th little-endian byte, or zero when `i ≥ 2`. -/
def UInt16.byte (v : UInt16) : Nat → UInt8
  | 0 => v.toUInt8
  | 1 => (v >>> 8).toUInt8
  | _ => 0

/-- Returns the `i`th little-endian byte, or zero when `i ≥ 4`. -/
def UInt32.byte (v : UInt32) : Nat → UInt8
  | 0 => v.toUInt8
  | 1 => (v >>> 8).toUInt8
  | 2 => (v >>> 16).toUInt8
  | 3 => (v >>> 24).toUInt8
  | _ => 0

/-- Returns the `i`th little-endian byte, or zero when `i ≥ 8`. -/
def UInt64.byte (v : UInt64) : Nat → UInt8
  | 0 => v.toUInt8
  | 1 => (v >>> 8).toUInt8
  | 2 => (v >>> 16).toUInt8
  | 3 => (v >>> 24).toUInt8
  | 4 => (v >>> 32).toUInt8
  | 5 => (v >>> 40).toUInt8
  | 6 => (v >>> 48).toUInt8
  | 7 => (v >>> 56).toUInt8
  | _ => 0

namespace ByteArray

/-- Creates a byte array that contains `n` copies of `v`. -/
def replicate (n : Nat) (v : UInt8) : ByteArray :=
  ⟨Array.replicate n v⟩

/-- Writes `n` consecutive bytes at offset `i`, without checking the full range first. -/
def setBytesUnchecked! (bs : ByteArray) (i n : Nat) (byte : Nat → UInt8) : ByteArray :=
  match n with
  | 0 => bs
  | n + 1 => (bs.setBytesUnchecked! i n byte).set! (i + n) (byte n)

/-- Writes `n` consecutive bytes at offset `i`, leaving the array unchanged if they do not fit. -/
def setBytes! (bs : ByteArray) (i n : Nat) (byte : Nat → UInt8) : ByteArray :=
  if i + n ≤ bs.size then
    bs.setBytesUnchecked! i n byte
  else
    bs

/-- Appends `n` consecutive bytes. -/
def pushBytes (bs : ByteArray) (n : Nat) (byte : Nat → UInt8) : ByteArray :=
  match n with
  | 0 => bs
  | n + 1 => (bs.pushBytes n byte).push (byte n)

/--
Zero-fills the bytes in `[i, i + n)`; the executable counterpart of splicing
`replicate n 0`.
-/
def setZeros (bs : ByteArray) (i n : Nat) : ByteArray :=
  bs.setBytesUnchecked! i n fun _ => 0

open Lean in
set_option hygiene false in
local macro "declare_bytearray_uint_ops" suffix:num typeName:ident width:num boundSub:num : command => do
  let some suffixNat := suffix.raw.isNatLit? | Macro.throwError "expected UInt suffix"
  let some widthNat := width.raw.isNatLit? | Macro.throwError "expected byte width"
  let toUInt := mkIdentFrom suffix.raw (.mkSimple s!"toUInt{suffixNat}")
  let mkLocal (s : String) := mkIdentFrom suffix.raw (.mkSimple s)
  let mkExtern (name : String) : MacroM (TSyntax `Lean.Parser.Attr.externEntry) := do
    let s : TSyntax `str := ⟨Syntax.mkStrLit name⟩
    `(Lean.Parser.Attr.externEntry| $s:str)
  let mkInline (code : String) : MacroM (TSyntax `Lean.Parser.Attr.externEntry) := do
    let s : TSyntax `str := ⟨Syntax.mkStrLit code⟩
    `(Lean.Parser.Attr.externEntry| c inline $s:str)
  let mkDoc (body : String) : TSyntax ``Parser.Command.docComment :=
    ⟨mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (body ++ " -/")]⟩
  let bytes := s!"{widthNat} bytes"
  let scalar := s!"little-endian `{typeName.getId}`"
  let inPlace := "The array is modified in place if there are no other references to it."
  let ugetDoc := mkDoc s!"Reads the {scalar} stored in the {bytes} at offset `i`.  Callers must \
    prove that the bytes are in bounds.  The offset is represented by a platform-specific \
    fixed-width integer."
  let getBangDoc := mkDoc s!"Reads the {scalar} stored in the {bytes} at offset `i`, or returns \
    `0` when the bytes are not in bounds."
  let getDoc := mkDoc s!"Reads the {scalar} stored in the {bytes} at offset `i`.  Callers must \
    prove that the bytes are in bounds.\n\nUse `uget{suffixNat}` for a more efficient \
    alternative or `get{suffixNat}!` for a variant that tolerates offsets out of bounds."
  let setBangDoc := mkDoc s!"Writes `v` as {bytes} in little-endian order at offset `i`.  \
    {inPlace}\n\nIf the bytes are not in bounds, the array is returned unmodified."
  let setDoc := mkDoc s!"Writes `v` as {bytes} in little-endian order at offset `i`.  No \
    bounds check is performed, but the function requires a proof that the bytes are in bounds.  \
    This proof can usually be omitted, and will be synthesized automatically.\n\n{inPlace}"
  let pushDoc := mkDoc s!"Appends `v` as {bytes} in little-endian order.  {inPlace}"
  let readCode (offset : String) : String :=
    let parts := (List.range widthNat).map fun j =>
      s!"((uint{suffixNat}_t)lean_sarray_cptr(#1)[({offset}) + {j}] << {8 * j})"
    s!"((uint{suffixNat}_t)({" | ".intercalate parts}))"
  let writeCode (offset : String) : String :=
    let writes := (List.range widthNat).map fun j =>
      s!"lean_sarray_cptr(transmog_data)[({offset}) + {j}] = (uint8_t)(#3 >> {8 * j});"
    "({ lean_object *transmog_data = lean_sarray_ensure_exclusive(#1); " ++
      " ".intercalate writes ++ " transmog_data; })"
  let fits := "(lean_is_scalar(#2) && lean_unbox(#2) <= lean_sarray_size(#1) && " ++
    s!"{widthNat} <= lean_sarray_size(#1) - lean_unbox(#2))"
  let mkRead (bs : Ident) (base : Term) : MacroM Term := do
    let mut acc? := none
    for k in [0:widthNat] do
      let idx : Term ← if k == 0 then
        pure base
      else
        let kStx : TSyntax `num := ⟨Syntax.mkNumLit (toString k)⟩
        `($base + $kStx:num)
      let byte ← `(($bs:ident[$idx]'(by get_elem_tactic)).$toUInt:ident)
      let term ← if k == 0 then
        pure byte
      else
        let shift : TSyntax `num := ⟨Syntax.mkNumLit (toString (8 * k))⟩
        `(($byte) <<< $shift:num)
      acc? ← match acc? with
        | none => pure (some term)
        | some acc => pure (some (← `($acc ||| $term)))
    match acc? with
    | some acc => pure acc
    | none => Macro.throwError "zero byte width"
  let bs := mkIdentFrom suffix.raw (.mkSimple "bs")
  let read ← mkRead bs ⟨mkIdentFrom suffix.raw (.mkSimple "i")⟩
  let uread ← mkRead bs (← `(i.toNat))
  let ugetExtern ← mkInline (readCode "#2")
  let getBangExtern ← mkInline s!"({fits} ? {readCode "lean_unbox(#2)"} : 0)"
  let getExtern ← mkInline (readCode "lean_unbox(#2)")
  let setBangExtern ← mkInline s!"({fits} ? {writeCode "lean_unbox(#2)"} : #1)"
  let setExtern ← mkInline (writeCode "lean_unbox(#2)")
  let usetExtern ← mkInline (writeCode "#2")
  let pushExtern ← mkExtern s!"lean_byte_array_push{suffixNat}"
  let uget := mkLocal s!"uget{suffixNat}"
  let getBang := mkLocal s!"get{suffixNat}!"
  let get := mkLocal s!"get{suffixNat}"
  let setBang := mkLocal s!"set{suffixNat}!"
  let set := mkLocal s!"set{suffixNat}"
  let uset := mkLocal s!"uset{suffixNat}"
  let push := mkLocal s!"push{suffixNat}"
  `(
    $ugetDoc:docComment
    @[extern $ugetExtern]
    def $uget (bs : @& ByteArray) (i : USize)
        (h : i.toNat < bs.size - $boundSub := by get_elem_tactic) : $typeName :=
      $uread

    $getBangDoc:docComment
    @[extern $getBangExtern]
    def $getBang (bs : @& ByteArray) (i : @& Nat) : $typeName :=
      if h : i < bs.size - $boundSub then
        $read
      else
        default

    $getDoc:docComment
    @[extern $getExtern]
    def $get (bs : @& ByteArray) (i : @& Nat)
        (h : i < bs.size - $boundSub := by get_elem_tactic) : $typeName :=
      $read

    $setBangDoc:docComment
    @[extern $setBangExtern]
    def $setBang (bs : ByteArray) (i : @& Nat) (v : $typeName) : ByteArray :=
      bs.setBytes! i $width v.byte

    $setDoc:docComment
    @[extern $setExtern]
    def $set (bs : ByteArray) (i : @& Nat) (v : $typeName)
        (h : i < bs.size - $boundSub := by get_elem_tactic) : ByteArray :=
      bs.setBytesUnchecked! i $width v.byte

    @[extern $usetExtern, inherit_doc $set]
    def $uset (bs : ByteArray) (i : USize) (v : $typeName)
        (h : i.toNat < bs.size - $boundSub := by get_elem_tactic) : ByteArray :=
      bs.setBytesUnchecked! i.toNat $width v.byte

    $pushDoc:docComment
    @[extern $pushExtern]
    def $push (bs : ByteArray) (v : $typeName) : ByteArray :=
      bs.pushBytes $width v.byte)

declare_bytearray_uint_ops 16 UInt16 2 1
declare_bytearray_uint_ops 32 UInt32 4 3
declare_bytearray_uint_ops 64 UInt64 8 7

end ByteArray

/-!
## Little-endian scalar codec specifications

`toLEBytes` materializes a scalar as its little-endian bytes and `ofLEBytes` reads it back
(total, masking out-of-range reads to `default`).  These are the specification counterparts of
the fast `setN`/`getN` operations above.
-/

/-- The little-endian byte serialization of a `UInt8`. -/
def UInt8.toLEBytes (v : UInt8) : ByteArray :=
  [v].toByteArray

/-- The little-endian byte serialization of a `UInt16`. -/
def UInt16.toLEBytes (v : UInt16) : ByteArray :=
  ByteArray.empty.pushBytes 2 v.byte

/-- The little-endian byte serialization of a `UInt32`. -/
def UInt32.toLEBytes (v : UInt32) : ByteArray :=
  ByteArray.empty.pushBytes 4 v.byte

/-- The little-endian byte serialization of a `UInt64`. -/
def UInt64.toLEBytes (v : UInt64) : ByteArray :=
  ByteArray.empty.pushBytes 8 v.byte

/-- Reads the first 1 bytes in little-endian order, treating missing bytes as zero. -/
def UInt8.ofLEBytes (bs : ByteArray) : UInt8 :=
  (bs[0]?.getD 0)

/-- Reads the first 2 bytes in little-endian order, treating missing bytes as zero. -/
def UInt16.ofLEBytes (bs : ByteArray) : UInt16 :=
  (bs[0]?.getD 0).toUInt16 ||| ((bs[1]?.getD 0).toUInt16 <<< (8 : UInt16))

/-- Reads the first 4 bytes in little-endian order, treating missing bytes as zero. -/
def UInt32.ofLEBytes (bs : ByteArray) : UInt32 :=
  (bs[0]?.getD 0).toUInt32 ||| ((bs[1]?.getD 0).toUInt32 <<< (8 : UInt32)) ||| ((bs[2]?.getD 0).toUInt32 <<< (16 : UInt32)) |||
    ((bs[3]?.getD 0).toUInt32 <<< (24 : UInt32))

/-- Reads the first 8 bytes in little-endian order, treating missing bytes as zero. -/
def UInt64.ofLEBytes (bs : ByteArray) : UInt64 :=
  (bs[0]?.getD 0).toUInt64 ||| ((bs[1]?.getD 0).toUInt64 <<< (8 : UInt64)) ||| ((bs[2]?.getD 0).toUInt64 <<< (16 : UInt64)) |||
    ((bs[3]?.getD 0).toUInt64 <<< (24 : UInt64)) ||| ((bs[4]?.getD 0).toUInt64 <<< (32 : UInt64)) ||| ((bs[5]?.getD 0).toUInt64 <<< (40 : UInt64)) |||
    ((bs[6]?.getD 0).toUInt64 <<< (48 : UInt64)) ||| ((bs[7]?.getD 0).toUInt64 <<< (56 : UInt64))

end -- @[expose] public section
