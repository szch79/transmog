/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

import TransmogTest.Layout.Derive
import TransmogTest.RuntimeRepr.Probes

/-!
# Native checks

What only compiled code can establish: the inline C scalar operations as the C compiler sees
them, and the word-backed values under the native reference counting, where an operation
emitted on a boxed word would crash rather than fail a check.
-/

-- Executable tests deliberately use concrete examples and diagnostic labels.
set_option linter.hazel false

open Transmog Transmog.Test.RuntimeRepr

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

/-! ## Scalars and collections through the compiled primitives -/

private def checkScalars : IO Unit := do
  let bs := ByteArray.replicate 16 0xAA
  for i in [0:15] do
    let v16 := (i * 293).toUInt16
    let v64 := (i * 100000000733).toUInt64
    let expected16 := bs.extract 0 i ++ v16.toLEBytes ++ bs.extract (i + 2) bs.size
    check "set16 bytes" (bs.set16! i v16 == expected16)
    check "get16" (expected16.get16! i == v16)
    if i + 8 ≤ bs.size then
      let expected64 := bs.extract 0 i ++ v64.toLEBytes ++ bs.extract (i + 8) bs.size
      check "set64 bytes" (bs.set64! i v64 == expected64)
      check "get64" (expected64.get64! i == v64)
    check "push64" (bs.push64 v64 == bs ++ v64.toLEBytes)
  check "copy-on-write preserves original" (bs == ByteArray.replicate 16 0xAA)
  check "large Nat read" (bs.get64! (2 ^ 128) == 0)
  check "large Nat write" (bs.set64! (2 ^ 128) 99 == bs)
  let xs := ([1, 2, 3] : List UInt64).toCompactArray
  check "compact array reads" (xs.toList == [1, 2, 3])
  check "compact array USize read" (xs.uget 1 (by simp [xs]) == 2)
  let ys := xs.uset 1 9 (by simp [xs])
  check "compact array USize write" (ys.toList == [1, 9, 3])
  check "compact array COW" (xs.toList == [1, 2, 3])
  check "compact array fold" (xs.foldl (· + ·) 0 == 6)
  check "iterator" (xs.iter.toList == [1, 2, 3])
  let ns := ([⟨1, 2, 3⟩, ⟨4, 5, 6⟩] : List Transmog.Test.Derive.Natural).toCompactArray
  check "derived layout stride" (ns.data.size == 24)
  check "derived layout reads" (ns.toList == [⟨1, 2, 3⟩, ⟨4, 5, 6⟩])
  check "derived layout USize write"
    ((ns.uset 0 ⟨7, 8, 9⟩ (by simp [ns])).toList == [⟨7, 8, 9⟩, ⟨4, 5, 6⟩])

/-! ## Word-backed values -/

@[noinline] private def laterMatch : Node → UInt32
  | .inode p => p.val
  | _ => 0

@[noinline] private def laterEqual : Node → Node → Bool
  | .sink, .sink => true
  | .inode p, .inode q => p.val == q.val
  | _, _ => false

private def opExpectedIndex : Op → Nat
  | .nop => 0
  | .add => 1
  | .sub => 2
  | .mul => 3
  | .div => 4
  | .mod => 5
  | .band => 6
  | .bor => 7
  | .bxor => 8
  | .shl => 9
  | .imm _ => 10

private def allOps : List Op :=
  [.nop, .add, .sub, .mul, .div, .mod, .band, .bor, .bxor, .shl, .imm 0, .imm 7, .imm 255]

private def checkNode : IO Unit := do
  let pointers : List Ptr := [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨0x12345678, by decide⟩,
    ⟨0x7fffffff, by decide⟩]
  let nodes := Node.sink :: pointers.map makeNode
  for n in nodes do
    let w := matchWord n
    check "rec" (recWord n == w)
    check "casesOn" (casesWord n == w)
    check "recOn" (recOnWord n == w)
    check "constructor index" (constructorIndex n == if w == 0 then 0 else 1)
    check "dependent match" (dependentWord n == w)
    check "codec" (matchWord (codec n) == w)
    check "repr" (!(reprStr n).isEmpty)
    check "wildcard" (wildcard n == w)
    check "private downstream wildcard" (laterMatch n == w)
  for a in nodes do
    for b in nodes do
      let expected := matchWord a == matchWord b
      check "derived BEq" (equal a b == expected)
      check "derived DecidableEq" (decideEqual a b == expected)
      check "private downstream multi-match" (laterEqual a b == expected)

private def checkWide : IO Unit := do
  -- A nullary constructor whose packed word is not zero, so it cannot coincide with `box 0`.
  check "nonzero nullary encoding" (DataRepr.toRepr cellEmpty == (0, 7, 9))
  check "nullary field default" (cellFst cellEmpty == 0 && cellSnd cellEmpty == 0)
  check "nullary codec" (cellFst (cellCodec cellEmpty) == 0)
  check "nullary equality" (cellEmpty == Cell.empty)
  for a in [(0 : UInt8), 1, 7, 128, 255] do
    for b in [(0 : UInt8), 3, 200, 255] do
      let c := cellMake a b
      check "multi-slot fields" (cellFst c == a && cellSnd c == b)
      check "multi-slot codec" (cellCodec c == c)
      check "multi-slot join point" (cellPick c true == a + 1 && cellPick c false == b + 1)
      check "multi-slot inequality" (c != Cell.empty)
      check "multi-slot option" (cellOption (some c) == a && cellOption none == 255)
  for o in allOps do
    check "wide constructor index" (opIndex o == opExpectedIndex o)
    check "wide codec" (opCodec o == o)
    check "wide self equality" (opBEq o o && opDecEq o o)
    check "wide ordering reflexive" (opLE o o)
  for a in allOps do
    for b in allOps do
      let same := opIndex a == opIndex b && opArg a == opArg b
      check "wide derived BEq" (opBEq a b == same)
      check "wide derived DecidableEq" (opDecEq a b == same)
      unless opBEq a b do
        check "wide hash separates tags" (opIndex a == opIndex b || opHash a != opHash b)
  check "wide fold over a closure" (opFold allOps == 10 + 0 + 7 + 255)
  check "wide array round trip" (opsRoundTrip allOps.toArray == allOps.toArray)
  let cells := [Cell.empty, .pair 1 2, .pair 255 0]
  check "layout over a word-backed type" ((cellsToCompact cells).toList == cells)
  check "layout stride" ((cellsToCompact cells).data.size == 9)

private def checkRetag : IO Unit := do
  for v in [(0 : UInt8), 1, 127, 255] do
    for negative in [false, true] do
      let s := signedMake negative v
      check "reclassified constructor index" (signedIndex s == if negative then 1 else 0)
      check "reclassified value" (signedValue s == if negative then 0 - v else v)
      check "reclassified codec" (signedCodec s == s)
      check "reclassified equality" (signedBEq s s && signedDecEq s s)
      check "reclassified inequality" (!signedBEq s (signedMake (!negative) v))
      check "reclassified repr" (!(reprStr s).isEmpty)
  let pointers : List Ptr := [⟨1, by decide⟩, ⟨0x12345678, by decide⟩, ⟨0x7fffffff, by decide⟩]
  let nodes := Node.sink :: pointers.map makeNode
  for n in nodes do
    let w := matchWord n
    for c in [false, true] do
      let e := edgeMake c n
      let packed := (w <<< 1) ||| (if c then 1 else 0)
      check "structure projection" (edgeCompl e == c)
      check "structure projection then match" (edgeNode e == w)
      check "structure match" (edgeMatch e == packed)
      check "structure update" (edgeCompl (edgeFlip e) == !c && edgeNode (edgeFlip e) == w)
      check "structure recursor" (edgeRec e == if c then w else 0)
      check "structure codec" (edgeCodec e == e)
      check "structure equality" (edgeBEq e e && edgeDecEq e e)
      check "structure inequality" (!edgeBEq e (edgeFlip e) && !edgeDecEq e (edgeFlip e))
      check "structure repr" (!(reprStr e).isEmpty)
      check "structure in option" (edgeOption (some e) == packed && edgeOption none == 0xffffffff)
      let l : Link := { hi := e, lo := edgeFlip e }
      check "structure in a structure"
        (edgeBEq (linkHi l) e && edgeBEq (linkHi (linkSwap l)) (edgeFlip e))
  let edges := nodes.flatMap fun n => [edgeMake false n, edgeMake true n]
  check "structure array round trip" (edgesRoundTrip edges.toArray == edges.toArray)
  check "structure projection as a function" (edgeCompls edges == edges.map (·.compl))
  check "layout over a reclassified structure" ((edgesToCompact edges).toList == edges)
  check "layout stride" ((edgesToCompact edges).data.size == 4 * edges.length)
  let links := edges.zipWith (fun hi lo => ({ hi, lo } : Link)) edges.reverse
  check "layout over a container of reclassified structures"
    ((linksToCompact links).toList.map linkHi == links.map (·.hi))
  -- Deterministic, so the two runs agree; what matters is that neither run crashes.
  check "allocation stress" (churn 32 == churn 32)

public def main : IO Unit := do
  checkScalars
  checkNode
  checkWide
  checkRetag
  IO.println "Native checks passed: scalars, collections, word-backed matches, recursors, \
    codecs and derived instances."
