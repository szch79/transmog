import Transmog
import Relay

open Transmog Transmog.Test.RuntimeRepr

-- Client code needs no C includes or additional compiler flags.
-- set_option linter.hazel false

-- A type declared with its representation from another package.
transmog struct Sample as [a : UInt32, b : UInt32] where
  x : UInt32 <= a
  y : UInt32 <= b
derive_layout C packed
deriving Repr, DecidableEq

#eval show IO Unit from do
  let bs := [1, 2].toByteArray
  unless bs.get16! 0 == 513 do throw (IO.userError "interpreted scalar read")
  unless (bs.set16! 0 0xABCD).toList == [0xCD, 0xAB] do
    throw (IO.userError "interpreted scalar write")
  unless (ByteArray.empty.push16 0xABCD).toList == [0xCD, 0xAB] do
    throw (IO.userError "interpreted scalar push")
  unless UInt64.ofLEBytes [0x34, 0x12].toByteArray == 0x1234 do
    throw (IO.userError "interpreted short decoder")
  -- The interpreter executes the same IR, so the reclassified types have to survive it as well.
  let e := edgeMake true (makeNode ⟨5, by decide⟩)
  unless edgeMatch e == 11 && !edgeCompl (edgeFlip e) && Relay.edgeEq e e do
    throw (IO.userError "interpreted reclassified structure")
  unless churn 4 == churn 4 do
    throw (IO.userError "interpreted allocation stress")

@[noinline] def scalarRead (bs : @& ByteArray) (i : USize)
    (h : i.toNat < bs.size - 1) : UInt16 := bs.uget16 i h

@[noinline] def scalarWrite (bs : ByteArray) (i : USize) (v : UInt16)
    (h : i.toNat < bs.size - 1) : ByteArray := bs.uset16 i v h

def main : IO Unit := do
  let xs := [1, 2, 3, 4].toByteArray
  unless xs.get16! 1 == 770 do throw (IO.userError "downstream scalar read")
  unless (xs.set16! 1 0xABCD).toList == [1, 0xCD, 0xAB, 4] do
    throw (IO.userError "downstream scalar write")
  unless (xs.push64 0x0102030405060708).size == 12 do
    throw (IO.userError "downstream scalar push")
  let a := ([10, 20, 30] : List UInt64).toCompactArray
  unless a.iter.toList == [10, 20, 30] do throw (IO.userError "downstream iterator")
  -- Word-backed types work in a downstream package with no per-module preparation.
  let ptrs : List Ptr := [⟨1, by decide⟩, ⟨0x12345678, by decide⟩, ⟨0x7fffffff, by decide⟩]
  let nodes := Node.sink :: ptrs.map Consumer.nodeMake
  for n in nodes do
    let w := Consumer.nodeWord n
    unless Consumer.nodeWildcard n == w do throw (IO.userError "downstream word-backed match")
    unless Relay.nodePair n n do throw (IO.userError "downstream word-backed pair match")
  for a in nodes do
    for b in nodes do
      unless Relay.nodePair a b == (Consumer.nodeWord a == Consumer.nodeWord b) do
        throw (IO.userError "downstream word-backed comparison")
  unless Consumer.opArgDown (.imm 42) == 42 && Consumer.opArgDown .nop == 0 do
    throw (IO.userError "downstream wide match")
  unless Relay.opEq (.imm 42) (.imm 42) && !Relay.opEq (.imm 42) .nop do
    throw (IO.userError "downstream wide equality")
  unless Consumer.cellFstDown (.pair 7 9) == 7 && Consumer.cellFstDown .empty == 0 do
    throw (IO.userError "downstream multi-slot match")
  for n in nodes do
    for c in [false, true] do
      let e := Consumer.edgeMakeDown c n
      let expected := (Consumer.nodeWord n <<< 1) ||| (if c then 1 else 0)
      unless Consumer.edgeWordDown e == expected do
        throw (IO.userError "downstream reclassified structure")
      unless Relay.edgeEq e e && !Relay.edgeEq e (edgeFlip e) do
        throw (IO.userError "downstream reclassified comparison")
  unless Consumer.signedValueDown (.neg 1) == 255 && Consumer.signedValueDown (.pos 1) == 1 do
    throw (IO.userError "downstream reclassified inductive")
  let samples : CompactArray Sample := CompactArray.empty.push { x := 10, y := 20 }
  unless samples.data.size == 8 && samples.toList == [{ x := 10, y := 20 }] do
    throw (IO.userError "downstream declared representation")
  IO.println "Downstream consumer passed."
