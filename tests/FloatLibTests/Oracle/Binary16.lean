/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime

/-!
# Binary16 exhaustive differential stream

`oracle binary16` evaluates logical `Model.add` or `Model.mul` and emits raw little-endian result
words for one contiguous shard of all ordered input pairs.
`tests/oracles/binary16-exhaustive.sh` pipes the stream into an independent MPFR oracle. Standard
output is binary-only; diagnostics go to standard error.
-/

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Oracle.Binary16

private inductive Operation where
  | add
  | mul

private def Operation.parse? : String → Option Operation
  | "add" => some .add
  | "mul" => some .mul
  | _ => none

@[inline] private def Operation.apply (operation : Operation)
    (left right : Model FloatFormat.binary16) :
    Model FloatFormat.binary16 :=
  match operation with
  | .add => Model.add left right
  | .mul => Model.mul left right

private def totalPairs : Nat := 2 ^ 32

private def shardBounds (index count : Nat) : Nat × Nat :=
  (totalPairs * index / count, totalPairs * (index + 1) / count)

@[inline] private def appendWord (buffer : ByteArray) (word : Nat) : ByteArray :=
  (buffer.push (UInt8.ofNat word)).push (UInt8.ofNat (word >>> 8))

private def makeChunk (operation : Operation) (start count : Nat) : ByteArray := Id.run do
  let mut buffer := ByteArray.empty
  for offset in [0:count] do
    let pair := start + offset
    let left := Model.ofNatBits (fmt := FloatFormat.binary16) (pair >>> 16)
    let right := Model.ofNatBits (fmt := FloatFormat.binary16) (pair % (2 ^ 16))
    buffer := appendWord buffer (operation.apply left right).toNatBits
  return buffer

private def streamShard (operation : Operation) (start stop : Nat) : IO Unit := do
  let stdout ← IO.getStdout
  if ← stdout.isTty then
    throw <| IO.userError "refusing to write the binary result stream to a terminal"
  let chunkPairs := 32768
  let mut cursor := start
  while cursor < stop do
    let count := min chunkPairs (stop - cursor)
    stdout.write (makeChunk operation cursor count)
    cursor := cursor + count
  stdout.flush

private def usage : String :=
  "usage: oracle binary16 {add|mul} SHARD_INDEX SHARD_COUNT"

private def parseNat (name value : String) : IO Nat :=
  match value.toNat? with
  | some result => pure result
  | none => throw <| IO.userError s!"invalid {name}: {value}"

/-- Emit a binary16 shard as little-endian words. -/
public def run (args : List String) : IO Unit := do
  let (operationText, indexText, countText) ←
    match args with
    | [operation, index, count] => pure (operation, index, count)
    | _ => throw <| IO.userError usage
  let operation ←
    match Operation.parse? operationText with
    | some result => pure result
    | none => throw <| IO.userError s!"unknown operation: {operationText}\n{usage}"
  let index ← parseNat "shard index" indexText
  let count ← parseNat "shard count" countText
  if count == 0 then
    throw <| IO.userError "shard count must be positive"
  if count > totalPairs then
    throw <| IO.userError s!"shard count must be at most {totalPairs}"
  if index >= count then
    throw <| IO.userError "shard index must be smaller than shard count"
  let (start, stop) := shardBounds index count
  IO.eprintln s!"binary16 {operationText} shard {index}/{count}: pairs [{start}, {stop})"
  streamShard operation start stop

end FloatLibTests.Oracle.Binary16
