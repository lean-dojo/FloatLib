import Lean

/-!
# Shared scalar conversion comparison

Inputs and outputs are little-endian UInt32 words. Each adapter constructs its native input
values before timing. The returned bits affect both the next input and the final checksum.
-/

namespace ConversionComparison

private def readWords (path : System.FilePath) : IO (Array UInt32) := do
  let bytes ← IO.FS.readBinFile path
  if bytes.size % 4 != 0 then
    throw <| IO.userError "input length must be a multiple of four"
  return (Array.range (bytes.size / 4)).map fun i =>
    (bytes[i * 4]!).toUInt32 |||
    (bytes[i * 4 + 1]!).toUInt32 <<< 8 |||
    (bytes[i * 4 + 2]!).toUInt32 <<< 16 |||
    (bytes[i * 4 + 3]!).toUInt32 <<< 24

private def writeWords (path : System.FilePath) (words : Array UInt32) : IO Unit := do
  let mut bytes := ByteArray.empty
  for word in words do
    for shift in [0, 8, 16, 24] do
      bytes := bytes.push (word >>> shift).toUInt8
  IO.FS.writeBinFile path bytes

/-- Measure a dependent sequence, including lookup, conversion, and checksum bookkeeping. -/
@[noinline] def chain {α : Type} [Inhabited α] (operation : α → UInt32)
    (inputs : Array α) (iterations : Nat) : IO UInt64 := do
  let mut index := 0
  let mut checksum : UInt64 := 0
  for i in [:iterations] do
    let result := operation inputs[index]!
    index := (index + result.toNat + i + 1) % inputs.size
    checksum := checksum * 1664525 + result.toUInt64 + index.toUInt64
  return checksum

/-- Share the complete checking and timing loop across the two library adapters. -/
def run {α : Type} (ofCode : UInt32 → α) (operation : α → UInt32)
    (args : List String) : IO Unit := do
  let _ : Inhabited α := ⟨ofCode 0⟩
  match args with
  | ["check", input, output] =>
    let words ← readWords input
    writeWords output (words.map fun word => operation (ofCode word))
    IO.println words.size
  | ["time", input, count] =>
    let some iterations := count.toNat?
      | throw <| IO.userError "iteration count must be a natural number"
    let inputs := (← readWords input).map ofCode
    if inputs.isEmpty then
      throw <| IO.userError "timing requires at least one input"
    let _ ← chain operation inputs 256
    let start ← IO.monoNanosNow
    let checksum ← chain operation inputs iterations
    let stop ← IO.monoNanosNow
    IO.println s!"{iterations},{stop - start},{checksum}"
  | _ => throw <| IO.userError "expected check INPUT OUTPUT or time INPUT ITERATIONS"

end ConversionComparison
