import Lean

/-!
# Shared P3109 comparison workload

Both adapters compile this file with their library's pinned Lean toolchain. Input construction
and file output happen outside the timed loop. The returned code selects the next fixture.
-/

namespace P3109Comparison

private def fixture (cardinality i : Nat) : Nat × Nat × Nat :=
  let sign := cardinality / 2
  let x := if cardinality == 16 then 1 + (i * 3) % 7 else 40 + (i * 7) % 64
  let y := if cardinality == 16 then 1 + (i * 5 + 2) % 7 else 32 + (i * 11) % 72
  let z := if cardinality == 16 then 1 + (i * 2 + 4) % 7 else 28 + (i * 13) % 80
  (x + (if i % 2 == 0 then 0 else sign),
   y + (if i % 3 == 0 then sign else 0),
   z + (if i % 4 == 0 then sign else 0))

/-- A result-dependent loop shared by the two compiled libraries. -/
@[noinline] def chain {α : Type} [Inhabited α]
    (operation : α → α → α → Nat) (inputs : Array (α × α × α))
    (iterations : Nat) : IO UInt64 := do
  let mut index := 0
  let mut checksum : UInt64 := 0
  for i in [:iterations] do
    let (x, y, z) := inputs[index]!
    let result := operation x y z
    index := (index + result + i + 1) % 16
    checksum := checksum * 1664525 + result.toUInt64 + index.toUInt64
  return checksum

/-- Emit every binary pair; FMA exhausts four-bit triples and samples one z per eight-bit pair. -/
private def check {α : Type} [Inhabited α] (cardinality : Nat)
    (ofCode : Nat → α) (operation : α → α → α → Nat)
    (isFma : Bool) (path : System.FilePath) : IO Unit := do
  let values := (Array.range cardinality).map ofCode
  let mut output := ByteArray.empty
  for x in [:cardinality] do
    for y in [:cardinality] do
      let zs := if isFma && cardinality == 16 then cardinality else 1
      for zi in [:zs] do
        let z := if zs == 16 then zi else (x * 17 + y * 29 + 43) % cardinality
        let result := operation values[x]! values[y]! values[z]!
        if result ≥ cardinality then
          throw <| IO.userError s!"result code {result} exceeds {cardinality}"
        output := output.push result.toUInt8
  IO.FS.writeBinFile path output
  IO.println s!"{output.size}"

/-- Run the identical correctness or timing protocol with a library-specific operation. -/
def run {α : Type} (cardinality : Nat) (ofCode : Nat → α)
    (select : String → Option (α → α → α → Nat)) (args : List String) : IO Unit := do
  let _ : Inhabited α := ⟨ofCode 0⟩
  let opName := args[0]?.getD ""
  let some operation := select opName
    | throw <| IO.userError "operation must be add, mul, div, or fma"
  match args.drop 1 with
  | ["check", path] => check cardinality ofCode operation (opName == "fma") path
  | ["fixtures", path] =>
    let mut output := ByteArray.empty
    for i in [:16] do
      let (x, y, z) := fixture cardinality i
      let result := operation (ofCode x) (ofCode y) (ofCode z)
      if result ≥ cardinality then
        throw <| IO.userError s!"result code {result} exceeds {cardinality}"
      for code in [x, y, z, result] do
        output := output.push code.toUInt8
    IO.FS.writeBinFile path output
  | ["time", count] =>
    let some iterations := count.toNat?
      | throw <| IO.userError "iteration count must be a natural number"
    let inputs := (Array.range 16).map fun i =>
      let (x, y, z) := fixture cardinality i
      (ofCode x, ofCode y, ofCode z)
    let _ ← chain operation inputs 256
    let start ← IO.monoNanosNow
    let checksum ← chain operation inputs iterations
    let stop ← IO.monoNanosNow
    IO.println s!"{iterations},{stop - start},{checksum}"
  | _ =>
    throw <| IO.userError "expected: FORMAT OP check|fixtures PATH | FORMAT OP time ITERATIONS"

end P3109Comparison
