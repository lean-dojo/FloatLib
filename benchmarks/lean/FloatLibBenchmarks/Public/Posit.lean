/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.Sweep
import FloatLibBenchmarks.Support.Posit

/-!
# Public Posit Standard execution benchmark

This executable measures all six user-facing `ExecFloat` operations over representative,
type-static posit widths from 2 through 4,096 bits. Every timed loop is monomorphic, consumes the
public packed carrier, records the certified backend actually selected by the dispatcher, and
mixes result words into an observable sink.

The static dispatcher selects each kernel from the width, operation, and execution policy, and
every row records the actual choice. Under the balanced policy, the very smallest formats use
exhaustive encoded-value tables, while byte-wide binary operations stay on direct packed-word
kernels because constructing a full binary table is too expensive for ordinary cold execution;
the much smaller byte-wide square-root table remains worthwhile. Selected lazy resources are
warmed outside the timed interval. Widths through 64 otherwise use direct packed-word kernels.
The public carrier remains a built-in word throughout that tier. Multiplication remains on the
direct packed-word kernel; fused multiply-add from width 37 widens only its internal exact kernel
to two `UInt64` limbs. The static dispatcher leaves no runtime width test in the generated
operation body.
Widths from 65 through 128 use direct packed-pair kernels: persistent operands are read from two
fixed `UInt64` limbs and exact arithmetic avoids rational normalization. Addition, subtraction,
multiplication, and fused multiply-add use packed exact-dyadic kernels. Division and square root
decode the packed fields directly and reuse the same destination-width quotient-prefix and
integer-root-prefix kernels as arbitrary-width Posits. Their exact remainders provide the sticky
information needed for nearest-even rounding; there is no candidate validation or fallback
search. Wider widths use those same proved prefix constructions over arbitrary-precision integer
carriers.

The x-axis is total encoded posit width, not a constant significand precision. Posit precision is
tapered and therefore depends on the represented value. Comparisons with fixed-precision binary,
MPFR, or Flocq must state the matching rule instead of silently treating total posit bits as a
fixed number of fraction bits.
-/

open FloatLib.Floats
open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit
open FloatLibBenchmarks.Public.Sweep
open FloatLibBenchmarks.Support
open FloatLibBenchmarks.Support.Environment
open FloatLibBenchmarks.Support.Posit

namespace FloatLibBenchmarks.Public.Posit

syntax "posit_binary_workload " ident " : " term " using " term : command
syntax "posit_ternary_workload " ident " : " term " using " term : command
syntax "posit_unary_workload " ident " : " term " using " term : command

macro_rules
  | `(posit_binary_workload $name:ident : $type:term using $operation:term) =>
      `(@[noinline] def $name :
          Nat → Array $type → Array $type → UInt64 → UInt64
        | 0, _, _, sink => sink
        | count + 1, xs, ys, sink =>
            let index := count &&& 15
            let result := $operation xs[index]! ys[index]!
            $name count xs ys
              (Support.Sink.mix sink
                (FloatLibBenchmarks.Support.Posit.resultBits result)))
  | `(posit_ternary_workload $name:ident : $type:term using $operation:term) =>
      `(@[noinline] def $name :
          Nat → Array $type → Array $type → Array $type → UInt64 → UInt64
        | 0, _, _, _, sink => sink
        | count + 1, xs, ys, zs, sink =>
            let index := count &&& 15
            let result := $operation xs[index]! ys[index]! zs[index]!
            $name count xs ys zs
              (Support.Sink.mix sink
                (FloatLibBenchmarks.Support.Posit.resultBits result)))
  | `(posit_unary_workload $name:ident : $type:term using $operation:term) =>
      `(@[noinline] def $name :
          Nat → Array $type → UInt64 → UInt64
        | 0, _, sink => sink
        | count + 1, xs, sink =>
            let index := count &&& 15
            let result := $operation xs[index]!
            $name count xs
              (Support.Sink.mix sink
                (FloatLibBenchmarks.Support.Posit.resultBits result)))

abbrev P2 := ExecFloat.Posit 2
abbrev P3 := ExecFloat.Posit 3
abbrev P4 := ExecFloat.Posit 4
abbrev P5 := ExecFloat.Posit 5
abbrev P6 := ExecFloat.Posit 6
abbrev P7 := ExecFloat.Posit 7
abbrev P8 := ExecFloat.Posit 8
abbrev P16 := ExecFloat.Posit 16
abbrev P32 := ExecFloat.Posit 32
abbrev P64 := ExecFloat.Posit 64
abbrev P128 := ExecFloat.Posit 128
abbrev P256 := ExecFloat.Posit 256
abbrev P512 := ExecFloat.Posit 512
abbrev P1024 := ExecFloat.Posit 1024
abbrev P2048 := ExecFloat.Posit 2048
abbrev P4096 := ExecFloat.Posit 4096

posit_binary_workload p2Add : P2 using ExecFloat.add
posit_binary_workload p2Sub : P2 using ExecFloat.sub
posit_binary_workload p2Mul : P2 using ExecFloat.mul
posit_binary_workload p2Div : P2 using ExecFloat.div
posit_unary_workload p2Sqrt : P2 using ExecFloat.sqrt
posit_ternary_workload p2Fma : P2 using ExecFloat.fma

posit_binary_workload p3Add : P3 using ExecFloat.add
posit_binary_workload p3Sub : P3 using ExecFloat.sub
posit_binary_workload p3Mul : P3 using ExecFloat.mul
posit_binary_workload p3Div : P3 using ExecFloat.div
posit_unary_workload p3Sqrt : P3 using ExecFloat.sqrt
posit_ternary_workload p3Fma : P3 using ExecFloat.fma

posit_binary_workload p4Add : P4 using ExecFloat.add
posit_binary_workload p4Sub : P4 using ExecFloat.sub
posit_binary_workload p4Mul : P4 using ExecFloat.mul
posit_binary_workload p4Div : P4 using ExecFloat.div
posit_unary_workload p4Sqrt : P4 using ExecFloat.sqrt
posit_ternary_workload p4Fma : P4 using ExecFloat.fma

posit_binary_workload p5Add : P5 using ExecFloat.add
posit_binary_workload p5Sub : P5 using ExecFloat.sub
posit_binary_workload p5Mul : P5 using ExecFloat.mul
posit_binary_workload p5Div : P5 using ExecFloat.div
posit_unary_workload p5Sqrt : P5 using ExecFloat.sqrt
posit_ternary_workload p5Fma : P5 using ExecFloat.fma

posit_binary_workload p6Add : P6 using ExecFloat.add
posit_binary_workload p6Sub : P6 using ExecFloat.sub
posit_binary_workload p6Mul : P6 using ExecFloat.mul
posit_binary_workload p6Div : P6 using ExecFloat.div
posit_unary_workload p6Sqrt : P6 using ExecFloat.sqrt
posit_ternary_workload p6Fma : P6 using ExecFloat.fma

posit_binary_workload p7Add : P7 using ExecFloat.add
posit_binary_workload p7Sub : P7 using ExecFloat.sub
posit_binary_workload p7Mul : P7 using ExecFloat.mul
posit_binary_workload p7Div : P7 using ExecFloat.div
posit_unary_workload p7Sqrt : P7 using ExecFloat.sqrt
posit_ternary_workload p7Fma : P7 using ExecFloat.fma

posit_binary_workload p8Add : P8 using ExecFloat.add
posit_binary_workload p8Sub : P8 using ExecFloat.sub
posit_binary_workload p8Mul : P8 using ExecFloat.mul
posit_binary_workload p8Div : P8 using ExecFloat.div
posit_unary_workload p8Sqrt : P8 using ExecFloat.sqrt
posit_ternary_workload p8Fma : P8 using ExecFloat.fma

posit_binary_workload p16Add : P16 using ExecFloat.add
posit_binary_workload p16Sub : P16 using ExecFloat.sub
posit_binary_workload p16Mul : P16 using ExecFloat.mul
posit_binary_workload p16Div : P16 using ExecFloat.div
posit_unary_workload p16Sqrt : P16 using ExecFloat.sqrt
posit_ternary_workload p16Fma : P16 using ExecFloat.fma

posit_binary_workload p32Add : P32 using ExecFloat.add
posit_binary_workload p32Sub : P32 using ExecFloat.sub
posit_binary_workload p32Mul : P32 using ExecFloat.mul
posit_binary_workload p32Div : P32 using ExecFloat.div
posit_unary_workload p32Sqrt : P32 using ExecFloat.sqrt
posit_ternary_workload p32Fma : P32 using ExecFloat.fma

posit_binary_workload p64Add : P64 using ExecFloat.add
posit_binary_workload p64Sub : P64 using ExecFloat.sub
posit_binary_workload p64Mul : P64 using ExecFloat.mul
posit_binary_workload p64Div : P64 using ExecFloat.div
posit_unary_workload p64Sqrt : P64 using ExecFloat.sqrt
posit_ternary_workload p64Fma : P64 using ExecFloat.fma

posit_binary_workload p128Add : P128 using ExecFloat.add
posit_binary_workload p128Sub : P128 using ExecFloat.sub
posit_binary_workload p128Mul : P128 using ExecFloat.mul
posit_binary_workload p128Div : P128 using ExecFloat.div
posit_unary_workload p128Sqrt : P128 using ExecFloat.sqrt
posit_ternary_workload p128Fma : P128 using ExecFloat.fma

posit_binary_workload p256Add : P256 using ExecFloat.add
posit_binary_workload p256Sub : P256 using ExecFloat.sub
posit_binary_workload p256Mul : P256 using ExecFloat.mul
posit_binary_workload p256Div : P256 using ExecFloat.div
posit_unary_workload p256Sqrt : P256 using ExecFloat.sqrt
posit_ternary_workload p256Fma : P256 using ExecFloat.fma

posit_binary_workload p512Add : P512 using ExecFloat.add
posit_binary_workload p512Sub : P512 using ExecFloat.sub
posit_binary_workload p512Mul : P512 using ExecFloat.mul
posit_binary_workload p512Div : P512 using ExecFloat.div
posit_unary_workload p512Sqrt : P512 using ExecFloat.sqrt
posit_ternary_workload p512Fma : P512 using ExecFloat.fma

posit_binary_workload p1024Add : P1024 using ExecFloat.add
posit_binary_workload p1024Sub : P1024 using ExecFloat.sub
posit_binary_workload p1024Mul : P1024 using ExecFloat.mul
posit_binary_workload p1024Div : P1024 using ExecFloat.div
posit_unary_workload p1024Sqrt : P1024 using ExecFloat.sqrt
posit_ternary_workload p1024Fma : P1024 using ExecFloat.fma

posit_binary_workload p2048Add : P2048 using ExecFloat.add
posit_binary_workload p2048Sub : P2048 using ExecFloat.sub
posit_binary_workload p2048Mul : P2048 using ExecFloat.mul
posit_binary_workload p2048Div : P2048 using ExecFloat.div
posit_unary_workload p2048Sqrt : P2048 using ExecFloat.sqrt
posit_ternary_workload p2048Fma : P2048 using ExecFloat.fma

posit_binary_workload p4096Add : P4096 using ExecFloat.add
posit_binary_workload p4096Sub : P4096 using ExecFloat.sub
posit_binary_workload p4096Mul : P4096 using ExecFloat.mul
posit_binary_workload p4096Div : P4096 using ExecFloat.div
posit_unary_workload p4096Sqrt : P4096 using ExecFloat.sqrt
posit_ternary_workload p4096Fma : P4096 using ExecFloat.fma

private def validOperation (operation : String) : Bool :=
  operation ∈ ["add", "sub", "mul", "div", "sqrt", "fma"]

/-- One calibrated measured-loop count selected for a width and operation. -/
private structure IterationOverride where
  width : Nat
  operation : String
  iterations : Nat

private def parsePositiveNat (name text : String) : Except String Nat := do
  let some value := text.toNat?
    | throw s!"invalid {name}: {text}"
  if value = 0 then
    throw s!"{name} must be positive"
  return value

private def parseIterationOverride
    (text : String) : Except String IterationOverride := do
  let [widthText, operation, iterationsText] := text.splitOn ":"
    | throw s!"invalid iteration-map entry: {text}"
  unless validOperation operation do
    throw s!"invalid iteration-map operation: {operation}"
  return {
    width := ← parsePositiveNat "iteration-map width" widthText
    operation
    iterations := ← parsePositiveNat "iteration-map count" iterationsText
  }

/--
Parse `width:operation:iterations` entries separated by semicolons.

The shell harness constructs this map from isolated calibration processes. The benchmark reads it
once before timing, so a steady-state trial can retain per-row measurement durations without
paying one process startup per row.
-/
private def parseIterationMap
    (text : String) : Except String (List IterationOverride) := do
  if text.isEmpty then
    return []
  (text.splitOn ";").foldlM (init := []) fun overrides entry => do
    let parsed ← parseIterationOverride entry
    if overrides.any fun existing =>
        existing.width == parsed.width &&
          existing.operation == parsed.operation then
      throw s!"duplicate iteration-map entry: {parsed.width}:{parsed.operation}"
    return parsed :: overrides

private def iterationOverride?
    (overrides : List IterationOverride) (width : Nat) (operation : String) :
    Option Nat :=
  (overrides.find? fun item =>
    item.width == width && item.operation == operation).map (·.iterations)

/-- Benchmark filters read once before any table construction or timing. -/
structure Filters where
  width? : Option Nat
  operation? : Option String
  iterations? : Option Nat
  iterationOverrides : List IterationOverride
  coldIterations : Nat
  warmupIterations? : Option Nat
  reverseTraversal : Bool
  profileAllocations : Bool
  /--
  Preserve input construction, cold execution, and warmup while replacing only
  the measured workload by a no-op. The allocation harness subtracts this
  matched control process from an otherwise identical measured process.
  -/
  allocationControl : Bool

private def readFilters : IO Filters := do
  let width? ← positiveNat? "POSIT_BENCH_WIDTH"
  let operation? ← IO.getEnv "POSIT_BENCH_OPERATION"
  if let some operation := operation? then
    unless validOperation operation do
      throw <| IO.userError s!"invalid POSIT_BENCH_OPERATION: {operation}"
  let iterations? ← positiveNat? "POSIT_BENCH_ITERATIONS"
  let iterationOverrides ←
    match ← IO.getEnv "POSIT_BENCH_ITERATION_MAP" with
    | none => pure []
    | some text =>
        match parseIterationMap text with
        | .ok overrides => pure overrides
        | .error message => throw <| IO.userError message
  let coldIterations :=
    (← positiveNat? "POSIT_BENCH_COLD_ITERATIONS").getD 1
  let warmupIterations? ← positiveNat? "POSIT_BENCH_WARMUP_ITERATIONS"
  let reverseTraversal ← bool "POSIT_BENCH_REVERSE"
  let profileAllocations ← bool "POSIT_BENCH_ALLOCPROF"
  let allocationControl ← bool "POSIT_BENCH_ALLOCATION_CONTROL"
  pure {
    width?
    operation?
    iterations?
    iterationOverrides
    coldIterations
    warmupIterations?
    reverseTraversal
    profileAllocations
    allocationControl
  }

private def Filters.accepts (filters : Filters) (width : Nat) (operation : String) : Bool :=
  filters.width?.all (· == width) && filters.operation?.all (· == operation)

/-- Width-sensitive default count for the current table, dyadic, and rational implementations. -/
def defaultIterations (width : Nat) : Nat :=
  if width ≤ 8 then 250000
  else if width ≤ 16 then 5000
  else if width ≤ 32 then 2500
  else if width ≤ 64 then 1000
  else if width ≤ 128 then 500
  else if width ≤ 256 then 250
  else if width ≤ 512 then 100
  else if width ≤ 1024 then 50
  else if width ≤ 2048 then 20
  else 10

/--
The three distinct counts make cold initialization, cache and branch-predictor warmup, and
steady-state work explicit. Lean produces ahead-of-time native code here; no JIT compilation is
part of the benchmark. The default warmup is long enough to move beyond a one-cache-line toy run
while staying bounded for arbitrary-precision formats whose measured count is intentionally small.
-/
private structure RunCounts where
  cold : Nat
  warmup : Nat
  measured : Nat

private def runCounts
    (filters : Filters) (width : Nat) (operation : String) : RunCounts :=
  let measured :=
    (iterationOverride? filters.iterationOverrides width operation).getD
      (filters.iterations?.getD (defaultIterations width))
  {
    cold := filters.coldIterations
    warmup := filters.warmupIterations?.getD (min measured 256)
    measured
  }

private def printHeader : IO Unit :=
  IO.println <|
    "implementation,family,totalBits,operation,backend,kernelClass,storage," ++
      "policy,expectedCalls,coldIterations,coldNanos,coldSink," ++
      "warmupIterations,warmupSink,iterations,totalNanos,sink"

private def timeRow (profileAllocations allocationControl : Bool)
    (width : Nat) (counts : RunCounts) (operation : String)
    (candidate : ExecFloat.Backend.Candidate)
    (policy : ExecFloat.Backend.Policy) (run : Nat → UInt64) : IO Unit := do
  -- The first invocation is timed separately so lazy table construction and other one-time work
  -- cannot be silently charged to, or hidden by, the steady-state measurement.
  let coldSink ← IO.mkRef 0
  let coldStart ← IO.monoNanosNow
  coldSink.set (run counts.cold)
  let coldStop ← IO.monoNanosNow
  let coldResult ← coldSink.get
  -- Retaining and reporting this sink makes the untimed warmup an observable computation.
  let warmupSink ← IO.mkRef 0
  warmupSink.set (run counts.warmup)
  let warmupResult ← warmupSink.get
  let measuredSink ← IO.mkRef 0
  let start ← IO.monoNanosNow
  measuredSink.set (if allocationControl then 0 else run counts.measured)
  let stop ← IO.monoNanosNow
  let result ← measuredSink.get
  IO.println <|
    s!"ExecFloat,posit,{width},{operation},{candidate.name},{candidate.kind.display}," ++
      s!"{candidate.storage.display},{policy.profileName},{policy.expectedCalls}," ++
      s!"{counts.cold},{coldStop - coldStart},{coldResult.toNat}," ++
      s!"{counts.warmup},{warmupResult.toNat}," ++
      s!"{counts.measured},{stop - start},{result.toNat}"
  if profileAllocations && !allocationControl then
    allocprof s!"ExecFloat.posit{width}.{operation}" do
      measuredSink.set (run counts.measured)

@[noinline] private def runBinary
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F Format Model]
    (filters : Filters) (width : Nat) (operation : String)
    (candidate : ExecFloat.Backend.Candidate)
    (policy : ExecFloat.Backend.Policy)
    (workload :
      Nat → Array (ExecFloat F) → Array (ExecFloat F) → UInt64 → UInt64) :
    IO Unit := do
  unless filters.accepts width operation do
    return
  let xs := inputsX F
  let ys := inputsY F
  let counts := runCounts filters width operation
  timeRow filters.profileAllocations filters.allocationControl
      width counts operation candidate policy fun iterations =>
    workload iterations xs ys 0

@[noinline] private def runUnary
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F Format Model]
    (filters : Filters) (width : Nat)
    (candidate : ExecFloat.Backend.Candidate)
    (policy : ExecFloat.Backend.Policy)
    (workload : Nat → Array (ExecFloat F) → UInt64 → UInt64) :
    IO Unit := do
  unless filters.accepts width "sqrt" do
    return
  let xs := inputsSqrt F
  let counts := runCounts filters width "sqrt"
  timeRow filters.profileAllocations filters.allocationControl
      width counts "sqrt" candidate policy fun iterations =>
    workload iterations xs 0

@[noinline] private def runTernary
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F Format Model]
    (filters : Filters) (width : Nat)
    (candidate : ExecFloat.Backend.Candidate)
    (policy : ExecFloat.Backend.Policy)
    (workload :
      Nat → Array (ExecFloat F) → Array (ExecFloat F) →
        Array (ExecFloat F) → UInt64 → UInt64) :
    IO Unit := do
  unless filters.accepts width "fma" do
    return
  let xs := inputsX F
  let ys := inputsY F
  let zs := xs.reverse
  let counts := runCounts filters width "fma"
  timeRow filters.profileAllocations filters.allocationControl width counts "fma"
    candidate policy fun iterations =>
      workload iterations xs ys zs 0

@[noinline] private def runFormat
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F Format Model]
    [ExecFloat.Add F] [ExecFloat.Sub F] [ExecFloat.Mul F]
    [ExecFloat.Div F] [ExecFloat.Sqrt F] [ExecFloat.Fma F]
    (filters : Filters) (width : Nat)
    (addWorkload subWorkload mulWorkload divWorkload :
      Nat → Array (ExecFloat F) → Array (ExecFloat F) → UInt64 → UInt64)
    (sqrtWorkload : Nat → Array (ExecFloat F) → UInt64 → UInt64)
    (fmaWorkload :
      Nat → Array (ExecFloat F) → Array (ExecFloat F) →
        Array (ExecFloat F) → UInt64 → UInt64) :
    IO Unit := do
  if filters.reverseTraversal then
    runTernary filters width
      (ExecFloat.Fma.selectedCandidate (F := F))
      (ExecFloat.Fma.policy (F := F)) fmaWorkload
    runUnary filters width
      (ExecFloat.Sqrt.selectedCandidate (F := F))
      (ExecFloat.Sqrt.policy (F := F)) sqrtWorkload
    runBinary filters width "div"
      (ExecFloat.Div.selectedCandidate (F := F))
      (ExecFloat.Div.policy (F := F)) divWorkload
    runBinary filters width "mul"
      (ExecFloat.Mul.selectedCandidate (F := F))
      (ExecFloat.Mul.policy (F := F)) mulWorkload
    runBinary filters width "sub"
      (ExecFloat.Sub.selectedCandidate (F := F))
      (ExecFloat.Sub.policy (F := F)) subWorkload
    runBinary filters width "add"
      (ExecFloat.Add.selectedCandidate (F := F))
      (ExecFloat.Add.policy (F := F)) addWorkload
  else
    runBinary filters width "add"
      (ExecFloat.Add.selectedCandidate (F := F))
      (ExecFloat.Add.policy (F := F)) addWorkload
    runBinary filters width "sub"
      (ExecFloat.Sub.selectedCandidate (F := F))
      (ExecFloat.Sub.policy (F := F)) subWorkload
    runBinary filters width "mul"
      (ExecFloat.Mul.selectedCandidate (F := F))
      (ExecFloat.Mul.policy (F := F)) mulWorkload
    runBinary filters width "div"
      (ExecFloat.Div.selectedCandidate (F := F))
      (ExecFloat.Div.policy (F := F)) divWorkload
    runUnary filters width
      (ExecFloat.Sqrt.selectedCandidate (F := F))
      (ExecFloat.Sqrt.policy (F := F)) sqrtWorkload
    runTernary filters width
      (ExecFloat.Fma.selectedCandidate (F := F))
      (ExecFloat.Fma.policy (F := F)) fmaWorkload

syntax "posit_format_runner " ident " at " num " using "
  ident ident ident ident ident ident : command

macro_rules
  | `(posit_format_runner $name:ident at $width:num using
        $add:ident $sub:ident $mul:ident $div:ident $sqrt:ident $fma:ident) =>
      `(@[noinline] private def $name (filters : Filters) : IO Unit :=
          runFormat filters $width $add $sub $mul $div $sqrt $fma)

posit_format_runner runP2 at 2 using p2Add p2Sub p2Mul p2Div p2Sqrt p2Fma
posit_format_runner runP3 at 3 using p3Add p3Sub p3Mul p3Div p3Sqrt p3Fma
posit_format_runner runP4 at 4 using p4Add p4Sub p4Mul p4Div p4Sqrt p4Fma
posit_format_runner runP5 at 5 using p5Add p5Sub p5Mul p5Div p5Sqrt p5Fma
posit_format_runner runP6 at 6 using p6Add p6Sub p6Mul p6Div p6Sqrt p6Fma
posit_format_runner runP7 at 7 using p7Add p7Sub p7Mul p7Div p7Sqrt p7Fma
posit_format_runner runP8 at 8 using p8Add p8Sub p8Mul p8Div p8Sqrt p8Fma
posit_format_runner runP16 at 16 using p16Add p16Sub p16Mul p16Div p16Sqrt p16Fma
posit_format_runner runP32 at 32 using p32Add p32Sub p32Mul p32Div p32Sqrt p32Fma
posit_format_runner runP64 at 64 using p64Add p64Sub p64Mul p64Div p64Sqrt p64Fma
posit_format_runner runP128 at 128 using p128Add p128Sub p128Mul p128Div p128Sqrt p128Fma
posit_format_runner runP256 at 256 using p256Add p256Sub p256Mul p256Div p256Sqrt p256Fma
posit_format_runner runP512 at 512 using p512Add p512Sub p512Mul p512Div p512Sqrt p512Fma
posit_format_runner runP1024 at 1024 using
  p1024Add p1024Sub p1024Mul p1024Div p1024Sqrt p1024Fma
posit_format_runner runP2048 at 2048 using
  p2048Add p2048Sub p2048Mul p2048Div p2048Sqrt p2048Fma
posit_format_runner runP4096 at 4096 using
  p4096Add p4096Sub p4096Mul p4096Div p4096Sqrt p4096Fma

def run : IO Unit := do
  let filters ← readFilters
  printHeader
  if filters.reverseTraversal then
    runP4096 filters
    runP2048 filters
    runP1024 filters
    runP512 filters
    runP256 filters
    runP128 filters
    runP64 filters
    runP32 filters
    runP16 filters
    runP8 filters
    runP7 filters
    runP6 filters
    runP5 filters
    runP4 filters
    runP3 filters
    runP2 filters
  else
    runP2 filters
    runP3 filters
    runP4 filters
    runP5 filters
    runP6 filters
    runP7 filters
    runP8 filters
    runP16 filters
    runP32 filters
    runP64 filters
    runP128 filters
    runP256 filters
    runP512 filters
    runP1024 filters
    runP2048 filters
    runP4096 filters

end FloatLibBenchmarks.Public.Posit

public def main : IO Unit :=
  FloatLibBenchmarks.Public.Posit.run
