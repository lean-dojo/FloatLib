/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.Sweep
import FloatLibBenchmarks.Support.Posit

/-!
# Small performance-regression workload

This executable is the runtime half of `benchmarks/scripts/performance-regression.sh`. It times
one representative public addition loop for IEEE binary32, binary64, binary128, Posit32, and the
custom 256-bit E19M236 binary format. Inputs, carrier bridges, observable sinks, and static backend
selection are shared with the full benchmark suite. Format selection and input construction occur
outside the hot loop.

The probe is intentionally narrow. The full sweeps remain the source for operation-by-operation
performance studies; this executable provides a fast signal suitable for routine refactoring.
-/

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics
open FloatLibBenchmarks.Support
open FloatLibBenchmarks.Support.Environment

namespace FloatLibBenchmarks.Public.PerformanceRegression

abbrev Binary32 := FloatLibBenchmarks.Public.Sweep.P24
abbrev Binary64 := FloatLibBenchmarks.Public.Sweep.P53
abbrev Binary128 := FloatLibBenchmarks.Public.Sweep.P113
abbrev Binary256 := FloatLibBenchmarks.Public.Sweep.P237
abbrev Posit32 := ExecFloat.Posit 32

syntax "regression_workload " ident " : " term " observing " term : command

macro_rules
  | `(regression_workload $name:ident : $type:term observing $observe:term) =>
      `(@[noinline] def $name :
          Nat → Array $type → Array $type → UInt64 → UInt64
        | 0, _, _, sink => sink
        | count + 1, xs, ys, sink =>
            let index := count &&& 15
            let result := ExecFloat.add xs[index]! ys[index]!
            $name count xs ys (Sink.mix sink ($observe result)))

regression_workload binary32Add : Binary32
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_workload binary64Add : Binary64
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_workload binary128Add : Binary128
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_workload posit32Add : Posit32
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_workload binary256Add : Binary256
  observing FloatLibBenchmarks.Public.Sweep.resultBits

private structure Filters where
  format? : Option String
  iterations? : Option Nat
  warmupIterations : Nat

private def readFilters : IO Filters := do
  let format? ← IO.getEnv "PERF_FORMAT"
  if let some format := format? then
    unless format ∈ ["binary32", "binary64", "binary128", "posit32", "binary256"] do
      throw <| IO.userError s!"invalid PERF_FORMAT: {format}"
  pure {
    format?
    iterations? := ← positiveNat? "PERF_ITERATIONS"
    warmupIterations := (← positiveNat? "PERF_WARMUP_ITERATIONS").getD 256
  }

private def Filters.accepts (filters : Filters) (format : String) : Bool :=
  filters.format?.all (· == format)

private def timeRow (filters : Filters) (format backend : String) (totalBits defaultCount : Nat)
    (run : Nat → UInt64) : IO Unit := do
  unless filters.accepts format do
    return
  let iterations := filters.iterations?.getD defaultCount
  let warmup ← IO.mkRef 0
  warmup.set (run filters.warmupIterations)
  let result ← IO.mkRef 0
  let start ← IO.monoNanosNow
  result.set (run iterations)
  let stop ← IO.monoNanosNow
  IO.println s!"{format},{totalBits},{backend},{iterations},{stop - start},{(← result.get).toNat}"

private def runBinary
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F FloatFormat Model] [ExecFloat.Add F]
    (filters : Filters) (format : String) (totalBits defaultCount : Nat)
    (workload : Nat → Array (ExecFloat F) → Array (ExecFloat F) → UInt64 → UInt64) :
    IO Unit := do
  unless filters.accepts format do
    return
  let xs := FloatLibBenchmarks.Public.Sweep.inputsX F
  let ys := FloatLibBenchmarks.Public.Sweep.inputsY F
  timeRow filters format (ExecFloat.Add.selectedCandidate (F := F)).name totalBits defaultCount
    fun count => workload count xs ys 0

private def runPosit
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F FloatLib.Floats.Formats.Posit.Format
      FloatLib.Floats.Formats.Posit.Model] [ExecFloat.Add F]
    (filters : Filters) (format : String) (totalBits defaultCount : Nat)
    (workload : Nat → Array (ExecFloat F) → Array (ExecFloat F) → UInt64 → UInt64) :
    IO Unit := do
  unless filters.accepts format do
    return
  let xs := FloatLibBenchmarks.Support.Posit.inputsX F
  let ys := FloatLibBenchmarks.Support.Posit.inputsY F
  timeRow filters format (ExecFloat.Add.selectedCandidate (F := F)).name totalBits defaultCount
    fun count => workload count xs ys 0

def run : IO Unit := do
  let filters ← readFilters
  IO.println "format,totalBits,backend,iterations,totalNanos,sink"
  runBinary filters "binary32" 32 1000000 binary32Add
  runBinary filters "binary64" 64 1000000 binary64Add
  runBinary filters "binary128" 128 100000 binary128Add
  runPosit filters "posit32" 32 500000 posit32Add
  runBinary filters "binary256" 256 50000 binary256Add

end FloatLibBenchmarks.Public.PerformanceRegression

public def main : IO Unit :=
  FloatLibBenchmarks.Public.PerformanceRegression.run
