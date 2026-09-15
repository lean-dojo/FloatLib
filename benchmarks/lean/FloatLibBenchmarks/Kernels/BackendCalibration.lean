/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.Sweep
import FloatLibBenchmarks.Support.CSV
import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Candidates

/-!
# Cold-start and warm-kernel calibration

This executable measures every admissible certified candidate exposed by the general binary
descriptor planner. It is intentionally separate from the public precision sweep:

* `firstNanos` includes lazy initialization, such as constructing an exhaustive table;
* `warmTotalNanos` measures the same candidate after initialization; and
* `selected` records whether the current deterministic policy chooses that candidate.

The calibration formats straddle every tiny-table threshold and include a non-IEEE descriptor.
Candidate availability still comes from structural predicates in `Descriptor.Plan`; the harness
does not maintain a second list of eligible algorithms.

Elapsed time is empirical data, whereas candidate estimates are portable static priors. Repeated
runs should be summarized with a robust statistic before changing those priors.
-/

open FloatLib.Floats
open FloatLib.Floats.ExecFloat.Backend
open FloatLibBenchmarks.Support.Environment
open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibBenchmarks.Kernels.BackendCalibration

abbrev Value (format : FloatFormat) :=
  ExecFloat (Descriptor format)

@[noinline] private def binaryLoop {format : FloatFormat}
    (run : Value format → Value format → Value format) :
    Nat → Array (Value format) → Array (Value format) → UInt64 → UInt64
  | 0, _, _, sink => sink
  | iterations + 1, lefts, rights, sink =>
      let index := iterations &&& 15
      let result := run lefts[index]! rights[index]!
      binaryLoop run iterations lefts rights
        (Support.Sink.mix sink (Public.Sweep.resultBits result))

@[noinline] private def unaryLoop {format : FloatFormat}
    (run : Value format → Value format) :
    Nat → Array (Value format) → UInt64 → UInt64
  | 0, _, sink => sink
  | iterations + 1, values, sink =>
      let index := iterations &&& 15
      let result := run values[index]!
      unaryLoop run iterations values
        (Support.Sink.mix sink (Public.Sweep.resultBits result))

@[noinline] private def ternaryLoop {format : FloatFormat}
    (run : Value format → Value format → Value format → Value format) :
    Nat → Array (Value format) → Array (Value format) →
      Array (Value format) → UInt64 → UInt64
  | 0, _, _, _, sink => sink
  | iterations + 1, lefts, rights, addends, sink =>
      let index := iterations &&& 15
      let result := run lefts[index]! rights[index]! addends[index]!
      ternaryLoop run iterations lefts rights addends
        (Support.Sink.mix sink (Public.Sweep.resultBits result))

private def printRow
    (formatName : String) (format : FloatFormat) (precision : Nat)
    (operation : Operation) (policy : Policy) (candidate selected : Candidate)
    (firstNanos warmIterations warmTotalNanos sink : Nat) : IO Unit :=
  IO.println <|
    s!"{formatName},{format.bitWidth},{precision},{operation.label}," ++
      s!"{candidate.name},{candidate.kind.display}," ++
      s!"{Support.CSV.bool (candidate = selected)}," ++
      s!"{candidate.warmCost policy},{candidate.coldCost policy}," ++
      s!"{candidate.score policy}," ++
      s!"{firstNanos},{warmIterations},{warmTotalNanos},{sink}"

private def calibrateBinary
    {format : FloatFormat}
    {spec : Value format → Value format → Value format}
    (formatName : String) (precision : Nat) (operation : Operation)
    (candidates : CandidateSet (Certified spec))
    (iterations : Nat) : IO Unit := do
  let policy := Policy.default
  let selected := selectCandidate policy candidates.estimates
  let lefts := Public.Sweep.inputsX (Descriptor format)
  let rights := Public.Sweep.inputsY (Descriptor format)
  for candidate in candidates.toList do
    if candidate.estimate.admissible policy then
      let resultRef ← IO.mkRef 0
      let firstStart ← IO.monoNanosNow
      resultRef.set <| Public.Sweep.resultBits <|
        candidate.run lefts[0]! rights[0]!
      let firstStop ← IO.monoNanosNow
      resultRef.set <| binaryLoop candidate.run 64 lefts rights 0
      let warmStart ← IO.monoNanosNow
      resultRef.set <| binaryLoop candidate.run iterations lefts rights 0
      let warmStop ← IO.monoNanosNow
      printRow formatName format precision operation policy candidate.estimate selected
        (firstStop - firstStart) iterations (warmStop - warmStart)
        (← resultRef.get).toNat

private def calibrateUnary
    {format : FloatFormat}
    {spec : Value format → Value format}
    (formatName : String) (precision : Nat) (operation : Operation)
    (candidates : CandidateSet (Certified spec))
    (iterations : Nat) : IO Unit := do
  let policy := Policy.default
  let selected := selectCandidate policy candidates.estimates
  let values :=
    (Public.Sweep.inputsX (Descriptor format)).map fun value =>
      Descriptor.pack (Model.abs value.raw)
  for candidate in candidates.toList do
    if candidate.estimate.admissible policy then
      let resultRef ← IO.mkRef 0
      let firstStart ← IO.monoNanosNow
      resultRef.set <| Public.Sweep.resultBits <|
        candidate.run values[0]!
      let firstStop ← IO.monoNanosNow
      resultRef.set <| unaryLoop candidate.run 64 values 0
      let warmStart ← IO.monoNanosNow
      resultRef.set <| unaryLoop candidate.run iterations values 0
      let warmStop ← IO.monoNanosNow
      printRow formatName format precision operation policy candidate.estimate selected
        (firstStop - firstStart) iterations (warmStop - warmStart)
        (← resultRef.get).toNat

private def calibrateTernary
    {format : FloatFormat}
    {spec : Value format → Value format → Value format → Value format}
    (formatName : String) (precision : Nat) (operation : Operation)
    (candidates : CandidateSet (Certified spec))
    (iterations : Nat) : IO Unit := do
  let policy := Policy.default
  let selected := selectCandidate policy candidates.estimates
  let lefts := Public.Sweep.inputsX (Descriptor format)
  let rights := Public.Sweep.inputsY (Descriptor format)
  let addends := lefts.reverse
  for candidate in candidates.toList do
    if candidate.estimate.admissible policy then
      let resultRef ← IO.mkRef 0
      let firstStart ← IO.monoNanosNow
      resultRef.set <| Public.Sweep.resultBits <|
        candidate.run lefts[0]! rights[0]! addends[0]!
      let firstStop ← IO.monoNanosNow
      resultRef.set <| ternaryLoop candidate.run 64 lefts rights addends 0
      let warmStart ← IO.monoNanosNow
      resultRef.set <| ternaryLoop candidate.run iterations lefts rights addends 0
      let warmStop ← IO.monoNanosNow
      printRow formatName format precision operation policy candidate.estimate selected
        (firstStop - firstStart) iterations (warmStop - warmStart)
        (← resultRef.get).toNat

private def calibrateFormat
    (formatName : String) (format : FloatFormat) (precision iterations : Nat) :
    IO Unit := do
  calibrateBinary formatName precision .add
    (Descriptor.Plan.addCandidates format) iterations
  calibrateBinary formatName precision .sub
    (Descriptor.Plan.subCandidates format) iterations
  calibrateBinary formatName precision .mul
    (Descriptor.Plan.mulCandidates format) iterations
  calibrateBinary formatName precision .div
    (Descriptor.Plan.divCandidates format) iterations
  calibrateUnary formatName precision .sqrt
    (Descriptor.Plan.sqrtCandidates format) iterations
  calibrateTernary formatName precision .fma
    (Descriptor.Plan.fmaCandidates format) iterations

def run : IO Unit := do
  let iterations ← positiveNat "CALIBRATION_ITERATIONS" 100000
  IO.println <|
    "format,storageBits,precision,operation,candidate,kernelClass,selected," ++
      "estimatedWarmCost,estimatedColdCost,estimatedScore," ++
      "firstNanos,warmIterations,warmTotalNanos,sink"
  calibrateFormat "p2" (FloatFormat.ieee 2 1) 2 iterations
  calibrateFormat "p3" (FloatFormat.ieee 2 2) 3 iterations
  calibrateFormat "p4" (FloatFormat.ieee 2 3) 4 iterations
  calibrateFormat "p5" (FloatFormat.ieee 3 4) 5 iterations
  calibrateFormat "OCP E5M2 descriptor" FloatFormat.e5m2 3 iterations
  calibrateFormat "ONNX E5M2FNUZ descriptor" FloatFormat.e5m2fnuz 3 iterations

end FloatLibBenchmarks.Kernels.BackendCalibration

public def main : IO Unit :=
  FloatLibBenchmarks.Kernels.BackendCalibration.run
