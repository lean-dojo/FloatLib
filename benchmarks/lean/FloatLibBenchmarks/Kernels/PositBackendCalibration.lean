/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.Sweep
import FloatLibBenchmarks.Support.CSV
import FloatLibBenchmarks.Support.Posit

/-!
# Cold-start and warm-kernel calibration for byte-sized posits

This executable measures every admissible certified candidate exposed by the public Posit
Standard byte planner. It complements `BackendCalibration`, which performs the same experiment
for binary descriptors.

The candidate portfolios come directly from `Posit.Configured.Plan`; this harness does not copy
the planner's eligibility rules or executable kernels. For every candidate it reports:

* the first call, including lazy exhaustive-table construction;
* a warmed repeated-call interval over the shared deterministic workload; and
* whether `Policy.default` selects that candidate.

Widths 4, 6, and 8 expose the table-size crossovers that matter in practice. Repeated runs should
be summarized with a robust statistic before changing the static engineering estimates.
-/

open FloatLib.Floats
open FloatLib.Floats.ExecFloat.Backend
open FloatLibBenchmarks.Support
open FloatLibBenchmarks.Support.Environment
open FloatLib.Floats.Formats.Posit
open FloatLibBenchmarks.Public.Sweep
open FloatLibBenchmarks.Support.Posit

namespace FloatLibBenchmarks.Kernels.PositBackendCalibration

abbrev Value (format : Format) (width_le : format.bits ≤ 8) :=
  ExecFloat
    (Configured.Family format
      (Configured.Code (.byte width_le)) (.byte width_le))

private instance valueBenchmarkCarrier
    (format : Format) (width_le : format.bits ≤ 8) :
    BenchmarkCarrier
      (Configured.Family format
        (Configured.Code (.byte width_le)) (.byte width_le)) Format Model :=
  configuredBenchmarkCarrier format (.byte width_le)

private instance valueInhabited
    (format : Format) (width_le : format.bits ≤ 8) :
    Inhabited (Value format width_le) where
  default := Configured.Family.ofModel (Model.zero format)

@[noinline] private def binaryLoop {format : Format}
    {width_le : format.bits ≤ 8}
    (run : Value format width_le → Value format width_le → Value format width_le) :
    Nat → Array (Value format width_le) → Array (Value format width_le) → UInt64 → UInt64
  | 0, _, _, sink => sink
  | iterations + 1, lefts, rights, sink =>
      let index := iterations &&& 15
      let result := run lefts[index]! rights[index]!
      binaryLoop run iterations lefts rights
        (Support.Sink.mix sink
          (FloatLibBenchmarks.Support.Posit.resultBits result))

@[noinline] private def unaryLoop {format : Format}
    {width_le : format.bits ≤ 8}
    (run : Value format width_le → Value format width_le) :
    Nat → Array (Value format width_le) → UInt64 → UInt64
  | 0, _, sink => sink
  | iterations + 1, values, sink =>
      let index := iterations &&& 15
      let result := run values[index]!
      unaryLoop run iterations values
        (Support.Sink.mix sink
          (FloatLibBenchmarks.Support.Posit.resultBits result))

@[noinline] private def ternaryLoop {format : Format}
    {width_le : format.bits ≤ 8}
    (run :
      Value format width_le → Value format width_le →
        Value format width_le → Value format width_le) :
    Nat → Array (Value format width_le) → Array (Value format width_le) →
      Array (Value format width_le) → UInt64 → UInt64
  | 0, _, _, _, sink => sink
  | iterations + 1, lefts, rights, addends, sink =>
      let index := iterations &&& 15
      let result := run lefts[index]! rights[index]! addends[index]!
      ternaryLoop run iterations lefts rights addends
        (Support.Sink.mix sink
          (FloatLibBenchmarks.Support.Posit.resultBits result))

private def printRow
    (format : Format) (operation : Operation) (policy : Policy)
    (candidate selected : Candidate)
    (firstNanos warmIterations warmTotalNanos sink : Nat) : IO Unit :=
  IO.println <|
    s!"posit{format.bits},{format.bits},{operation.label}," ++
      s!"{candidate.name},{candidate.kind.display}," ++
      s!"{Support.CSV.bool (candidate = selected)}," ++
      s!"{candidate.warmCost policy},{candidate.coldCost policy}," ++
      s!"{candidate.score policy}," ++
      s!"{firstNanos},{warmIterations},{warmTotalNanos}," ++
      s!"{warmTotalNanos / warmIterations},{sink}"

private def calibrateBinary
    {format : Format} {width_le : format.bits ≤ 8}
    {spec : Value format width_le → Value format width_le → Value format width_le}
    (operation : Operation) (candidates : CandidateSet (Certified spec))
    (iterations : Nat) : IO Unit := do
  let policy := Policy.default
  let selected := selectCandidate policy candidates.estimates
  let lefts := inputsX (Configured.Family format
    (Configured.Code (.byte width_le)) (.byte width_le))
  let rights := inputsY (Configured.Family format
    (Configured.Code (.byte width_le)) (.byte width_le))
  for candidate in candidates.toList do
    if candidate.estimate.admissible policy then
      let resultRef ← IO.mkRef 0
      let firstStart ← IO.monoNanosNow
      resultRef.set <|
        (FloatLibBenchmarks.Support.Posit.resultBits <|
          candidate.run lefts[0]! rights[0]!).toNat
      let firstStop ← IO.monoNanosNow
      resultRef.set <| (binaryLoop candidate.run 64 lefts rights 0).toNat
      let warmStart ← IO.monoNanosNow
      resultRef.set <| (binaryLoop candidate.run iterations lefts rights 0).toNat
      let warmStop ← IO.monoNanosNow
      printRow format operation policy candidate.estimate selected
        (firstStop - firstStart) iterations (warmStop - warmStart)
        (← resultRef.get)

private def calibrateUnary
    {format : Format} {width_le : format.bits ≤ 8}
    {spec : Value format width_le → Value format width_le}
    (operation : Operation) (candidates : CandidateSet (Certified spec))
    (iterations : Nat) : IO Unit := do
  let policy := Policy.default
  let selected := selectCandidate policy candidates.estimates
  let values := inputsSqrt (Configured.Family format
    (Configured.Code (.byte width_le)) (.byte width_le))
  for candidate in candidates.toList do
    if candidate.estimate.admissible policy then
      let resultRef ← IO.mkRef 0
      let firstStart ← IO.monoNanosNow
      resultRef.set <|
        (FloatLibBenchmarks.Support.Posit.resultBits <|
          candidate.run values[0]!).toNat
      let firstStop ← IO.monoNanosNow
      resultRef.set <| (unaryLoop candidate.run 64 values 0).toNat
      let warmStart ← IO.monoNanosNow
      resultRef.set <| (unaryLoop candidate.run iterations values 0).toNat
      let warmStop ← IO.monoNanosNow
      printRow format operation policy candidate.estimate selected
        (firstStop - firstStart) iterations (warmStop - warmStart)
        (← resultRef.get)

private def calibrateTernary
    {format : Format} {width_le : format.bits ≤ 8}
    {spec :
      Value format width_le → Value format width_le →
        Value format width_le → Value format width_le}
    (operation : Operation) (candidates : CandidateSet (Certified spec))
    (iterations : Nat) : IO Unit := do
  let policy := Policy.default
  let selected := selectCandidate policy candidates.estimates
  let lefts := inputsX (Configured.Family format
    (Configured.Code (.byte width_le)) (.byte width_le))
  let rights := inputsY (Configured.Family format
    (Configured.Code (.byte width_le)) (.byte width_le))
  let addends := lefts.reverse
  for candidate in candidates.toList do
    if candidate.estimate.admissible policy then
      let resultRef ← IO.mkRef 0
      let firstStart ← IO.monoNanosNow
      resultRef.set <|
        (FloatLibBenchmarks.Support.Posit.resultBits <|
          candidate.run lefts[0]! rights[0]! addends[0]!).toNat
      let firstStop ← IO.monoNanosNow
      resultRef.set <| (ternaryLoop candidate.run 64 lefts rights addends 0).toNat
      let warmStart ← IO.monoNanosNow
      resultRef.set <|
        (ternaryLoop candidate.run iterations lefts rights addends 0).toNat
      let warmStop ← IO.monoNanosNow
      printRow format operation policy candidate.estimate selected
        (firstStop - firstStart) iterations (warmStop - warmStart)
        (← resultRef.get)

private def calibrateFormat
    (format : Format) (width_le : format.bits ≤ 8) (iterations : Nat) :
    IO Unit := do
  calibrateBinary .add
    (Configured.Plan.addByteCandidates format width_le) iterations
  calibrateBinary .sub
    (Configured.Plan.subByteCandidates format width_le) iterations
  calibrateBinary .mul
    (Configured.Plan.mulByteCandidates format width_le) iterations
  calibrateBinary .div
    (Configured.Plan.divByteCandidates format width_le) iterations
  calibrateUnary .sqrt
    (Configured.Plan.sqrtByteCandidates format width_le) iterations
  calibrateTernary .fma
    (Configured.Plan.fmaByteCandidates format width_le) iterations

def run : IO Unit := do
  let iterations ← positiveNat "POSIT_CALIBRATION_ITERATIONS" 100000
  IO.println <|
    "format,totalBits,operation,candidate,kernelClass,selected," ++
      "estimatedWarmCost,estimatedColdCost,estimatedScore," ++
      "firstNanos,warmIterations,warmTotalNanos,nanosPerOperation,sink"
  calibrateFormat (ExecFloat.Posit.format 4) (by decide) iterations
  calibrateFormat (ExecFloat.Posit.format 6) (by decide) iterations
  calibrateFormat (ExecFloat.Posit.format 8) (by decide) iterations

end FloatLibBenchmarks.Kernels.PositBackendCalibration

public def main : IO Unit :=
  FloatLibBenchmarks.Kernels.PositBackendCalibration.run
