/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.Sweep
import FloatLibBenchmarks.Support.CSV

/-!
# Configured low-bit FMA calibration

This executable explains the configured-binary FMA crossover at encoded widths four through
eight. It reads the certified candidate portfolio from the public `ExecFloat.Binary` capability,
then reports both static selection metadata and direct cold/warm measurements for every candidate
within a configurable measurement-memory ceiling.

The planner's own memory ceilings are not reused as measurement filters. This is intentional:
diagnostics must be able to measure a candidate that a policy rejects, without changing the
policy or arithmetic implementation merely to inspect it. By default, tables through two
mebibytes are measured, which includes the seven-bit FMA table but skips the sixteen-mebibyte
eight-bit table.
-/

open FloatLib.Floats
open FloatLib.Floats.ExecFloat.Backend
open FloatLibBenchmarks.Support
open FloatLibBenchmarks.Support.Environment
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics

namespace FloatLibBenchmarks.Kernels.ConfiguredLowBitCalibration

@[noinline] private def ternaryLoop
    {F : Type} [EncodedFormat F] [BenchmarkCarrier F FloatFormat Model]
    (run : ExecFloat F → ExecFloat F → ExecFloat F → ExecFloat F) :
    Nat → Array (ExecFloat F) → Array (ExecFloat F) →
      Array (ExecFloat F) → UInt64 → UInt64
  | 0, _, _, _, sink => sink
  | iterations + 1, lefts, rights, addends, sink =>
      let index := iterations &&& 15
      let result := run lefts[index]! rights[index]! addends[index]!
      ternaryLoop run iterations lefts rights addends
        (Support.Sink.mix sink (Public.Sweep.resultBits result))

private def printMetadata
    (formatName : String) (storageBits precision : Nat)
    (measurementLimit : Nat) (candidate balancedSelected throughputSelected : Candidate)
    (measurementStatus : String)
    (firstNanos warmIterations warmTotalNanos nanosPerOperation sink : String) :
    IO Unit :=
  IO.println <|
      s!"{formatName},{storageBits},{precision},fma," ++
      s!"{candidate.name},{candidate.kind.display},{candidate.residentBytes}," ++
      s!"{Support.CSV.bool (candidate.admissible Policy.default)}," ++
      s!"{Support.CSV.bool (candidate = balancedSelected)},{candidate.score Policy.default}," ++
      s!"{Support.CSV.bool (candidate.admissible Policy.throughput)}," ++
      s!"{Support.CSV.bool (candidate = throughputSelected)},{candidate.score Policy.throughput}," ++
      s!"{measurementLimit},{measurementStatus},{firstNanos},{warmIterations}," ++
      s!"{warmTotalNanos},{nanosPerOperation},{sink}"

private def calibrateFma
    {F : Type} [PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F FloatFormat Model] [ExecFloat.Fma F]
    (formatName : String) (storageBits precision iterations measurementLimit : Nat) :
    IO Unit := do
  let candidates := ExecFloat.Fma.candidates (F := F)
  let estimates := candidates.estimates
  let balancedSelected := selectCandidate Policy.default estimates
  let throughputSelected := selectCandidate Policy.throughput estimates
  let lefts := Public.Sweep.inputsX F
  let rights := Public.Sweep.inputsY F
  let addends := lefts.reverse
  for candidate in candidates.toList do
    if candidate.estimate.residentBytes ≤ measurementLimit then
      let resultRef ← IO.mkRef 0
      let firstStart ← IO.monoNanosNow
      resultRef.set <| Public.Sweep.resultBits <|
        candidate.run lefts[0]! rights[0]! addends[0]!
      let firstStop ← IO.monoNanosNow
      resultRef.set <| ternaryLoop candidate.run 64 lefts rights addends 0
      let warmStart ← IO.monoNanosNow
      resultRef.set <| ternaryLoop candidate.run iterations lefts rights addends 0
      let warmStop ← IO.monoNanosNow
      let warmTotalNanos := warmStop - warmStart
      printMetadata formatName storageBits precision measurementLimit
        candidate.estimate balancedSelected throughputSelected "measured"
        (toString (firstStop - firstStart)) (toString iterations)
        (toString warmTotalNanos) (toString (warmTotalNanos / iterations))
        (toString (← resultRef.get).toNat)
    else
      printMetadata formatName storageBits precision measurementLimit
        candidate.estimate balancedSelected throughputSelected "skipped-resident-limit"
        "" "" "" "" ""

def run : IO Unit := do
  let iterations ←
    positiveNat "CONFIGURED_LOWBIT_CALIBRATION_ITERATIONS" 100000
  let measurementLimit ←
    positiveNat "CONFIGURED_LOWBIT_CALIBRATION_MAX_RESIDENT_BYTES" (2 * 1024 * 1024)
  IO.println <|
    "format,totalBits,precision,operation,candidate,kernelClass,residentBytes," ++
      "balancedAdmissible,balancedSelected,balancedScore," ++
      "throughputAdmissible,throughputSelected,throughputScore," ++
      "measurementLimitBytes,measurementStatus,firstNanos,warmIterations," ++
      "warmTotalNanos,nanosPerOperation,sink"
  calibrateFma (F := ExecFloat.Binary.Family 2 1)
    "binary4-e2m1" 4 2 iterations measurementLimit
  calibrateFma (F := ExecFloat.Binary.Family 2 2)
    "binary5-e2m2" 5 3 iterations measurementLimit
  calibrateFma (F := ExecFloat.Binary.Family 3 2)
    "binary6-e3m2" 6 3 iterations measurementLimit
  calibrateFma (F := ExecFloat.Binary.Family 3 3)
    "binary7-e3m3" 7 4 iterations measurementLimit
  calibrateFma (F := ExecFloat.Binary.Family 4 3)
    "binary8-e4m3" 8 4 iterations measurementLimit

end FloatLibBenchmarks.Kernels.ConfiguredLowBitCalibration

public def main : IO Unit :=
  FloatLibBenchmarks.Kernels.ConfiguredLowBitCalibration.run
