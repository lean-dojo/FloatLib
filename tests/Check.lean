/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Examples.FormatComparison
import FloatLib.Floats.Formats.IEEE754.Native
import FloatLibTests.Accounting
import FloatLibTests.Conformance.BinaryInterchange.NativeExecution
import FloatLibTests.Conformance.Formats.LowBit
import FloatLibTests.Conformance.Formats.MXStandard
import FloatLibTests.Conformance.P3109.Block
import FloatLibTests.Conformance.Posit.Quire
import FloatLibTests.Regression.ArbParser
import FloatLibTests.Regression.BinaryInterchange.ExecFloatInstances
import FloatLibTests.Regression.BinaryInterchange.ExecFloatTranscendentals
import FloatLibTests.Regression.BinaryInterchange.Model
import FloatLibTests.Regression.BinaryInterchange.NativeBinary64
import FloatLibTests.Regression.BinaryInterchange.NativeProduct
import FloatLibTests.Regression.BinaryInterchange.PolicyRounding
import FloatLibTests.Regression.BinaryInterchange.RoundingDirections
import FloatLibTests.Regression.BinaryInterchange.SmallWord
import FloatLibTests.Regression.BinaryInterchange.Text
import FloatLibTests.Regression.BinaryInterchange.TinyArithmetic
import FloatLibTests.Regression.BinaryInterchange.TwoWordMul
import FloatLibTests.Regression.BinaryInterchange.WideLimb
import FloatLibTests.Regression.Display
import FloatLibTests.Regression.Interval.ArbTranscendentals
import FloatLibTests.Regression.Interval.ElementaryArb
import FloatLibTests.Regression.RationalPower
meta import FloatLib.Examples
meta import FloatLibTests

/-!
# Native regression checks

`lake -d tests test` builds the conformance proofs and runs the model, kernel, transcendental,
rational-power, host-FPU, and tutorial checks. Select a suite with `lake -d tests exe check SUITE`.
The `powers` suite prints the time of each group. The `reduction` suite, which `all` leaves out,
reduces sine and cosine arguments that need the `2^20`- and `2^21`-bit levels of `2 / pi` and
prints its time. The `arb` suite also requires python-flint.
-/

-- Reports force cached regression thunks only in the selected IO branch. Closed-expression
-- extraction would otherwise move those forces back into module initialization.
set_option compiler.extract_closed false

namespace FloatLibTests.Check

open FloatLibTests.Accounting
open FloatLibTests.Fixtures.NativeIEEE
open FloatLibTests.Regression.BinaryInterchange
open FloatLibTests.Regression.BinaryInterchange.ExecFloatTranscendentals

private def core : IO UInt32 :=
  runSectionedReport #[
    Model.report.get,
    Text.report.get,
    FloatLibTests.Regression.Display.report.get,
    { title := "public instances"
      body := ExecFloatInstances.report.get
      failures := ExecFloatInstances.totalFailures.get },
    { title := "rounding policies"
      body := PolicyRounding.report.get
      failures := PolicyRounding.totalFailures.get },
    { title := "rounding directions"
      body := RoundingDirections.report.get
      failures := RoundingDirections.totalFailures.get },
    Conformance.Formats.LowBit.report.get,
    Conformance.Formats.MXStandard.report.get,
    Conformance.P3109.Block.report.get
  ]

private def kernels : IO UInt32 :=
  let quireFailures := Conformance.Posit.Quire.totalFailures.get
  runSectionedReport #[
    { title := "native and fixed-limb kernels"
      body := NativeProduct.report.get
      failures := NativeProduct.totalFailures.get },
    { title := "binary64 division dispatch"
      body := NativeBinary64Division.report.get
      failures := NativeBinary64Division.totalFailures.get },
    { title := "binary64 square-root dispatch"
      body := NativeBinary64Sqrt.report.get
      failures := NativeBinary64Sqrt.totalFailures.get },
    { title := "binary64 subtraction dispatch"
      body := NativeBinary64Subtraction.report.get
      failures := NativeBinary64Subtraction.totalFailures.get },
    { title := "one-word division"
      body := SmallWordDiv.report.get
      failures := SmallWordDiv.totalFailures.get },
    { title := "one-word finite dispatch"
      body := SmallWordFinite.report.get
      failures := SmallWordFinite.totalFailures.get },
    { title := "one-word multiplication"
      body := SmallWordMul.report.get
      failures := SmallWordMul.totalFailures.get },
    TinyArithmetic.report.get,
    { title := "two-word multiplication"
      body := TwoWordMul.report.get
      failures := TwoWordMul.totalFailures.get },
    { title := "wide-limb kernels"
      body := WideLimb.report.get
      failures := WideLimb.totalFailures.get },
    { title := "posit quire"
      body := s!"TOTAL: {quireFailures}"
      failures := quireFailures }
  ]

private def canonicalBinary32Bits (bits : UInt32) : UInt32 :=
  FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32.toUInt32 <|
    FloatLib.Floats.Formats.BinaryInterchange.Model.canonicalizeModel
      (FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32.ofUInt32 bits)

private def canonicalBinary64Bits (bits : UInt64) : UInt64 :=
  FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64.toUInt64 <|
    FloatLib.Floats.Formats.BinaryInterchange.Model.canonicalizeModel
      (FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64.ofUInt64 bits)

@[noinline] private def binary32RoundTripMatches (bits : UInt32) : Bool :=
  let imported : FloatLib.Floats.Binary32 :=
    FloatLib.Floats.ExecFloat.Binary.ofFloat32 (Float32.ofBits bits)
  let exported := FloatLib.Floats.ExecFloat.Binary.toFloat32
    (FloatLib.Floats.ExecFloat.Binary.ofBits32 bits)
  let expected := canonicalBinary32Bits bits
  FloatLib.Floats.ExecFloat.Binary.toBits32 imported == expected && exported.toBits == expected

@[noinline] private def binary64RoundTripMatches (bits : UInt64) : Bool :=
  let imported : FloatLib.Floats.Binary64 :=
    FloatLib.Floats.ExecFloat.Binary.ofFloat (Float.ofBits bits)
  let exported := FloatLib.Floats.ExecFloat.Binary.toFloat
    (FloatLib.Floats.ExecFloat.Binary.ofBits64 bits)
  let expected := canonicalBinary64Bits bits
  FloatLib.Floats.ExecFloat.Binary.toBits64 imported == expected && exported.toBits == expected

private def binary32InteropFailures : Thunk Nat := ⟨fun _ =>
  countWhereFailures (interopInputs binary32Cases) binary32RoundTripMatches⟩

private def binary64InteropFailures : Thunk Nat := ⟨fun _ =>
  countWhereFailures (interopInputs binary64Cases) binary64RoundTripMatches⟩

private def native : IO UInt32 :=
  runSectionedReport #[
    { title := "native arithmetic"
      body := Conformance.BinaryInterchange.NativeExecution.report.get
      failures :=
        Conformance.BinaryInterchange.NativeExecution.totalFailures.get },
    ReportSection.ofRows "native bit interop"
      #[ ("binary32 round trips", binary32InteropFailures.get)
       , ("binary64 round trips", binary64InteropFailures.get) ]
  ]

private def runCheck (name : String) (compute : Thunk Nat) : IO Nat := do
  IO.println s!"running {name}"
  let failures := compute.get
  IO.println s!"{name}: {failures}"
  pure failures

private def transcendentals : IO UInt32 := do
  let fixtureFailures ← runCheck "mpfrFixtures" failMpfrFixtures
  let specialFailures ← runCheck "specialValueMatrix" failSpecialValueMatrix
  let nanFailures ← runCheck "nanPayloads" failNaNPayloads
  let constantFailures ← runCheck "provedConstants" failProvedConstants
  let piFailures ← runCheck "pi" failPi
  let generatedScaleFailures ← runCheck "generatedScale" failGeneratedScale
  let explicitConfigurationFailures ←
    runCheck "explicitConfigurationReduction" failExplicitConfigurationReduction
  let progressFailures ← runCheck "reductionProgress" failReductionProgress
  let largeFailures ← runCheck "largeArguments" failLargeArguments
  let attemptFailures ← runCheck "reductionAttempts" failReductionAttempts
  let tinyFailures ← runCheck "tinyDyadicSine" failTinyDyadicSine
  let certifiedFailures ← runCheck "certifiedStable" failCertifiedStable
  let rejectionFailures ← runCheck "certifiedStableRejection" failCertifiedStableRejection
  let powFailures ← runCheck "certifiedPow" failCertifiedPow
  let configuredFailures ← runCheck "configuredCertified" failConfiguredCertified
  let total := fixtureFailures + specialFailures + nanFailures + constantFailures + piFailures +
    generatedScaleFailures + explicitConfigurationFailures + progressFailures + largeFailures +
    attemptFailures + tinyFailures + certifiedFailures + rejectionFailures + powFailures +
    configuredFailures
  IO.println s!"TOTAL: {total}"
  pure <| exitCode total

private def reduction : IO UInt32 := do
  let start ← IO.monoMsNow
  let failures ← runCheck "slowTrigReduction" failSlowTrigReduction
  let stop ← IO.monoMsNow
  IO.println s!"slowTrigReduction time: {stop - start} ms"
  IO.println s!"TOTAL: {failures}"
  pure <| exitCode failures

private def powers : IO UInt32 := do
  let mut total := 0
  for (name, compute) in FloatLibTests.Regression.RationalPower.checks do
    let start ← IO.monoMsNow
    let failures ← runCheck name compute
    let stop ← IO.monoMsNow
    IO.println s!"{name} time: {stop - start} ms"
    total := total + failures
  IO.println s!"TOTAL: {total}"
  pure <| exitCode total

private def arb : IO UInt32 := do
  let parserFailures := FloatLibTests.Regression.ArbParser.totalFailures.get
  IO.println s!"arbParser: {parserFailures}"
  let runtimeFailures ←
    FloatLibTests.Regression.Interval.ArbTranscendentals.run
  let elementaryFailures ← FloatLibTests.Regression.Interval.ElementaryArb.run
  let total := parserFailures + runtimeFailures + elementaryFailures
  IO.println s!"TOTAL: {total}"
  pure <| exitCode total

/--
One shard of the opt-in exhaustive fused multiply-add campaign of
`Regression.BinaryInterchange.RoundingDirections`. The shards split the 256 first operands, so at
most 256 shards keep every shard nonempty.
-/
private def fmaExhaustive (shardIndex shardCount : String) : IO UInt32 := do
  match shardIndex.toNat?, shardCount.toNat? with
  | some index, some count =>
      if count == 0 || count > 256 || index ≥ count then
        IO.eprintln
          "fma-exhaustive: SHARD_COUNT must be from 1 to 256 and SHARD_INDEX below it"
        return 2
      let failures := RoundingDirections.exhaustiveFmaFailures index count
      IO.println s!"fma-exhaustive shard {index} of {count}: {failures}"
      pure <| exitCode failures
  | _, _ =>
      IO.eprintln "fma-exhaustive: SHARD_INDEX and SHARD_COUNT must be natural numbers"
      return 2

private def exampleCheck : IO UInt32 := do
  FloatLib.Examples.FormatComparison.showComparison
  return 0

private def allChecks : IO UInt32 := do
  let mut status := 0
  for run in [core, transcendentals, powers, kernels, native, exampleCheck] do
    if (← run) != 0 then
      status := 1
  return status

private def usage : String :=
  "usage: check [all|core|kernels|transcendentals|reduction|powers|native|example|arb]\n" ++
    "       check fma-exhaustive SHARD_INDEX SHARD_COUNT"

end FloatLibTests.Check

open FloatLibTests.Check in
/-- Run the selected checks and return a nonzero status if any check fails. -/
public def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["all"] => allChecks
  | ["core"] => core
  | ["kernels"] => kernels
  | ["transcendentals"] => transcendentals
  | ["reduction"] => reduction
  | ["powers"] => powers
  | ["native"] => native
  | ["example"] => exampleCheck
  | ["arb"] => arb
  | ["fma-exhaustive", shardIndex, shardCount] => fmaExhaustive shardIndex shardCount
  | ["--help"] | ["-h"] => IO.println usage; return 0
  | _ => IO.eprintln usage; return 2
