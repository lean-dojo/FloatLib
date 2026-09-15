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
import FloatLibTests.Conformance.Posit.Quire
import FloatLibTests.Regression.ArbParser
import FloatLibTests.Regression.BinaryInterchange.ExecFloatInstances
import FloatLibTests.Regression.BinaryInterchange.ExecFloatTranscendentals
import FloatLibTests.Regression.BinaryInterchange.Model
import FloatLibTests.Regression.BinaryInterchange.NativeBinary64
import FloatLibTests.Regression.BinaryInterchange.NativeProduct
import FloatLibTests.Regression.BinaryInterchange.PolicyRounding
import FloatLibTests.Regression.BinaryInterchange.SmallWord
import FloatLibTests.Regression.BinaryInterchange.TinyArithmetic
import FloatLibTests.Regression.BinaryInterchange.TwoWordMul
import FloatLibTests.Regression.BinaryInterchange.WideLimb
import FloatLibTests.Regression.Interval.ArbTranscendentals
meta import FloatLib.Examples
meta import FloatLibTests

/-!
# Native regression checks

`lake -d tests test` builds the conformance proofs and runs the model, kernel, transcendental,
host-FPU, and tutorial checks. Select a suite with `lake -d tests exe check SUITE`.
The `arb` suite also requires python-flint.
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
    { title := "public instances"
      body := ExecFloatInstances.report.get
      failures := ExecFloatInstances.totalFailures.get },
    { title := "rounding policies"
      body := PolicyRounding.report.get
      failures := PolicyRounding.totalFailures.get },
    Conformance.Formats.LowBit.report.get
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
  let imported := FloatLib.Floats.ExecFloat.Binary.ofFloat32 (Float32.ofBits bits)
  let exported := FloatLib.Floats.ExecFloat.Binary.toFloat32
    (FloatLib.Floats.ExecFloat.Binary.ofBits32 bits)
  let expected := canonicalBinary32Bits bits
  FloatLib.Floats.ExecFloat.Binary.toBits32 imported == expected && exported.toBits == expected

@[noinline] private def binary64RoundTripMatches (bits : UInt64) : Bool :=
  let imported := FloatLib.Floats.ExecFloat.Binary.ofFloat (Float.ofBits bits)
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
  let specialFailures ← runCheck "arbitraryFormatSpecialValues" failArbitraryFormatSpecialValues
  let constantFailures ← runCheck "generatedConstants" failGeneratedConstants
  let boundedGenerationFailures ← runCheck "boundedGeneration" failBoundedGeneration
  let total := specialFailures + constantFailures + boundedGenerationFailures
  IO.println s!"TOTAL: {total}"
  pure <| exitCode total

private def arb : IO UInt32 := do
  let parserFailures := FloatLibTests.Regression.ArbParser.totalFailures.get
  IO.println s!"arbParser: {parserFailures}"
  let runtimeFailures ←
    FloatLibTests.Regression.Interval.ArbTranscendentals.run
  let total := parserFailures + runtimeFailures
  IO.println s!"TOTAL: {total}"
  pure <| exitCode total

private def exampleCheck : IO UInt32 := do
  FloatLib.Examples.FormatComparison.showComparison
  return 0

private def allChecks : IO UInt32 := do
  let mut status := 0
  for run in [core, transcendentals, kernels, native, exampleCheck] do
    if (← run) != 0 then
      status := 1
  return status

private def usage : String :=
  "usage: check [all|core|kernels|transcendentals|native|example|arb]"

end FloatLibTests.Check

open FloatLibTests.Check in
/-- Run the selected checks and return a nonzero status if any check fails. -/
public def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["all"] => allChecks
  | ["core"] => core
  | ["kernels"] => kernels
  | ["transcendentals"] => transcendentals
  | ["native"] => native
  | ["example"] => exampleCheck
  | ["arb"] => arb
  | ["--help"] | ["-h"] => IO.println usage; return 0
  | _ => IO.eprintln usage; return 2
