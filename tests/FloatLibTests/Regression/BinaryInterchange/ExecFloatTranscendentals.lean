/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals
public import FloatLibTests.Accounting
public import FloatLibTests.Regression.BinaryInterchange.Harness

/-!
# Regression checks for format-generic executable transcendentals

These checks exercise special-value behavior in binary16, bfloat16, binary32, binary64, and a
custom tiny format, validate generated constants, and check argument-reduction budgets for formats
with wide exponent fields.

Run the native report with:

```text
lake -d tests exe check transcendentals
```
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.ExecFloatTranscendentals

abbrev f32 := FloatFormat.binary32

open FloatLibTests.Accounting

def specialValueFailures (fmt : FloatFormat) : Nat :=
  let positiveZero := Model.posZero fmt
  let negativeZero := Model.negZero fmt
  let positiveInfinity := Model.posInf fmt
  let negativeInfinity := Model.negInf fmt
  let one := Model.posOne fmt
  let negativeOne := Model.negOne fmt
  let canonicalNaN := Model.canonicalNaN fmt
  let checks :=
    [ Harness.sameBits (Model.exp negativeInfinity) positiveZero
    , Harness.sameBits (Model.exp positiveInfinity) positiveInfinity
    , Harness.sameBits (Model.log positiveZero) negativeInfinity
    , Harness.sameBits (Model.log negativeZero) negativeInfinity
    , Model.isNaN (Model.log negativeOne)
    , Harness.sameBits (Model.sinh negativeInfinity) negativeInfinity
    , Harness.sameBits (Model.cosh negativeInfinity) positiveInfinity
    , Harness.sameBits (Model.tanh positiveInfinity) one
    , Harness.sameBits (Model.tanh negativeInfinity) negativeOne
    , Harness.sameBits (Model.sin positiveZero) positiveZero
    , Harness.sameBits (Model.sin negativeZero) negativeZero
    , Harness.sameBits (Model.cos positiveZero) one
    , Model.isNaN (Model.sin positiveInfinity)
    , Model.isNaN (Model.cos negativeInfinity)
    , Model.isNaN (Model.exp canonicalNaN)
    ]
  countFailures checks

def failArbitraryFormatSpecialValues : Thunk Nat := ⟨fun _ =>
  specialValueFailures FloatFormat.binary16 +
  specialValueFailures FloatFormat.bfloat16 +
  specialValueFailures FloatFormat.binary32 +
  specialValueFailures FloatFormat.binary64 +
  specialValueFailures (FloatFormat.ieee 3 4)⟩

def failGeneratedConstants : Thunk Nat := ⟨fun _ =>
  let config := Model.Transcendentals.Config.binary32
  countFailures
    [ Model.Transcendentals.Config.generateLn2Fixed config.fixed == config.ln2Fixed
    , Model.Transcendentals.Config.generateHalfPiFixed config.trigFixed ==
        config.halfPiFixed
    ]⟩

abbrev wideExponentFormat : FloatFormat :=
  FloatFormat.ieee 20 37

/--
Check that default generation remains practical for a wide exponent field.

The full-range trigonometric scale would exceed half a million bits. The bounded policy retains the
destination precision and guard bits while capping only the exponent-range contribution.
-/
def failBoundedGeneration : Thunk Nat := ⟨fun _ =>
  let policy := Model.Transcendentals.GenerationPolicy.standard
  let config := Model.Transcendentals.Config.generated wideExponentFormat
  let expectedScale :=
    Nat.min (Int.toNat wideExponentFormat.maxNormalExponent)
      policy.trigExponentBudget +
      wideExponentFormat.fracWidth + policy.guardBits
  let fullRangeScale :=
    Int.toNat wideExponentFormat.maxNormalExponent +
      wideExponentFormat.fracWidth + policy.guardBits
  countFailures
    [ config.fixed == wideExponentFormat.fracWidth + policy.guardBits
    , config.trigFixed == expectedScale
    , decide (config.trigFixed < fullRangeScale)
    , decide (config.halfPiFixed > 0)
    ]⟩

/-- Oversized inputs report the same budget failure for either sign and map to NaN in value APIs. -/
def failReductionBudget : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary128
  let config := Model.Transcendentals.Config.forFormat fmt
  let oversized := Model.roundDyadic fmt
    { negative := false, significand := 1, exponent := 5000 }
  let expected : Model.Transcendentals.TrigReductionError := ⟨5000, 4096⟩
  let rejected (x : Model fmt) : Bool :=
    match Model.sinCosWithResult config x with
    | .error error => error == expected
    | .ok _ => false
  let defaultRejected :=
    match Model.sinCosResult oversized with
    | .error error => error == expected
    | .ok _ => false
  let tiny := Model.posMinSubnormal fmt
  let tinyAccepted :=
    match Model.sinCosWithResult config tiny with
    | .ok (sine, cosine) =>
        Harness.sameBits sine tiny && Harness.sameBits cosine (Model.posOne fmt)
    | .error _ => false
  countFailures
    [ rejected oversized
    , rejected (Model.neg oversized)
    , defaultRejected
    , Model.isNaN (Model.sin oversized)
    , Model.isNaN (Model.cos oversized)
    , tinyAccepted
    ]⟩

/-- An explicit small budget rejects the next exponent; full-range generation accepts it. -/
def failCustomReductionBudget : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.ieee 5 7
  let bounded := Model.Transcendentals.Config.generatedWith
    { trigExponentBudget := 2 } fmt
  let full := Model.Transcendentals.Config.generatedFullRange fmt
  let atBudget := Model.roundDyadic fmt
    { negative := false, significand := 1, exponent := 2 }
  let aboveBudget := Model.roundDyadic fmt
    { negative := false, significand := 1, exponent := 3 }
  let accepts (config : Model.Transcendentals.Config) (x : Model fmt) : Bool :=
    match Model.sinCosWithResult config x with
    | .ok _ => true
    | .error _ => false
  let reportsExponent :=
    match Model.sinCosWithResult bounded aboveBudget with
    | .error error => error == ⟨3, 2⟩
    | .ok _ => false
  countFailures
    [ accepts bounded atBudget
    , reportsExponent
    , accepts full aboveBudget
    ]⟩

def report : Thunk String := ⟨fun _ =>
  let rows :=
    [ ("arbitraryFormatSpecialValues", failArbitraryFormatSpecialValues.get)
    , ("generatedConstants", failGeneratedConstants.get)
    , ("boundedGeneration", failBoundedGeneration.get)
    , ("reductionBudget", failReductionBudget.get)
    , ("customReductionBudget", failCustomReductionBudget.get)
    ]
  renderFailureReport rows⟩

end FloatLibTests.Regression.BinaryInterchange.ExecFloatTranscendentals
