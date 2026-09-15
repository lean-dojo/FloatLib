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
custom tiny format, validate generated constants, and construct the bounded default configuration
for a format with a wide exponent field.

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

def report : Thunk String := ⟨fun _ =>
  let rows :=
    [ ("arbitraryFormatSpecialValues", failArbitraryFormatSpecialValues.get)
    , ("generatedConstants", failGeneratedConstants.get)
    , ("boundedGeneration", failBoundedGeneration.get)
    ]
  renderFailureReport rows⟩

end FloatLibTests.Regression.BinaryInterchange.ExecFloatTranscendentals
