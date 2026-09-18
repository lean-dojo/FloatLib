/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat
public import FloatLib.Floats.Formats
public meta import FloatLib.Floats.ExecFloat.Conversion.Proof
public meta import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Runtime
public meta import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Proof
public meta import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Instances
public meta import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances
public meta import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Conversion
public meta import FloatLib.Floats.Formats.Block.Configured.Conversion.Runtime
public meta import FloatLib.Floats.Formats.Block.Configured.Conversion.Proof
public meta import FloatLib.Floats.Formats.Block.Configured.Conversion.Instances
public meta import FloatLib.Floats.Formats.Codebook.Configured.Conversion.Runtime
public meta import FloatLib.Floats.Formats.Codebook.Configured.Conversion.Proof
public meta import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Conversion.Runtime
public meta import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Conversion.Proof
public meta import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Conversion.Instances
public meta import FloatLib.Floats.Formats.FixedPoint.Configured.Conversion.Runtime
public meta import FloatLib.Floats.Formats.FixedPoint.Configured.Conversion.Proof
public meta import FloatLib.Floats.Formats.FixedPoint.Configured.Conversion.Instances
public meta import FloatLib.Floats.Formats.IEEE754.Native
public meta import FloatLib.Floats.Formats.Logarithmic.Configured.Conversion.Runtime
public meta import FloatLib.Floats.Formats.Logarithmic.Configured.Conversion.Proof
public meta import FloatLib.Floats.Formats.OCP.FP8.E4M3FN
public meta import FloatLib.Floats.Formats.OCP.MX.Configured.Conversion.Runtime
public meta import FloatLib.Floats.Formats.OCP.MX.Configured.Conversion.Proof
public meta import FloatLib.Floats.Formats.Posit.Configured.Conversion.Runtime
public meta import FloatLib.Floats.Formats.Posit.Configured.Conversion.Proof
public meta import FloatLib.Floats.Formats.Posit.Configured.Conversion.Instances
public meta import FloatLib.Floats.Formats.Posit.Quire.Configured.Conversion.Runtime
public meta import FloatLib.Floats.Formats.Posit.Quire.Configured.Conversion.Proof

/-!
# Explicit conversion and mixed-arithmetic conformance

These theorem-level and reviewed native regressions protect the intentionally small
interoperability surface:

* values never acquire an implicit cross-format coercion;
* ordinary notation never invents a mixed-format result type;
* `cast` and `convert` decode a source through its exact meaning and quantize once;
* all five mixed operations perform finite exact arithmetic before one named destination
  quantization; and
* destinations that require policy or context receive it explicitly.

The cases below cover every currently installed scalar source decoder and every currently
installed destination class. Source-only families remain source-only: this module does not
fabricate a rounding rule for logarithmic systems, arbitrary codebooks, quires, or E8M0.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.Conversion

open FloatLib.Floats
open FloatLib.Numerics

private abbrev Binary32 :=
  ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

private abbrev Binary64 :=
  ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

private abbrev Posit32 :=
  ExecFloat.Posit (bits := 32)

private abbrev Posit8 :=
  ExecFloat.Posit (bits := 8)

private abbrev Quire8 :=
  ExecFloat.Posit.Quire (bits := 8)

private abbrev OCPFloat8 :=
  ExecFloat Formats.OCP.FP8.E4M3FN

private abbrev ExactCents :=
  ExecFloat.FixedPoint decimalRadix 2

private abbrev Cents8 :=
  ExecFloat.BoundedFixedPoint decimalRadix 2 8

private abbrev Bipolar :=
  ExecFloat.Codebook Formats.Codebook.Catalog.bipolar1

private abbrev Log10 :=
  ExecFloat.Logarithmic decimalRadix

private abbrev MXScale :=
  ExecFloat.OCP.MX.E8M0

private abbrev Block4 :=
  ExecFloat.SharedScale 4

/-! ## No implicit promotion -/

/-!
There is no heterogeneous `+` instance between binary and posit values. A user must name the
destination with `ExecFloat.addAs`.
-/
/--
error: failed to synthesize instance of type class
  HAdd Binary32 Posit32
-/
#guard_msgs (substring := true) in
#check fun (left : Binary32) (right : Posit32) => left + right

/-!
Even an exactly representable widening is explicit. A user must write
`value.cast (target := Binary64)`.
-/
/--
error: Type mismatch
  value
has type
  Binary32
but is expected to have type
  Binary64
-/
#guard_msgs (substring := true) in
#check fun (value : Binary32) => (value : Binary64)

/-! ## Every mixed operation uses one named destination -/

private def mixedLeft : Binary32 := 6
private def mixedRight : Posit32 := 4
private def mixedAddend : OCPFloat8 :=
  Formats.OCP.FP8.E4M3FN.ofNatBits 0x3c

/-- Decode a successful binary64 destination without hiding conversion failure. -/
private def binary64Rat? (outcome : ExecFloat.ConversionOutcome Binary64) : Option Rat :=
  outcome.value?.bind ExecFloat.Binary.toRat?

/--
Addition, subtraction, multiplication, division, and FMA may use different source families, but
all five compute in exact rational arithmetic and round once into binary64.
-/
example :
    [ binary64Rat? (ExecFloat.addAs (result := Binary64) mixedLeft mixedRight)
    , binary64Rat? (ExecFloat.subAs (result := Binary64) mixedLeft mixedRight)
    , binary64Rat? (ExecFloat.mulAs (result := Binary64) mixedLeft mixedRight)
    , binary64Rat? (ExecFloat.divAs (result := Binary64) mixedLeft mixedRight)
    , binary64Rat?
        (ExecFloat.fmaAs (result := Binary64) mixedLeft mixedRight mixedAddend)
    ] =
      [ some 10, some 2, some 24, some (3 / 2), some (51 / 2) ] := by
  native_decide

/-- Checked exact division rejects both representations of signed-rational zero. -/
example :
    [ ExecFloat.ExactExpression.div (SignedRat.ofRat 1) (0 : SignedRat)
    , ExecFloat.ExactExpression.div (SignedRat.ofRat 1) SignedRat.negZero
    ] =
      [ .error .divisionByZero, .error .divisionByZero ] := by
  decide

/-! ## Every installed scalar source decoder reaches the common rational domain -/

private def exactCents : ExactCents :=
  ExecFloat.FixedPoint.ofCoefficient 125

private def boundedCents : Cents8 :=
  ExecFloat.BoundedFixedPoint.ofCoefficient 125

private def bipolarNegative : Bipolar :=
  ExecFloat.Codebook.ofNatBits 0

private def logarithmicHundred : Log10 :=
  ExecFloat.Logarithmic.ofSignExponent false 2

private def scaleEight : MXScale :=
  ExecFloat.OCP.MX.E8M0.ofExponentSaturating 3

private def quireThreeHalves : Quire8 :=
  ExecFloat.Posit.Quire.pToQ (1.5 : Posit8)

private def nativeThreeHalves32 : Float32 :=
  Float32.ofBits 0x3fc00000

private def nativeThreeHalves64 : Float :=
  Float.ofBits 0x3ff8000000000000

/--
The homogeneous result list keeps the test compact while exercising binary, posit, nominal FP8,
exact and bounded fixed point, codebook, logarithmic, E8M0, quire, and both Lean native sources.
Each source is interpreted by its own decoder; no source is first converted through a host float.
-/
example :
    [ binary64Rat? ((1.5 : Binary32).cast (target := Binary64))
    , binary64Rat? ((2.25 : Posit32).cast (target := Binary64))
    , binary64Rat?
        ((Formats.OCP.FP8.E4M3FN.ofNatBits 0x3c : OCPFloat8).cast
          (target := Binary64))
    , binary64Rat? (exactCents.cast (target := Binary64))
    , binary64Rat? (boundedCents.cast (target := Binary64))
    , binary64Rat? (bipolarNegative.cast (target := Binary64))
    , binary64Rat? (logarithmicHundred.cast (target := Binary64))
    , binary64Rat? (scaleEight.cast (target := Binary64))
    , binary64Rat? (ExecFloat.convert (target := Binary64) quireThreeHalves)
    , binary64Rat? (ExecFloat.convert (target := Binary64) nativeThreeHalves32)
    , binary64Rat? (ExecFloat.convert (target := Binary64) nativeThreeHalves64)
    ] =
      [ some (3 / 2), some (9 / 4), some (3 / 2), some (5 / 4)
      , some (5 / 4), some (-1), some 100, some 8, some (3 / 2)
      , some (3 / 2), some (3 / 2)
      ] := by
  native_decide

/-! ## Every installed destination class keeps its policy visible -/

/-- Posit destinations use the standard posit rounder and preserve exact ordinary values. -/
example :
    (ExecFloat.addAs (result := Posit32) (1.5 : Binary32) (2.25 : Binary64)).value?.bind
        ExecFloat.Posit.toRat? =
      some (15 / 4) := by
  native_decide

/-- Nominal FP8 destinations use the same explicit API and expose their exact meaning. -/
example :
    ((1.5 : Binary32).cast (target := OCPFloat8)).value?.map
        Formats.BinaryInterchange.StaticByte.Conversion.decode =
      some (.finite (3 / 2)) := by
  native_decide

/-- Unbounded fixed point installs an honest default because coefficient overflow is impossible. -/
example :
    ((1.25 : Binary32).cast (target := ExactCents)).value?.map
        ExecFloat.FixedPoint.toRat =
      some (5 / 4) := by
  native_decide

/-- Bounded fixed point defaults to checked conversion rather than hiding wrap or saturation. -/
example :
    ((1.25 : Binary32).cast (target := Cents8)).value?.map
        ExecFloat.BoundedFixedPoint.coefficient =
      some 125 := by
  native_decide

/-- Saturation is available only through an explicit bounded-destination context. -/
example :
    let outcome :=
      ExecFloat.addAsWith (result := Cents8)
        ExecFloat.BoundedFixedPoint.Conversion.OverflowPolicy.saturate
        (1 : Binary32) (1 : Posit32)
    outcome.value?.map ExecFloat.BoundedFixedPoint.coefficient = some 127 ∧
      outcome.status?.map (·.overflow) = some true ∧
      outcome.status?.map (·.saturated) = some true := by
  native_decide

private def blockInput : Vector Rat 4 :=
  ⟨#[1, 3 / 2, -2, 3 / 8], by decide⟩

private def fineBlock : Block4 :=
  ExecFloat.SharedScale.quantizeAt (-2) blockInput

/--
Shared-scale destinations have no context-free default. Their explicit context is the common
exponent selected by the caller.
-/
example :
    (fineBlock.castWith (target := Block4) (-1 : Int)).value?.map
        ExecFloat.SharedScale.exponent =
      some (-1) := by
  native_decide

/-! ## Failure behavior remains representation-independent -/

private def positiveInfinity : Binary32 :=
  ExecFloat.Binary.infinity false

/-- Mixed arithmetic rejects a non-finite input before destination quantization. -/
example :
    (ExecFloat.addAs (result := Binary64) positiveInfinity (1 : Posit32)).failure? =
      some (.infinity .left false) := by
  native_decide

/-- Default conversion maps IEEE infinity to `NaR`, as required by Posit Standard (2022), §6.5. -/
example :
    positiveInfinity.cast (target := Posit32) =
      .success ExecFloat.Posit.nar { mappedSpecial := true } := by
  native_decide

/-! ## Binary conversion overflow and descriptor boundaries -/

open Formats.BinaryInterchange

-- Half an ulp above binary32's largest finite value.
private def binary32OverflowMidpoint : Rat := 2 ^ 128 - 2 ^ 103

/-- Retain the configured conversion's bits and every status flag. -/
private def binary32Conversion (rounding : RoundingMode) (exact : Rat)
    (entropy : Nat := 0) : ExecFloat.ConversionOutcome Nat :=
  (ExecFloat.convertWith (target := Binary32) exact
    ({ quantization := { rounding }, entropy } : ExecFloat.Binary.Conversion.Context)).map
      ExecFloat.Binary.toNatBits

-- Exceeding maxFinite does not itself signal overflow. The midpoint rounds to infinity.
example :
    [ binary32Conversion .nearestEven (binary32OverflowMidpoint - 1)
    , binary32Conversion .nearestEven binary32OverflowMidpoint
    , binary32Conversion .nearestEven (binary32OverflowMidpoint + 1)
    , binary32Conversion .nearestEven (-(binary32OverflowMidpoint - 1))
    , binary32Conversion .nearestEven (-binary32OverflowMidpoint)
    ] =
      [ .success 0x7f7fffff { inexact := true }
      , .success 0x7f800000 { inexact := true, overflow := true }
      , .success 0x7f800000 { inexact := true, overflow := true }
      , .success 0xff7fffff { inexact := true }
      , .success 0xff800000 { inexact := true, overflow := true }
      ] := by
  decide +kernel

-- Directed overflow depends on the sign and direction. Truncation overflows at 2^128,
-- even though its delivered value remains maxFinite.
example :
    [ binary32Conversion .towardZero (binary32OverflowMidpoint - 1)
    , binary32Conversion .towardZero (2 ^ 128 - 1)
    , binary32Conversion .towardZero (2 ^ 128)
    , binary32Conversion .towardPositive (binary32OverflowMidpoint - 1)
    , binary32Conversion .towardPositive (-(binary32OverflowMidpoint - 1))
    , binary32Conversion .towardNegative (binary32OverflowMidpoint - 1)
    , binary32Conversion .towardNegative (-(binary32OverflowMidpoint - 1))
    ] =
      [ .success 0x7f7fffff { inexact := true }
      , .success 0x7f7fffff { inexact := true }
      , .success 0x7f7fffff { inexact := true, overflow := true }
      , .success 0x7f800000 { inexact := true, overflow := true }
      , .success 0xff7fffff { inexact := true }
      , .success 0x7f7fffff { inexact := true }
      , .success 0xff800000 { inexact := true, overflow := true }
      ] := by
  decide +kernel

-- The policies without an IEEE rounding-mode constructor also classify overflow after rounding.
-- These entropy values select opposite sides of the same stochastic rounding interval.
example :
    [ binary32Conversion .nearestAway (binary32OverflowMidpoint - 1)
    , binary32Conversion .nearestAway binary32OverflowMidpoint
    , binary32Conversion .stochastic (binary32OverflowMidpoint - 1) 0
    , binary32Conversion .stochastic (binary32OverflowMidpoint - 1) (2 ^ 103)
    ] =
      [ .success 0x7f7fffff { inexact := true }
      , .success 0x7f800000 { inexact := true, overflow := true }
      , .success 0x7f800000 { inexact := true, overflow := true }
      , .success 0x7f7fffff { inexact := true }
      ] := by
  decide +kernel

/-- Retain a model cast's destination bits and all five exception indicators. -/
private def binary32Cast (format : FloatFormat) (bits : Nat)
    (rounding : Model.IEEERoundingMode := .nearestEven) : Nat × Model.IEEEStatus :=
  let outcome := Model.castWithStatus FloatFormat.binary32 format (Model.ofNatBits bits) rounding
  (outcome.value.toNatBits, outcome.status)

-- Infinity follows the destination's native overflow behavior in every rounding mode.
example :
    [.nearestEven, .towardZero, .towardPositiveInfinity, .towardNegativeInfinity].map
      (fun mode =>
        [ binary32Cast FloatFormat.e4m3fn 0x7f800000 mode
        , binary32Cast FloatFormat.e4m3fn 0xff800000 mode
        , binary32Cast FloatFormat.e4m3fnuz 0x7f800000 mode
        , binary32Cast FloatFormat.e4m3fnuz 0xff800000 mode
        ]) =
      List.replicate 4
        [ (0x7f, { overflow := true, inexact := true })
        , (0x7f, { overflow := true, inexact := true })
        , (0x80, { overflow := true, inexact := true })
        , (0x80, { overflow := true, inexact := true })
        ] := by
  decide +kernel

-- Finite overflow, here from binary32's representations of ±10^10, selects the same NaNs.
example :
    [ binary32Cast FloatFormat.e4m3fn 0x501502f9
    , binary32Cast FloatFormat.e4m3fn 0xd01502f9
    , binary32Cast FloatFormat.e4m3fnuz 0x501502f9
    , binary32Cast FloatFormat.e4m3fnuz 0xd01502f9
    ] =
      [ (0x7f, { overflow := true, inexact := true })
      , (0x7f, { overflow := true, inexact := true })
      , (0x80, { overflow := true, inexact := true })
      , (0x80, { overflow := true, inexact := true })
      ] := by
  decide +kernel

-- IEEE infinity remains exact; a fully finite encoding selects its signed endpoint.
example :
    [ binary32Cast FloatFormat.binary16 0x7f800000
    , binary32Cast FloatFormat.binary16 0xff800000
    , binary32Cast (FloatFormat.custom 4 3 7 .finite) 0x7f800000
    , binary32Cast (FloatFormat.custom 4 3 7 .finite) 0xff800000
    ] =
      [ (0x7c00, {})
      , (0xfc00, {})
      , (0x7f, { overflow := true, inexact := true })
      , (0xff, { overflow := true, inexact := true })
      ] := by
  decide +kernel

private def customBias : FloatFormat := FloatFormat.custom 8 23 100 .ieee

example : customBias.isIEEE = false := by decide

-- The general rational rounder uses the declared bias, including signed and scaled inputs.
example :
    [ Model.toRat? (Model.roundRatScaled customBias false 1 3 0)
    , Model.toRat? (Model.roundRatScaled customBias true 1 3 0)
    , Model.toRat? (Model.roundRatScaled customBias false 1 3 5)
    ] =
      [ some (11184811 / 33554432)
      , some (-11184811 / 33554432)
      , some (11184811 / 1048576)
      ] := by
  decide +kernel

-- The specialized helper cannot bypass its conventional-IEEE precondition.
/--
error: Type mismatch
  Model.ieeeRoundRatScaled customBias false 1 3 0
has type
  customBias.isIEEE = true → Model customBias
but is expected to have type
  Model customBias
-/
#guard_msgs (substring := true) in
#check (Model.ieeeRoundRatScaled customBias false 1 3 0 : Model customBias)

end FloatLibTests.Conformance.Formats.Conversion
