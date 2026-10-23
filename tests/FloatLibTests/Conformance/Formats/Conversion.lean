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
public meta import FloatLib.Floats.Formats.BinaryInterchange.Configured.Parsing
public meta import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.BoundedParsing
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
-- The `DecidableEq (Except ε α)` instance body is needed by `decide` below.
import all Batteries.Data.Except

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

The cases below cover every installed scalar source decoder and every installed destination
class. Source-only families stay source-only, so this module invents no rounding rule for
logarithmic systems, arbitrary codebooks, quires, or E8M0.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.Conversion

open FloatLib.Floats
open FloatLib.Numerics

private abbrev OCPFloat8 :=
  E4M3FN

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
  E4M3FN.ofNatBits 0x3c

/-- Decode a successful binary64 destination without hiding conversion failure. -/
private def binary64Rat? (outcome : ExecFloat.ConversionOutcome Binary64) : Option Rat :=
  outcome.value?.bind ExecFloat.Binary.toRat?

/--
Addition, subtraction, multiplication, division, and FMA may use different source families, but
all five compute in exact rational arithmetic and round once into binary64.
-/
example :
    [ binary64Rat? (ExecFloat.addAs (target := Binary64) mixedLeft mixedRight)
    , binary64Rat? (ExecFloat.subAs (target := Binary64) mixedLeft mixedRight)
    , binary64Rat? (ExecFloat.mulAs (target := Binary64) mixedLeft mixedRight)
    , binary64Rat? (ExecFloat.divAs (target := Binary64) mixedLeft mixedRight)
    , binary64Rat?
        (ExecFloat.fmaAs (target := Binary64) mixedLeft mixedRight mixedAddend)
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

/-- The standard posit and quire names select the matching widths. -/
example :
    Posit8 = ExecFloat.Posit 8 ∧ Posit64 = ExecFloat.Posit 64 ∧
      Quire8 = ExecFloat.Posit.Quire 8 ∧ Quire64 = ExecFloat.Posit.Quire 64 :=
  ⟨rfl, rfl, rfl, rfl⟩

private def quireThreeHalves : Quire8 :=
  ExecFloat.Posit.Quire.pToQ (1.5 : Posit8)

private def nativeThreeHalves32 : Float32 :=
  Float32.ofBits 0x3fc00000

private def nativeThreeHalves64 : Float :=
  Float.ofBits 0x3ff8000000000000

/--
The homogeneous result list keeps the test compact while exercising binary, posit, nominal FP8,
exact and bounded fixed point, codebook, logarithmic, E8M0, quire, and both Lean native sources.
Each source is interpreted by its own decoder, and no source passes through a host float first.
-/
example :
    [ binary64Rat? ((1.5 : Binary32).cast (target := Binary64))
    , binary64Rat? ((2.25 : Posit32).cast (target := Binary64))
    , binary64Rat?
        ((E4M3FN.ofNatBits 0x3c : OCPFloat8).cast
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
    (ExecFloat.addAs (target := Posit32) (1.5 : Binary32) (2.25 : Binary64)).value?.bind
        ExecFloat.Posit.toRat? =
      some (15 / 4) := by
  native_decide

/-- Nominal FP8 destinations use the same conversion API and expose their exact meaning. -/
example :
    ((1.5 : Binary32).cast (target := OCPFloat8)).value?.map
        Formats.BinaryInterchange.StaticByte.Conversion.decode =
      some (.finite (3 / 2)) := by
  native_decide

/-- Unbounded fixed point has a context-free default because coefficient overflow is impossible. -/
example :
    ((1.25 : Binary32).cast (target := ExactCents)).value?.map
        ExecFloat.FixedPoint.toRat =
      some (5 / 4) := by
  native_decide

/-- Bounded fixed point defaults to checked conversion, so it never wraps or saturates silently. -/
example :
    ((1.25 : Binary32).cast (target := Cents8)).value?.map
        ExecFloat.BoundedFixedPoint.coefficient =
      some 125 := by
  native_decide

/-- Saturation is available only through an explicit bounded-destination context. -/
example :
    let outcome :=
      ExecFloat.addAs (target := Cents8) (1 : Binary32) (1 : Posit32)
        (context := ExecFloat.BoundedFixedPoint.OverflowPolicy.saturate)
    outcome.value?.map ExecFloat.BoundedFixedPoint.coefficient = some 127 ∧
      outcome.status?.map (·.overflow) = some true ∧
      outcome.status?.map (·.saturated) = some true := by
  native_decide

private def blockInput : Vector Rat 4 :=
  ⟨#[1, 3 / 2, -2, 3 / 8], by decide⟩

private def fineBlock : Block4 :=
  ExecFloat.SharedScale.quantizeAt (-2) blockInput

/--
Shared-scale destinations have no context-free default. Their context is the common exponent
that the caller selects.
-/
example :
    (fineBlock.cast (target := Block4) (context := (-1 : Int))).value?.map
        ExecFloat.SharedScale.exponent =
      some (-1) := by
  native_decide

/-! ## Failure behavior remains representation-independent -/

private def positiveInfinity : Binary32 :=
  ExecFloat.Binary.infinity false

/-- Mixed arithmetic rejects a non-finite input before destination quantization. -/
example :
    (ExecFloat.addAs (target := Binary64) positiveInfinity (1 : Posit32)).failure? =
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
  (ExecFloat.convert (target := Binary32) exact (context :=
    ({ quantization := { rounding }, entropy } : ExecFloat.Binary.Conversion.Context))).map
      ExecFloat.Binary.toNatBits

private structure DiagnosticNaN where
  payload : Nat
  signaling : Bool

private instance : ExecFloat.ExactDecoder DiagnosticNaN SignedRat where
  decode value := .exceptional (.nan (some value.payload) false value.signaling)

/-- Custom decoders supply diagnostic payloads independently of the source NaN's signaling bit. -/
example :
    [ (ExecFloat.convert (target := Binary32) (DiagnosticNaN.mk 5 false)).map
        ExecFloat.Binary.toNatBits
    , (ExecFloat.convert (target := Binary32) (DiagnosticNaN.mk 5 true)).map
        ExecFloat.Binary.toNatBits
    ] =
      [ .success 0x7fc00005 {}, .success 0x7fc00005 { invalid := true } ] := by
  decide +kernel

-- A NaN cast keeps its sign and payload and is quieted, IEEE 754-2019 §6.2.3. A signaling
-- source raises invalid (§7.2). A payload too wide for the destination becomes zero.
example :
    [ ((ExecFloat.Binary.ofNatBits 0xffc00005 : Binary32).cast (target := Binary32)).map
        ExecFloat.Binary.toNatBits
    , ((ExecFloat.Binary.ofNatBits 0xff800005 : Binary32).cast (target := Binary32)).map
        ExecFloat.Binary.toNatBits
    , ((ExecFloat.Binary.ofNatBits 0x7f800001 : Binary32).cast (target := Binary64)).map
        ExecFloat.Binary.toNatBits
    ] =
      [ .success 0xffc00005 {}
      , .success 0xffc00005 { invalid := true }
      , .success 0x7ff8000000000001 { invalid := true }
      ] := by
  decide +kernel

example :
    [ ((ExecFloat.Binary.ofNatBits 0xfff8000000000000 : Binary64).cast (target := Binary16)).map
        ExecFloat.Binary.toNatBits
    , ((ExecFloat.Binary.ofNatBits 0x7ff8000000000201 : Binary64).cast (target := Binary16)).map
        ExecFloat.Binary.toNatBits
    , ((ExecFloat.Binary.ofNatBits 0x7ff8000000000001 : Binary64).cast (target := Binary16)).map
        ExecFloat.Binary.toNatBits
    ] =
      [ .success 0xfe00 {}
      , .success 0x7e00 {}
      , .success 0x7e01 {}
      ] := by
  decide +kernel

-- Posit NaR has no sign or payload, but a signaling source still raises invalid.
example :
    [ (ExecFloat.Binary.ofNatBits 0x7f800001 : Binary32).cast (target := Posit32)
    , (ExecFloat.Binary.ofNatBits 0x7fc00001 : Binary32).cast (target := Posit32)
    ] =
      [ .success ExecFloat.Posit.nar { mappedSpecial := true, invalid := true }
      , .success ExecFloat.Posit.nar { mappedSpecial := true }
      ] := by
  decide +kernel

-- Exceeding maxFinite does not itself signal overflow. The midpoint rounds to infinity.
example :
    [ binary32Conversion .nearest (binary32OverflowMidpoint - 1)
    , binary32Conversion .nearest binary32OverflowMidpoint
    , binary32Conversion .nearest (binary32OverflowMidpoint + 1)
    , binary32Conversion .nearest (-(binary32OverflowMidpoint - 1))
    , binary32Conversion .nearest (-binary32OverflowMidpoint)
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
    , binary32Conversion .up (binary32OverflowMidpoint - 1)
    , binary32Conversion .up (-(binary32OverflowMidpoint - 1))
    , binary32Conversion .down (binary32OverflowMidpoint - 1)
    , binary32Conversion .down (-(binary32OverflowMidpoint - 1))
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

-- Rounding away from zero overflows to infinity of either sign above maxFinite. It takes a value
-- less than half an ulp above one to the next float, where nearest-even keeps one, and a value
-- far below the least subnormal up to that subnormal. A value that rounds up to the smallest
-- normal 2^-126 is tiny only up to and including 2^-126 - 2^-150, below the nearest-rounding
-- boundary 2^-126 - 2^-151, so nearest-even reports underflow where away from zero does not.
example :
    [ binary32Conversion .away (binary32OverflowMidpoint - 1)
    , binary32Conversion .away (-(binary32OverflowMidpoint - 1))
    , binary32Conversion .away (1 + 1 / (3 * 2 ^ 24))
    , binary32Conversion .nearest (1 + 1 / (3 * 2 ^ 24))
    , binary32Conversion .away (1 / 2 ^ 160)
    , binary32Conversion .away (1 / 2 ^ 126 - 1 / 2 ^ 150)
    , binary32Conversion .away (1 / 2 ^ 126 - 3 / 2 ^ 152)
    , binary32Conversion .nearest (1 / 2 ^ 126 - 3 / 2 ^ 152)
    ] =
      [ .success 0x7f800000 { inexact := true, overflow := true }
      , .success 0xff800000 { inexact := true, overflow := true }
      , .success 0x3f800001 { inexact := true }
      , .success 0x3f800000 { inexact := true }
      , .success 0x00000001 { inexact := true, underflow := true }
      , .success 0x00800000 { inexact := true, underflow := true }
      , .success 0x00800000 { inexact := true }
      , .success 0x00800000 { inexact := true, underflow := true }
      ] := by
  decide +kernel

-- Nearest-away overflow is classified through its `IEEERoundingMode` direction. Stochastic
-- rounding, the only policy rounding without such a direction, also classifies overflow after
-- rounding. These entropy values select opposite sides of the same stochastic rounding interval.
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
    (mode : Model.IEEERoundingMode := .nearest) : Nat × IEEEStatus :=
  let outcome :=
    Model.cast FloatFormat.binary32 format (Model.ofNatBits bits) mode (status := true)
  (outcome.value.toNatBits, outcome.status)

-- Infinity follows the destination's native overflow behavior in every rounding mode.
example :
    Model.IEEERoundingMode.all.map
      (fun mode =>
        [ binary32Cast FloatFormat.e4m3fn 0x7f800000 mode
        , binary32Cast FloatFormat.e4m3fn 0xff800000 mode
        , binary32Cast FloatFormat.e4m3fnuz 0x7f800000 mode
        , binary32Cast FloatFormat.e4m3fnuz 0xff800000 mode
        ]) =
      List.replicate 6
        [ (0x7f, { overflow := true, inexact := true })
        , (0xff, { overflow := true, inexact := true })
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
      , (0xff, { overflow := true, inexact := true })
      , (0x80, { overflow := true, inexact := true })
      , (0x80, { overflow := true, inexact := true })
      ] := by
  decide +kernel

-- IEEE infinity stays exact, and a fully finite encoding selects its signed endpoint.
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

private abbrev FiniteE4M3 :=
  ExecFloat.Binary (exponentBits := 4) (fractionBits := 3) (encoding := .finite)

-- A fully finite destination has no NaN. `ExecFloat` conversion fails with the source NaN, and the
-- model cast delivers positive zero with invalid raised, in every rounding mode.
example :
    [ ExecFloat.cast (target := FiniteE4M3) (ExecFloat.Binary.ofNatBits 0x7fc00000 : Binary32)
    , ExecFloat.cast (target := FiniteE4M3) (ExecFloat.Binary.ofNatBits 0xff800001 : Binary32)
    ] =
      [ .failure (.exceptional .source (.nan (some 0) false false))
      , .failure (.exceptional .source (.nan (some 1) true true))
      ] := by
  decide +kernel

example :
    [ binary32Cast (FloatFormat.custom 4 3 7 .finite) 0x7fc00000
    , binary32Cast (FloatFormat.custom 4 3 7 .finite) 0xff800001 .towardZero
    ] =
      [ (0x00, { invalid := true })
      , (0x00, { invalid := true })
      ] := by
  decide +kernel

-- The same agreement holds for every NaN source and every configured fully finite destination.
example {format : FloatFormat} {plan : Configured.StoragePlan format}
    {code : Type} [ExecFloat.ModelCodec plan (Model format) code]
    (value : Binary32) (mode : Model.IEEERoundingMode)
    (hnan : Model.isNaN (ExecFloat.Binary.toModel value) = true)
    (hformat : format.encoding = .finite) :
    (ExecFloat.Binary.Conversion.run (format := format) (plan := plan) (code := code)
        .default (ExecFloat.Binary.decode value)).value? = none ∧
      (Model.cast _ format
        (ExecFloat.Binary.toModel value) mode (status := true)).status.invalid = true := by
  obtain ⟨hrun, hinvalid⟩ :=
    ExecFloat.Binary.Conversion.run_default_decode_of_isNaN_of_encoding_finite
      (format := format) (plan := plan) (code := code) value mode hnan hformat
  exact ⟨by rw [hrun]; rfl, hinvalid⟩

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

/-! ## Rounding direction and context options -/

/-- A cast with `mode` delivers the bits of the model cast with the same direction. -/
private def directedCastAgrees (bits : Nat) (mode : Model.IEEERoundingMode) : Bool :=
  let x : Binary64 := ExecFloat.Binary.ofNatBits bits
  let expected : Binary32 :=
    ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x) (mode := mode))
  (x.cast (target := Binary32) (mode := mode)).value?.map ExecFloat.Binary.toNatBits ==
    some (ExecFloat.Binary.toNatBits expected)

/-- Directed casts agree with `Model.cast` on ties, overflow, underflow, and signed zero. -/
example :
    [ 0x3fb999999999999a, 0xbfb999999999999a, 0x3fd5555555555555, 0x3ff0000010000000
    , 0xbff0000010000000, 0x7fefffffffffffff, 0xffefffffffffffff, 1, 0x8000000000000001
    , 0, 0x8000000000000000, 0x3ff0000000000000, 0x7ff0000000000000, 0xfff0000000000000
    ].all (fun bits => Model.IEEERoundingMode.all.all (directedCastAgrees bits)) = true := by
  decide +kernel

/-- A nearest-even `mode` is the default context, and a directed `mode` changes the result. -/
example :
    let tenth : Binary64 := 0.1
    [ (tenth.cast (target := Binary32) (mode := .nearest)).map ExecFloat.Binary.toNatBits
    , (tenth.cast (target := Binary32)).map ExecFloat.Binary.toNatBits
    , (tenth.cast (target := Binary32) (mode := .down)).map ExecFloat.Binary.toNatBits
    , (ExecFloat.convert (target := Binary32) (1 / 3 : Rat) (mode := .down)).map
        ExecFloat.Binary.toNatBits
    , (ExecFloat.convert (target := Binary32) (1 / 3 : Rat) (mode := .up)).map
        ExecFloat.Binary.toNatBits
    ] =
      [ .success 0x3dcccccd { inexact := true }, .success 0x3dcccccd { inexact := true }
      , .success 0x3dcccccc { inexact := true }, .success 0x3eaaaaaa { inexact := true }
      , .success 0x3eaaaaab { inexact := true } ] := by
  decide +kernel

/-- Nominal FP8 destinations take the same directions. -/
example :
    [ ((0.3 : Binary32).cast (target := OCPFloat8) (mode := .down)).value?.map
        Formats.BinaryInterchange.StaticByte.Conversion.decode
    , ((0.3 : Binary32).cast (target := OCPFloat8) (mode := .up)).value?.map
        Formats.BinaryInterchange.StaticByte.Conversion.decode
    ] =
      [ some (.finite (9 / 32)), some (.finite (5 / 16)) ] := by
  decide +kernel

/--
Mixed operations take the same option. An exactly cancelling sum or difference rounded downward
is negative zero, and the quotient `1 / 3` rounds to either neighbour.
-/
example :
    [ (ExecFloat.addAs (target := Binary32) (1 : Binary32) (-1 : Posit32)).map
        ExecFloat.Binary.toNatBits
    , (ExecFloat.addAs (target := Binary32) (1 : Binary32) (-1 : Posit32) (mode := .down)).map
        ExecFloat.Binary.toNatBits
    , (ExecFloat.subAs (target := Binary32) (1 : Binary32) (1 : Posit32) (mode := .down)).map
        ExecFloat.Binary.toNatBits
    , (ExecFloat.fmaAs (target := Binary32) (1 : Binary32) (1 : Posit32) (-1 : Binary64)
        (mode := .down)).map ExecFloat.Binary.toNatBits
    , (ExecFloat.divAs (target := Binary32) (1 : Binary32) (3 : Posit32) (mode := .down)).map
        ExecFloat.Binary.toNatBits
    , (ExecFloat.divAs (target := Binary32) (1 : Binary32) (3 : Posit32) (mode := .up)).map
        ExecFloat.Binary.toNatBits
    , (ExecFloat.mulAs (target := Binary32) (1 / 3 : Rat) (1 : Posit32) (mode := .up)).map
        ExecFloat.Binary.toNatBits
    ] =
      [ .success 0 {}, .success 0x80000000 {}, .success 0x80000000 {}
      , .success 0x80000000 {}, .success 0x3eaaaaaa { inexact := true }
      , .success 0x3eaaaaab { inexact := true }, .success 0x3eaaaaab { inexact := true } ] := by
  decide +kernel

/-- A directed `ExactExpression.add` keeps the cancellation sign that `roundOnce` then rounds. -/
private def downwardCancellation : ExecFloat.ConversionOutcome Binary32 :=
  ExecFloat.roundOnce (mode := .down) do
    let a ← ExecFloat.ExactExpression.operand 0 (1 : Binary32)
    let b ← ExecFloat.ExactExpression.operand 1 (-1 : Binary32)
    ExecFloat.ExactExpression.add (target := Binary32) a b (mode := .down)

/-- Ordinary `SignedRat` addition keeps the nearest-even positive zero. -/
private def nearestCancellation : ExecFloat.ConversionOutcome Binary32 :=
  ExecFloat.roundOnce (mode := .down) do
    let a ← ExecFloat.ExactExpression.operand 0 (1 : Binary32)
    let b ← ExecFloat.ExactExpression.operand 1 (-1 : Binary32)
    pure (a + b)

example :
    [ downwardCancellation.map ExecFloat.Binary.toNatBits
    , nearestCancellation.map ExecFloat.Binary.toNatBits
    , (ExecFloat.roundOnce (target := Binary32) (mode := .up) do
        let a ← ExecFloat.ExactExpression.operand 0 (1 : Binary32)
        let b ← ExecFloat.ExactExpression.operand 1 (3 : Binary32)
        ExecFloat.ExactExpression.div a b).map ExecFloat.Binary.toNatBits
    ] =
      [ .success 0x80000000 {}, .success 0 {}, .success 0x3eaaaaab { inexact := true } ] := by
  decide +kernel

/-!
A family without directed conversion rejects a direction when the call is elaborated, and a
destination without a canonical context requires an explicit one.
-/
/--
error: failed to synthesize instance of type class
  ExecFloat.RoundingModes Posit32 IEEERoundingMode
-/
#guard_msgs (substring := true) in
open FloatLib.Rounding in
#check fun (value : Binary32) => value.cast (target := Posit32) (mode := up)

/--
error: failed to synthesize instance of type class
  ExecFloat.ModeContext Block4
-/
#guard_msgs (substring := true) in
#check fineBlock.cast (target := Block4)

/-! ## Parse limits -/

/--
Setting one parse limit takes effect while the other keeps its default, in the descriptor model
and the configured parser.
-/
example :
    [ (Model.parse FloatFormat.binary64 "1.0" (limits := some { maxBytes := 2 })).toOption.isSome
    , (Model.parse FloatFormat.binary64 "1e3" (limits := some { maxExponent := 2 })).toOption.isSome
    , (Model.parse FloatFormat.binary64 "1e3" (limits := some { maxBytes := 2 })).toOption.isSome
    , (Model.parse FloatFormat.binary64 "1e3" (limits := some {})).toOption.isSome
    , ((ExecFloat.Binary.parse "1.0" (limits := some { maxBytes := 2 }) :
        Except Model.ParseError Binary32).toOption.isSome)
    , ((ExecFloat.Binary.parse "1.0" (limits := some { maxBytes := 3 }) :
        Except Model.ParseError Binary32).toOption.isSome)
    ] =
      [ false, false, false, true, false, true ] := by
  decide +kernel

/-- The limit errors name the measured quantity and the bound it exceeded. -/
example :
    [ match Model.parse FloatFormat.binary64 "1.0" (limits := some { maxBytes := 2 }) with
      | .error error => decide (error = .inputTooLong 3 2)
      | .ok _ => false
    , match Model.parse FloatFormat.binary64 "1e3" (limits := some { maxExponent := 2 })
          (status := true) with
      | .error error => decide (error = .exponentTooLarge 3 2)
      | .ok _ => false
    ] =
      [ true, true ] := by
  decide +kernel

end FloatLibTests.Conformance.Formats.Conversion
