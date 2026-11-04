/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Info
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Sterbenz
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.PrecisionProof
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Spec
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Conversion
public meta import FloatLib.Floats.Formats.BinaryInterchange.Format.Runtime
public meta import FloatLib.Floats.Formats.BinaryInterchange.Format.Storage
public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Proof.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Status
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Contract

/-!
# Inspection profiles for binary-interchange formats

This module assembles what `#float_info` reports about a binary-interchange format: its
representation, exceptional values, rounding rules and theorem groups. `Info.Command` resolves
the carrier, its storage plan, and its installed operations. Complex and interval profiles also
use `inspectSummary` and `standardName` to read their component descriptor.

Which theorems a report lists depends on the carrier. A configured, static-byte, or descriptor
value gets the theorems stated about its own type first, chosen by its installed operations, and
then the theorems about the proof model `Model format`, reached through the carrier's embedding.
The proof model itself gets the model theorems with no embedding in between. Each theorem group
states its scope, and applicability tells destination-only IEEE contracts apart from contracts
requiring IEEE encodings on both sides of a cast.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange

namespace FloatInfo

open Lean Meta
open FloatLib.Floats.ExecFloat

/-- Closed descriptor data extracted by the `#float_info` elaborator. -/
meta structure Summary where
  /-- Number of stored exponent bits. -/
  expWidth : Nat
  /-- Number of stored fraction bits. -/
  fracWidth : Nat
  /-- Bias subtracted from a stored normal exponent. -/
  exponentBias : Nat
  /-- Exceptional-value encoding policy. -/
  encoding : FloatFormat.Encoding
  /-- Total encoded width, including the sign bit. -/
  bitWidth : Nat
  /-- Smallest unbiased exponent of a normal value. -/
  minNormalExponent : Int
  /-- Largest unbiased exponent of a finite normal value. -/
  maxNormalExponent : Int
  /-- Whether the descriptor uses the conventional IEEE bias and exceptional-value encoding. -/
  isIEEE : Bool

/-- Read the exceptional-value policy of a closed binary descriptor. -/
private meta def readEncoding (format : Expr) : MetaM FloatFormat.Encoding := do
  let value ← Inspection.reduceProjection ``FloatFormat.encoding format
  if value.isConstOf ``FloatFormat.Encoding.ieee then
    return .ieee
  if value.isConstOf ``FloatFormat.Encoding.finiteMaxNaN then
    return .finiteMaxNaN
  if value.isConstOf ``FloatFormat.Encoding.finiteUnsignedZero then
    return .finiteUnsignedZero
  if value.isConstOf ``FloatFormat.Encoding.finite then
    return .finite
  throwError "failed to inspect the binary exceptional-value encoding"

/-- Read the descriptor fields used by scalar, complex, and interval reports. -/
meta def inspectSummary (format : Expr) : MetaM Summary := do
  let expWidth ←
    Inspection.readNatProjection "binary descriptor" ``FloatFormat.expWidth format
  let fracWidth ←
    Inspection.readNatProjection "binary descriptor" ``FloatFormat.fracWidth format
  let exponentBias ←
    Inspection.readNatProjection "binary descriptor" ``FloatFormat.exponentBias format
  let encoding ← readEncoding format
  let maxFiniteExponent := encoding.maxFiniteExponent expWidth
  pure
    { expWidth
      fracWidth
      exponentBias
      encoding
      bitWidth := ←
        Inspection.readNatProjection "binary descriptor" ``FloatFormat.bitWidth format
      minNormalExponent := 1 - Int.ofNat exponentBias
      maxNormalExponent := Int.ofNat maxFiniteExponent - Int.ofNat exponentBias
      isIEEE := ←
        Inspection.readFlagProjection "binary descriptor"
          ``FloatFormat.isIEEE ``Bool.true ``Bool.false format }

/-- Human-readable name of a binary exceptional-value policy. -/
meta def encodingName : FloatFormat.Encoding → String
  | .ieee => "IEEE exceptional encodings"
  | .finiteMaxNaN => "finite values with maximum-fraction NaN"
  | .finiteUnsignedZero => "finite values with unsigned zero (FNUZ)"
  | .finite => "finite-only"

/--
The width `k` of an IEEE 754-2019 binary interchange format with this layout, if there is one.

Table 3.5 of the standard defines binaryk for `k` of 16, 32, and 64, with 5, 8, and 11 exponent
bits, and for every multiple of 32 from 128, with `round(4 log2 k) - 13` exponent bits. The
descriptor must also use the IEEE encoding and bias. As `k ^ 8` is never an odd power of two,
`4 log2 k` is never halfway between integers, and its rounding is `(log2 (k ^ 8) + 1) / 2`.
-/
meta def interchangeWidth? (summary : Summary) : Option Nat :=
  let k := summary.bitWidth
  let exponentBits? :=
    match k with
    | 16 => some 5
    | 32 => some 8
    | 64 => some 11
    | _ => if 128 ≤ k && k % 32 == 0 then some ((Nat.log2 (k ^ 8) + 1) / 2 - 13) else none
  if summary.isIEEE && exponentBits? == some summary.expWidth then some k else none

/--
Name the standards a binary layout follows. A layout is named only when its exponent and fraction
widths, encoding, and bias all match, never from its total width alone.
-/
meta def standardName (summary : Summary) : String :=
  match interchangeWidth? summary with
  | some k => s!"IEEE 754-2019 binary{k}"
  | none =>
      if summary.isIEEE then
        if summary.expWidth == 8 && summary.fracWidth == 7 then
          "bfloat16, the brain floating-point format; not an IEEE 754 interchange format"
        else
          "IEEE-style layout; not an IEEE 754 interchange format"
      else
        "binary layout with format-specific encoding or bias"

/--
The configured type with this descriptor, written with the arguments that differ from
`ExecFloat.Binary`'s defaults.
-/
meta def configuredSpelling (summary : Summary) : String :=
  let encoding :=
    match summary.encoding with
    | .ieee => ""
    | .finiteMaxNaN => " (encoding := .finiteMaxNaN)"
    | .finiteUnsignedZero => " (encoding := .finiteUnsignedZero)"
    | .finite => " (encoding := .finite)"
  let bias :=
    if summary.exponentBias == summary.encoding.defaultBias summary.expWidth then ""
    else s!" (bias := {summary.exponentBias})"
  s!"ExecFloat.Binary (exponentBits := {summary.expWidth}) " ++
    s!"(fractionBits := {summary.fracWidth}){encoding}{bias}"

/-- The carriers that the binary-interchange report distinguishes. -/
meta inductive Carrier where
  /-- A configured value `ExecFloat (Configured.Family format code plan)`, such as `Binary32`. -/
  | configured
  /-- A nominal static-byte value, such as `E4M3FN`, stored in one byte. -/
  | staticByte
  /-- A value `ExecFloat (Descriptor format)`, which stores its proof model. -/
  | descriptor
  /-- The proof model `Model format` itself. -/
  | model

/-- Precise NaN population and metadata retained by an encoding policy. -/
meta def nanDescription (encoding : FloatFormat.Encoding) : String :=
  match encoding with
  | .ieee =>
      "yes; sign, signaling/quiet class, and complete fraction payload are decoded"
  | .finiteMaxNaN =>
      "yes; one maximum-fraction quiet NaN per sign"
  | .finiteUnsignedZero =>
      "yes; the negative-zero bit pattern is the sole quiet NaN"
  | .finite =>
      "no"

/--
Whether the encoding has a signaling NaN. IEEE signaling NaNs require a nonzero fraction
with a clear quiet bit, so at least one fraction bit must lie below the quiet bit.
-/
meta def signalingNaNDescription (encoding : FloatFormat.Encoding) (fracWidth : Nat) : String :=
  match encoding with
  | .ieee =>
      if fracWidth > 1 then "yes"
      else "no; no payload bit is available below the quiet bit"
  | .finiteMaxNaN | .finiteUnsignedZero =>
      "no; every NaN in this encoding is quiet"
  | .finite => "no; the encoding has no NaN"

/-- Descriptor-level applicability of theorem families specialized to conventional IEEE layouts. -/
meta def ieeeApplicability
    (summary : Summary) : FloatLib.Floats.ExecFloat.TheoremApplicability :=
  if summary.isIEEE then
    .verifiedForType
  else
    .unavailable
      "the theorem requires `format.isIEEE = true`, but this descriptor reduces it to `false`"

/--
Applicability of a cross-format IEEE theorem when the inspected descriptor may occupy either side.
-/
meta def ieeeCrossFormatApplicability
    (summary : Summary) : FloatLib.Floats.ExecFloat.TheoremApplicability :=
  if summary.isIEEE then
    .conditional "the other source or destination descriptor must also satisfy `isIEEE = true`"
  else
    .unavailable
      "the theorem requires both source and destination descriptors to satisfy `isIEEE = true`"

/-- Applicability of the all-words-finite range-limited enclosure theorems. -/
meta def finiteOnlyApplicability
    (summary : Summary) : FloatLib.Floats.ExecFloat.TheoremApplicability :=
  if summary.encoding == .finite then
    .verifiedForType
  else
    .unavailable
      "the theorem requires `format.encoding = .finite`; NaN-reserving finite encodings have a different boundary"

/-- Applicability of integral rounding when every neighboring integer fits the format range. -/
meta def integralApplicability (summary : Summary) : TheoremApplicability :=
  if !summary.isIEEE then
    ieeeApplicability summary
  else if Int.ofNat summary.fracWidth ≤ summary.maxNormalExponent then
    .verifiedForType
  else
    .unavailable
      "the theorem requires `fracWidth ≤ maxNormalExponent`; this descriptor fails that range premise"

/--
Six significant decimal digits of the positive dyadic `significand * 2 ^ exponent`, as `3.40282e38`,
computed with exact arithmetic and rounded half up. It is `none` for zero or an exponent of
magnitude beyond a million, whose expansion would be slow.
-/
meta def sixDigits (significand : Nat) (exponent : Int) : Option String :=
  if significand = 0 || exponent.natAbs > 1000000 then none
  else
    let num := if 0 ≤ exponent then significand <<< exponent.toNat else significand
    let den := if 0 ≤ exponent then 1 else 1 <<< exponent.natAbs
    -- The digit counts give the decimal exponent of `num / den` up to one.
    let estimate : Int := ((toString num).length : Int) - (toString den).length
    let below :=
      if 0 ≤ estimate then num < den * 10 ^ estimate.toNat else num * 10 ^ estimate.natAbs < den
    let power := if below then estimate - 1 else estimate
    let shift := 5 - power
    let scaledNum := if 0 ≤ shift then num * 10 ^ shift.toNat else num
    let scaledDen := if 0 ≤ shift then den else den * 10 ^ shift.natAbs
    let digits := (2 * scaledNum + scaledDen) / (2 * scaledDen)
    let (digits, power) := if digits ≥ 1000000 then (digits / 10, power + 1) else (digits, power)
    let text := toString digits
    some s!"{text.take 1}.{text.drop 1}e{power}"

/-- An exact text with the six-digit decimal approximation of a dyadic, when one is cheap. -/
meta def withApproximation (exact : String) (significand : Nat) (exponent : Int) : String :=
  match sixDigits significand exponent with
  | some approximation => s!"{exact} ≈ {approximation}"
  | none => exact

/-- A power of two `2 ^ exponent` with its decimal approximation. -/
meta def twoPower (exponent : Int) : String :=
  withApproximation s!"2^{exponent}" 1 exponent

/--
The largest finite value, `(2 - 2 ^ -k) * 2 ^ maxNormalExponent`, where `k` is the fraction width,
or `k - 1` when the all-ones fraction at the top exponent is a NaN.
-/
meta def largestFinite (summary : Summary) : String :=
  let gap := if summary.encoding == .finiteMaxNaN then summary.fracWidth - 1 else summary.fracWidth
  withApproximation s!"(2 - 2^-{gap}) * 2^{summary.maxNormalExponent}"
    (2 ^ (gap + 1) - 1) (summary.maxNormalExponent - gap)

/-- The theorem groups about the proof model `Model format`, the binary descriptor's own values. -/
meta def modelSurfaces (summary : Summary) : List TheoremSurface :=
  [ { topic := "meaning of every bit pattern"
      declarations := []
      definitions := [``Model.exactValue, ``Model.AtExact, ``Model.AtValue]
      applicability := .verifiedForType
      scope :=
        "all bit patterns; finite dyadics plus signed-zero, infinity, and NaN metadata when represented by the encoding" }
  , { topic := "arithmetic equals its reference operation"
      declarations :=
        [ ``Model.Proof.add_eq_spec
        , ``Model.Proof.sub_eq_spec
        , ``Model.Proof.mul_eq_spec
        , ``Model.Proof.div_eq_spec
        , ``Model.Proof.sqrt_eq_spec
        , ``Model.Proof.fma_eq_spec
        ]
      applicability := .verifiedForType
      scope :=
        "all encoded operands for every valid descriptor; each automatically dispatched proof-model operation equals its descriptor-aware specification" }
  , { topic := "a finite result is one nearest-even rounding of the exact result"
      declarations :=
        [ ``Model.toReal_add_eq_roundAt
        , ``Model.toReal_roundRatScaled_eq_roundAt
        , ``Model.toReal_sub_eq_roundAt
        , ``Model.toReal_mul_eq_roundAt
        , ``Model.toReal_div_eq_roundAt
        , ``Model.toReal_sqrt_eq_roundAt
        , ``Model.isFinite_sqrt_of_isFinite
        , ``Model.toReal_fma_eq_roundAt
        ]
      applicability := ieeeApplicability summary
      scope :=
        "the finiteness, sign, nonzero, domain, and result-range hypotheses in each theorem"
      numericalGuarantee? := some {
        kinds := [.rounding]
        statement :=
          "Each listed finite primitive equals one nearest-even rounding of its exact real operation." } }
  , { topic := "exception flags and ternary values"
      declarations :=
        [ ``Model.value_add
        , ``Model.value_sub
        , ``Model.value_mul
        , ``Model.value_div
        , ``Model.value_sqrt
        , ``Model.value_fma
        , ``Model.add_status_of_toDyadic
        , ``Model.mul_status_of_toDyadic
        , ``Model.div_status_of_toDyadic_nonzero
        , ``Model.fma_status_of_toDyadic
        , ``Model.sqrt_status_of_toDyadic
        , ``Model.add_invalid
        , ``Model.mul_invalid
        , ``Model.div_invalid
        , ``Model.add_invalid_of_isIEEE
        , ``Model.mul_invalid_of_isIEEE
        , ``Model.fma_invalid_of_isIEEE
        , ``Model.div_invalid_of_isIEEE
        , ``Model.div_divideByZero
        , ``Model.sqrt_invalid
        , ``Model.sqrt_inexact_iff
        , ``Model.sqrt_inexact_eq_ternary_bne_eq
        , ``Model.sqrt_inexact_of_underflow
        , ``Model.fma_invalid
        , ``Model.dyadicRoundingStatus_inexact_of_underflow
        , ``Model.dyadicRoundingStatus_inexact_of_overflow
        , ``Model.rationalRoundingStatusScaled_inexact_of_underflow
        , ``Model.rationalRoundingStatusScaled_inexact_of_overflow
        ]
      definitions :=
        [ ``Numerics.IEEEStatus
        , ``Model.OutcomeAt
        , ``Model.add
        , ``Model.sub
        , ``Model.mul
        , ``Model.div
        , ``Model.sqrt
        , ``Model.fma
        ]
      applicability := .verifiedForType
      scope :=
        "all binary descriptors; value preservation, finite rounding classification, invalid operations, divide-by-zero, and the overflow/underflow/inexact invariants stated by the listed theorems" }
  , { topic := "classification, comparison, neighbors, and the other operations"
      declarations :=
        [ ``Model.compare_eq_some_lt_iff_toEReal_lt
        , ``Model.compare_eq_some_eq_iff_toEReal_eq
        , ``Model.compare_eq_some_gt_iff_toEReal_gt
        , ``Model.toEReal_minimum_eq_min
        , ``Model.toEReal_maximum_eq_max
        , ``Model.toEReal_minNum_eq_min
        , ``Model.toEReal_maxNum_eq_max
        , ``Model.toEReal_minimumNumber_eq_min
        , ``Model.toEReal_maximumNumber_eq_max
        , ``Model.minimumNumber_of_isNaN_left
        , ``Model.maximumNumber_of_isNaN_left
        , ``Model.minimumNumber_invalid
        , ``Model.maximumNumber_invalid
        , ``Model.minimum_invalid
        , ``Model.maximum_invalid
        , ``Model.nextUp_invalid
        , ``Model.nextDown_invalid
        , ``Model.adjacencyRank_nextUp
        , ``Model.adjacencyRank_nextDown
        , ``Model.no_rank_between_nextUp
        , ``Model.no_rank_between_nextDown
        , ``Model.adjacencyRank_lt_adjacencyRank_iff
        , ``Model.no_value_between_nextUp
        , ``Model.no_value_between_nextDown
        , ``Model.remainderDyadic_toRat
        , ``Model.remainder_status_of_finite
        , ``Model.remainder_status_of_zero_divisor
        , ``Model.roundToIntegral_status_of_finite
        , ``Model.roundToIntegral_inexact_iff
        , ``Model.scale_status_of_finite
        , ``Model.binaryExponent_status_of_finite_nonzero
        , ``Model.binaryExponentInt_of_finite_nonzero
        , ``Model.binaryExponentInt_bounds
        , ``Model.binaryExponentInt_of_zero
        , ``Model.binaryExponentInt_of_infinity
        , ``Model.binaryExponentInt_of_nan
        ]
      definitions :=
        [ ``Model.signBit
        , ``Model.isZero
        , ``Model.isFinite
        , ``Model.isSubnormal
        , ``Model.isInf
        , ``Model.isNaN
        , ``Model.isSNaN
        , ``Model.isQNaN
        , ``Model.neg
        , ``Model.abs
        , ``Model.copySign
        , ``Model.compare
        , ``Model.minimum
        , ``Model.maximum
        , ``Model.minNum
        , ``Model.maxNum
        , ``Model.minimumNumber
        , ``Model.maximumNumber
        , ``Model.nextUp
        , ``Model.nextDown
        , ``Model.remainder
        , ``Model.roundToIntegral
        , ``Model.scale
        , ``Model.binaryExponent
        , ``Model.binaryExponentInt
        ]
      applicability := .verifiedForType
      scope :=
        "all binary descriptors under the non-NaN, finite, nonzero, and endpoint hypotheses stated by each theorem; the declaration list is validated when the inspection profile is constructed" }
  , { topic := "IEEE exact remainder and integral truncation"
      declarations :=
        [ ``Model.remainder_exact
        , ``Model.isFinite_roundToIntegral_towardZero
        , ``Model.toReal_roundToIntegral_towardZero
        , ``Model.roundToIntegral_towardZero_overflow_eq_false
        ]
      applicability := ieeeApplicability summary
      scope := "IEEE-style descriptor; finite inputs and a nonzero remainder divisor as stated by each theorem" }
  , { topic := "IEEE rounding to representable integers"
      declarations :=
        [ ``Model.roundToIntegral_overflow_eq_false
        , ``Model.isFinite_roundToIntegral
        , ``Model.toReal_roundToIntegral_down
        , ``Model.toReal_roundToIntegral_up
        , ``Model.toReal_roundToIntegral_nearest
        , ``Model.toReal_roundToIntegral_nearestAway
        , ``Model.toReal_roundToIntegral_away
        ]
      applicability := integralApplicability summary
      scope := "IEEE-style descriptor with fracWidth ≤ maxNormalExponent; finite inputs as stated by each theorem" }
  , { topic := "IEEE directed rounding and interval enclosures"
      declarations :=
        [ ``Model.toEReal_add_down_le
        , ``Model.le_toEReal_add_up
        , ``Model.toEReal_sub_down_le
        , ``Model.le_toEReal_sub_up
        , ``Model.toEReal_mul_down_le
        , ``Model.le_toEReal_mul_up
        , ``Model.toEReal_div_down_le
        , ``Model.le_toEReal_div_up
        , ``Model.toEReal_sqrt_down_le
        , ``Model.le_toEReal_sqrt_up
        , ``Model.Interval.add_sound
        , ``Model.Interval.sub_sound
        , ``Model.Interval.mul_sound
        , ``Model.Interval.div_sound
        , ``Model.Interval.sqrt_sound
        ]
      applicability := ieeeApplicability summary
      scope :=
        "the finite-input, interval-validity, and operation-domain hypotheses stated by each theorem"
      numericalGuarantee? := some {
        kinds := [.range]
        statement :=
          "Directed endpoints and interval operations enclose the exact real result." } }
  , { topic := "finite-only range-limited directed rounding and dyadic interval arithmetic"
      declarations :=
        [ ``Model.toReal_roundDyadicDown_le_of_encoding_finite
        , ``Model.le_toReal_roundDyadicUp_of_encoding_finite
        , ``Model.toReal_add_down_le_of_encoding_finite
        , ``Model.le_toReal_add_up_of_encoding_finite
        , ``Model.toReal_sub_down_le_of_encoding_finite
        , ``Model.le_toReal_sub_up_of_encoding_finite
        , ``Model.toReal_mul_down_le_of_encoding_finite
        , ``Model.le_toReal_mul_up_of_encoding_finite
        , ``Model.Interval.add_sound_of_encoding_finite
        , ``Model.Interval.sub_sound_of_encoding_finite
        , ``Model.Interval.mul_sound_of_encoding_finite
        ]
      applicability := finiteOnlyApplicability summary
      scope :=
        "all-words-finite encoding only; exact add/sub endpoint expressions and all four multiplication corners must lie within the largest-finite magnitude"
      numericalGuarantee? := some {
        kinds := [.range]
        statement :=
          "Range-limited directed endpoints enclose exact dyadic add, subtract, and multiply results." } }
  , { topic := "generic rounding-grid error bounds"
      declarations :=
        [ ``Model.abs_roundAt_sub_le
        , ``Model.roundAt_mem_Icc
        , ``Model.relativeError_roundAt_le_of_normal
        ]
      applicability := .verifiedForType
      scope :=
        "roundAt uses this descriptor's precision and bias with no upper exponent bound. " ++
        "Executable operations require a separate refinement theorem; relative error requires " ++
        "nonzero normal-range input."
      numericalGuarantee? := some {
        kinds := [.range, .rounding, .absoluteError, .relativeError]
        statement :=
          "The real-valued roundAt grid has absolute error at most 1/2 ULP; " ++
          "for nonzero normal-range inputs, relative error is at most " ++
          s!"2^-{summary.fracWidth + 1}."
      } }
  , { topic := "exact compatible widening"
      declarations := [``Model.cast_exact_of_compatibleWidening]
      applicability := .verifiedForType
      scope :=
        "source and destination have equal exponent width, bias, and encoding, while destination precision is at least the source precision"
      numericalGuarantee? := some {
        kinds := [.exactness]
        statement :=
          "A compatible widening preserves the represented finite value with zero rounding error." } }
  , { topic := "mixed-precision sequential reduction and matrix entry bounds"
      declarations :=
        [ ``Model.mulAccError_eq_site_residuals
        , ``Model.mulAcc_abs_error_le_budget
        , ``Model.sequentialAccumulator_error_eq_sum
        , ``Model.dotSequential_abs_error_le_budget
        , ``Model.matmul_refines
        , ``Model.matmul_entry_abs_error_le_budget
        ]
      definitions := [``Model.SitePolicy, ``Model.MatmulRefines]
      applicability := ieeeCrossFormatApplicability summary
      scope :=
        "arbitrary storage, product, accumulator, and output descriptors under the IEEE, finiteness, length, shape, and per-site premises stated by each theorem"
      numericalGuarantee? := some {
        kinds := [.absoluteError]
        statement :=
          "Sequential dot products and matrix entries are bounded by the sum of their checked per-site rounding residual budgets." } }
  , { topic := "requested-precision decimal and hexadecimal output"
      declarations :=
        [ ``Model.significantDecimal_nearest_error
        , ``Model.significantHex_nearest_error
        , ``Model.le_significantDecimal_up
        , ``Model.significantDecimal_down_le
        , ``Model.significantDecimal_towardZero_abs_le
        , ``Model.le_significantHex_up
        , ``Model.significantHex_down_le
        , ``Model.significantHex_towardZero_abs_le
        ]
      applicability := .verifiedForType
      scope :=
        "every exact finite input and positive requested significant-digit count; " ++
        "directed bounds concern the emitted value, not a subsequent binary input rounding"
      numericalGuarantee? := some {
        kinds := [.absoluteError, .rounding]
        statement :=
          "Nearest-even output stays within half an external grid unit. Directed output " ++
          "stays on its requested side, and toward-zero output cannot increase magnitude." } }
  , { topic := "half-ulp error and exact operations, Sterbenz subtraction included"
      declarations :=
        [ ``Model.abs_toReal_add_sub_le
        , ``Model.abs_toReal_sub_sub_le
        , ``Model.abs_toReal_mul_sub_le
        , ``Model.abs_toReal_div_sub_le
        , ``Model.abs_toReal_sqrt_sub_le
        , ``Model.abs_toReal_fma_sub_le
        , ``Model.toReal_sub_eq_of_sterbenz
        , ``Model.toReal_sub_eq_of_sterbenz_of_same_sign
        , ``Model.toReal_add_of_isZero_left
        , ``Model.toReal_add_of_isZero_right
        , ``Model.toReal_sub_of_isZero_left
        , ``Model.toReal_sub_of_isZero_right
        , ``Model.toReal_sub_self
        , ``Model.toReal_mul_of_isZero_left
        , ``Model.toReal_mul_of_isZero_right
        , ``Model.toReal_mul_of_abs_toReal_eq_one_left
        , ``Model.toReal_mul_of_abs_toReal_eq_one_right
        , ``Model.toReal_div_of_abs_toReal_eq_one_right
        ]
      applicability := ieeeApplicability summary
      scope :=
        "the finiteness, result-range, positivity, normality, and factor-of-two hypotheses stated by each theorem"
      numericalGuarantee? := some {
        kinds := [.absoluteError, .exactness]
        statement :=
          "Each finite primitive has at most 1/2 ULP absolute error; Sterbenz subtraction is " ++
          "exact in its proved factor-of-two domain, and so are sums and differences with a " ++
          "zero, x - x, products with a zero or with a value of magnitude one, and quotients " ++
          "by a value of magnitude one." } }
  , { topic := "mixed relative and absolute error"
      declarations :=
        [ ``Model.mixedError_roundAt
        , ``Model.mixedError_toReal_add
        , ``Model.mixedError_toReal_add_of_mul_nonneg
        , ``Model.mixedError_toReal_sub
        , ``Model.mixedError_toReal_sub_of_mul_nonpos
        , ``Model.mixedError_toReal_mul
        , ``Model.mixedError_toReal_div
        , ``Model.mixedError_toReal_fma
        , ``Model.mixedError_toReal_sqrt
        , ``Model.mixedError_toReal_cast
        , ``Model.mixedError_toReal_foldl_add
        , ``Model.mixedError_toReal_foldl_add_weighted
        , ``Model.mixedError_toReal_foldl_add_absolute
        , ``Model.toRat?_foldl_add_eq_single
        ]
      definitions := [``Numerics.MixedError]
      applicability := ieeeApplicability summary
      scope :=
        "finite results and the operand errors, signs, and partial-sum finiteness stated by " ++
        "each theorem; a cast needs only an IEEE destination"
      numericalGuarantee? := some {
        kinds := [.relativeError, .absoluteError, .exactness]
        statement :=
          "|x - x0| <= r * |x0| + a is carried through each finite operation, which adds one " ++
          s!"rounding with relative error u = 2^-{summary.fracWidth + 1} and, except for " ++
          "addition and subtraction, absolute error half the least subnormal. A " ++
          "left-to-right sum of n terms whose seed and terms have nonnegative exact values, " ++
          "relative error r and absolute errors d and e_i has relative error " ++
          "(1 + u)^n * (1 + r) - 1 and absolute error (1 + u)^n * (d + sum e_i), so exact " ++
          "inputs give (1 + u)^n - 1. A one-hot sum over distinct indices is exact." } }
  , { topic := "casts to IEEE destinations"
      declarations :=
        [ ``Model.cast_eq_roundAt
        , ``Model.cast_exact_of_gridExtension
        , ``Model.abs_toReal_cast_sub_le
        ]
      applicability := .conditional
        "the destination must satisfy `isIEEE = true`; the source may use any descriptor"
      scope :=
        "finite result, which forces a finite source; grid exactness also requires destination grid inclusion"
      numericalGuarantee? := some {
        kinds := [.rounding, .absoluteError, .exactness]
        statement :=
          "Casting performs one destination rounding with at most 1/2 destination ULP error, " ++
          "including finite-only and custom-bias sources; a finer destination grid preserves " ++
          "the source real value." } }
  , { topic := "IEEE rational conversion enclosures"
      declarations :=
        [ ``Model.toEReal_ofRat_down_le
        , ``Model.le_toEReal_ofRat_up
        ]
      applicability := ieeeApplicability summary
      scope := "all normalized rationals, including zero and overflow to infinity"
      numericalGuarantee? := some {
        kinds := [.rounding]
        statement :=
          "Directed conversion encloses the exact rational between extended-real bounds." } }
  , { topic := "IEEE destination reduction semantics"
      declarations :=
        [ ``Model.Reduction.sum_status_value_toReal_eq_roundAt_of_finite
        , ``Model.Reduction.dot_status_value_toReal_eq_roundAt_of_finite
        ]
      applicability := ieeeApplicability summary
      scope := "finite operands and result; dot products additionally require equal input lengths"
      numericalGuarantee? := some {
        kinds := [.rounding]
        statement :=
          "Exact accumulation is followed by one nearest-even destination rounding, " ++
          "including empty inputs and cancellation to zero." } }
  , { topic := "transcendental enclosures and whole-algorithm proof contracts"
      declarations :=
        [ ``Model.Transcendentals.Contract.RealEnclosure.abs_sub_le_width
        , ``Model.Transcendentals.Contract.StableEnclosure.roundAt_eq_roundAt_lower
        , ``Model.Transcendentals.Contract.CertifiedRoundedResult.toReal_value_eq_roundAt
        ]
      definitions :=
        [ ``Model.Transcendentals.Contract.RealEnclosure
        , ``Model.Transcendentals.Contract.RealEnclosure.exp
        , ``Model.Transcendentals.Contract.RealEnclosure.log
        , ``Model.Transcendentals.Contract.RealEnclosure.sqrt
        , ``Model.Transcendentals.Contract.RealEnclosure.sin
        , ``Model.Transcendentals.Contract.RealEnclosure.cos
        , ``Model.Transcendentals.Contract.RealEnclosure.sinh
        , ``Model.Transcendentals.Contract.RealEnclosure.cosh
        , ``Model.Transcendentals.Contract.RealEnclosure.tanh
        , ``Model.Transcendentals.Contract.ApproximationCertificate
        , ``Model.Transcendentals.Contract.CorrectlyRoundedCertificate
        ]
      applicability := .conditional
        "a whole-algorithm certificate for the selected executable kernel; the built-in approximations supply none"
      scope :=
        "generic finite-real proof interfaces, not certificates for this type's executable kernels; numerical accuracy or correct rounding requires an inhabited certificate connecting the selected kernel to the real function" }
  ]

/-- The theorem groups about configured values, such as `Binary32` values. -/
private meta def configuredSurfaces (summary : Summary) (operations : CoreOperationCoverage) :
    List TheoremSurface :=
  let premises :=
    "a finite result, which forces finite operands and a nonzero divisor; a finite divisor for " ++
    "division and a zero or positive operand for square root; and the capability's `HasSpec` " ++
    "instance, which instance search proves for the capabilities the library declares"
  let groups : List TheoremSurface :=
    [ { topic := "a finite result is one nearest-even rounding of the exact result"
        declarations := operations.installed fun
          | .add => [``FloatLib.Floats.ExecFloat.Binary.toReal_add_eq_roundAt]
          | .sub => [``FloatLib.Floats.ExecFloat.Binary.toReal_sub_eq_roundAt]
          | .mul => [``FloatLib.Floats.ExecFloat.Binary.toReal_mul_eq_roundAt]
          | .div => [``FloatLib.Floats.ExecFloat.Binary.toReal_div_eq_roundAt]
          | .sqrt => [``FloatLib.Floats.ExecFloat.Binary.toReal_sqrt_eq_roundAt]
          | .fma => [``FloatLib.Floats.ExecFloat.Binary.toReal_fma_eq_roundAt]
        definitions := [``FloatLib.Floats.ExecFloat.Binary.toReal, ``Model.roundAt]
        applicability := ieeeApplicability summary
        scope := premises
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Each listed finite operation equals one nearest-even rounding of its exact real " ++
            "result." } }
    , { topic := "half-ulp error"
        declarations := operations.installed fun
          | .add => [``FloatLib.Floats.ExecFloat.Binary.abs_toReal_add_sub_le]
          | .sub => [``FloatLib.Floats.ExecFloat.Binary.abs_toReal_sub_sub_le]
          | .mul => [``FloatLib.Floats.ExecFloat.Binary.abs_toReal_mul_sub_le]
          | .div => [``FloatLib.Floats.ExecFloat.Binary.abs_toReal_div_sub_le]
          | .sqrt => [``FloatLib.Floats.ExecFloat.Binary.abs_toReal_sqrt_sub_le]
          | .fma => [``FloatLib.Floats.ExecFloat.Binary.abs_toReal_fma_sub_le]
        applicability := ieeeApplicability summary
        scope := premises
        numericalGuarantee? := some {
          kinds := [.absoluteError]
          statement := "Each listed finite operation is within half an ulp of its exact real result." } }
    , { topic := "operations that do not round"
        declarations := operations.installed fun
          | .add =>
              [ ``FloatLib.Floats.ExecFloat.Binary.toReal_add_of_isZero_left
              , ``FloatLib.Floats.ExecFloat.Binary.toReal_add_of_isZero_right ]
          | .sub =>
              [ ``FloatLib.Floats.ExecFloat.Binary.toReal_sub_of_isZero_left
              , ``FloatLib.Floats.ExecFloat.Binary.toReal_sub_of_isZero_right
              , ``FloatLib.Floats.ExecFloat.Binary.toReal_sub_self ]
          | .mul =>
              [ ``FloatLib.Floats.ExecFloat.Binary.toReal_mul_of_isZero_left
              , ``FloatLib.Floats.ExecFloat.Binary.toReal_mul_of_isZero_right
              , ``FloatLib.Floats.ExecFloat.Binary.toReal_mul_of_abs_toReal_eq_one_left
              , ``FloatLib.Floats.ExecFloat.Binary.toReal_mul_of_abs_toReal_eq_one_right ]
          | .div => [``FloatLib.Floats.ExecFloat.Binary.toReal_div_of_abs_toReal_eq_one_right]
          | .sqrt => [``FloatLib.Floats.ExecFloat.Binary.toReal_sqrt_of_isZero]
          | .fma => []
        applicability := ieeeApplicability summary
        scope :=
          "finite operands, a zero operand or one of magnitude one as each theorem states, and " ++
          "the capability's `HasSpec` instance"
        numericalGuarantee? := some {
          kinds := [.exactness]
          statement :=
            "Sums and differences with a zero, x - x, products with a zero or with a value of " ++
            "magnitude one, quotients by a value of magnitude one, and the square root of a " ++
            "zero are exact." } }
    , { topic := "decoding to the proof model"
        declarations :=
          [ ``FloatLib.Floats.ExecFloat.Binary.toModel_ofModel
          , ``FloatLib.Floats.ExecFloat.Binary.ofModel_toModel
          , ``FloatLib.Floats.ExecFloat.Binary.toModel_neg ] ++
          operations.installed fun
            | .add =>
                [ ``FloatLib.Floats.ExecFloat.Binary.toModel_hAdd
                , ``FloatLib.Floats.ExecFloat.Binary.toModel_add
                , ``FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.toModel_add ]
            | .sub =>
                [ ``FloatLib.Floats.ExecFloat.Binary.toModel_hSub
                , ``FloatLib.Floats.ExecFloat.Binary.toModel_sub
                , ``FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.toModel_sub ]
            | .mul =>
                [ ``FloatLib.Floats.ExecFloat.Binary.toModel_hMul
                , ``FloatLib.Floats.ExecFloat.Binary.toModel_mul
                , ``FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.toModel_mul ]
            | .div =>
                [ ``FloatLib.Floats.ExecFloat.Binary.toModel_hDiv
                , ``FloatLib.Floats.ExecFloat.Binary.toModel_div
                , ``FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.toModel_div ]
            | .sqrt =>
                [ ``FloatLib.Floats.ExecFloat.Binary.toModel_execFloat_sqrt
                , ``FloatLib.Floats.ExecFloat.Binary.toModel_sqrt
                , ``FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.toModel_sqrt ]
            | .fma =>
                [ ``FloatLib.Floats.ExecFloat.Binary.toModel_fma
                , ``FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.toModel_fma ]
        definitions :=
          [``FloatLib.Floats.ExecFloat.Binary.toModel, ``FloatLib.Floats.ExecFloat.Binary.ofModel]
        applicability := .verifiedForType
        scope :=
          "every value and rounding direction; the `IEEEOutcome` forms cover " ++
          "`(status := true)`, and the operation theorems take the capability's `HasSpec` " ++
          "instance, so the theorems about `Model` values below apply through `toModel`" } ]
  refinementEquations operations ++ groups.filter fun surface => !surface.declarations.isEmpty

/-- The theorem groups about static-byte values, such as `E4M3FN` values. -/
private meta def staticByteSurfaces (operations : CoreOperationCoverage) :
    List TheoremSurface :=
  refinementEquations operations ++
  [ { topic := "decoding to the proof model"
      declarations :=
        [ ``StaticByte.toModel_ofModel
        , ``StaticByte.ofModel_toModel
        , ``StaticByte.toModel_injective ]
      definitions :=
        [ ``StaticByte.toModel, ``StaticByte.ofModel, ``StaticByte.Spec.add, ``StaticByte.Spec.sub
        , ``StaticByte.Spec.mul, ``StaticByte.Spec.div, ``StaticByte.Spec.sqrt
        , ``StaticByte.Spec.fma ]
      applicability := .verifiedForType
      scope :=
        "every value; the reference operation of `x + y` is `StaticByte.Spec.add`, which " ++
        "re-encodes the model sum of `toModel x` and `toModel y`, and likewise for the other " ++
        "operations. No theorem states `x + y` on this type in terms of real rounding; the " ++
        "theorems about `Model` values below state it for the decoded values" } ]

/-- The theorem groups about descriptor-carrier values `ExecFloat (Descriptor format)`. -/
private meta def descriptorSurfaces (operations : CoreOperationCoverage) :
    List TheoremSurface :=
  refinementEquations operations ++
  [ { topic := "the stored proof model"
      declarations := []
      definitions :=
        [ ``FloatLib.Floats.ExecFloat.raw, ``Descriptor.Spec.add, ``Descriptor.Spec.sub
        , ``Descriptor.Spec.mul, ``Descriptor.Spec.div, ``Descriptor.Spec.sqrt
        , ``Descriptor.Spec.fma ]
      applicability := .verifiedForType
      scope :=
        "a value stores its `Model format` word, read with `raw`; the reference operation of " ++
        "`x + y` is `Descriptor.Spec.add`, the model operation lifted through that identity " ++
        "codec, and likewise for the other operations" } ]

/--
Storage of a carrier. A configured carrier's word comes from its storage plan instead.
-/
meta def carrierStorage (summary : Summary) : Carrier → String
  | .configured => "the word its storage plan selects"
  | .staticByte => "UInt8"
  | .descriptor => s!"BitVec {summary.bitWidth} (the proof model itself)"
  | .model => s!"BitVec {summary.bitWidth}"

/-- Rounding of literals and arithmetic, and the options that select other rules, by carrier. -/
private meta def roundingEntries (summary : Summary) : Carrier → List InfoEntry
  | .configured =>
      [ ⟨"numeric literals", "exact integer/rational input rounded once to nearest, ties to even"⟩
      , ⟨"arithmetic",
          "nearest, ties to even, for `x + y`, `x - y`, `x * y`, `x / y`, " ++
            "`ExecFloat.sqrt`, and `ExecFloat.fma`"⟩
      , ⟨"directions and flags",
          "`ExecFloat.Binary.add x y (mode := .up) (status := true)`, likewise sub, mul, " ++
            "div, sqrt, and fma: six rounding directions, including away from zero, and the " ++
            "invalid, divide-by-zero, overflow, underflow, and inexact flags with the " ++
            "ternary value"⟩
      ]
  | .staticByte =>
      [ ⟨"numeric literals", "exact integer/rational input rounded once to nearest, ties to even"⟩
      , ⟨"arithmetic", "nearest, ties to even"⟩
      , ⟨"directions and flags",
          s!"none on this type; {configuredSpelling summary} has the same values, with " ++
            "rounding-direction and status options"⟩
      ]
  | .descriptor =>
      [ ⟨"arithmetic", "nearest, ties to even"⟩
      , ⟨"directions and flags",
          "none on this type; the stored model has them, as in " ++
            "`Model.add x.raw y.raw (mode := .up) (status := true)`"⟩
      ]
  | .model =>
      [ ⟨"numeric literals", "exact integer/rational input rounded once to nearest, ties to even"⟩
      , ⟨"model arithmetic", "nearest, ties to even"⟩
      , ⟨"directions",
          "`(mode := m)` on each operation selects one of six rounding directions, including " ++
            "away from zero"⟩
      , ⟨"status flags",
          "`(status := true)` adds the invalid, divide-by-zero, overflow, underflow, and " ++
            "inexact flags and the ternary value"⟩
      ]

/-- The claims a report does not make, by carrier and layout. -/
private meta def nonclaimsOf (summary : Summary) (carrier : Carrier) : List String :=
  let hostFloat :=
    match summary.expWidth, summary.fracWidth, summary.isIEEE with
    | 8, 23, true => ["equivalence between compiled `Float32` arithmetic and this type; only the explicit conversion boundary is checked"]
    | 11, 52, true => ["equivalence between compiled `Float` arithmetic and this type; only the explicit conversion boundary is checked"]
    | _, _, _ => []
  let realRounding :=
    match carrier with
    | .staticByte | .descriptor =>
        ["a theorem stating this type's arithmetic in terms of real rounding; those theorems are about the decoded `Model` values"]
    | .configured | .model => []
  let display :=
    match carrier with
    | .configured | .model =>
        [ "bitwise NaN round trips through the display `format`; use " ++
            "`format (style := .exact)` or `(style := .hex)` output to retain NaN metadata"
        , "the built-in deterministic transcendental kernels currently carry a whole-algorithm approximation or correctly-rounded certificate" ]
    | .staticByte | .descriptor => []
  hostFloat ++ realRounding ++
    ["every clause of IEEE 754 follows from the six backend-refinement equations"] ++ display ++
    ["external MPFR, Arb, compiler lowering, or FFI behavior is inside this certificate"]

/--
Build the user-facing inspection profile of a binary descriptor seen through `carrier`.

`storage` describes the carrier's storage, and `operations` the universal operations whose
capabilities are installed, which decide the refinement equations the report lists. The default
carrier is the proof model itself, whose report lists the model theorems without an embedding.
-/
meta def profile
    (summary : Summary)
    (standard : String)
    (storage : String)
    (carrier : Carrier := .model)
    (operations : CoreOperationCoverage := .none) :
    FloatLib.Floats.ExecFloat.FormatProfile where
  family := "binary interchange"
  standard
  representation :=
    [ ⟨"storage", storage⟩
    , ⟨"total bits", toString summary.bitWidth⟩
    , ⟨"sign bits", "1"⟩
    , ⟨"exponent bits", toString summary.expWidth⟩
    , ⟨"stored fraction bits", toString summary.fracWidth⟩
    , ⟨"normal significand precision", s!"{summary.fracWidth + 1} bits"⟩
    , ⟨"exponent bias", toString summary.exponentBias⟩
    , ⟨"minimum normal exponent", toString summary.minNormalExponent⟩
    , ⟨"maximum finite normal exponent", toString summary.maxNormalExponent⟩
    , ⟨"encoding", encodingName summary.encoding⟩
    ]
  values :=
    [ ⟨"largest finite value (maxFinite)", largestFinite summary⟩
    , ⟨"least normal value (minNormal)", twoPower summary.minNormalExponent⟩
    , ⟨"least subnormal value (minSubnormal)",
        twoPower (summary.minNormalExponent - summary.fracWidth)⟩
    , ⟨"machine epsilon (epsilon)", twoPower (-(summary.fracWidth : Int))⟩
    , ⟨"finite numbers", "yes"⟩
    , ⟨"subnormals", "yes; exponent field zero with a nonzero fraction"⟩
    , ⟨"distinct signed zeros", yesNo (summary.encoding != .finiteUnsignedZero)⟩
    , ⟨"signed infinities", yesNo (summary.encoding == .ieee)⟩
    , ⟨"NaN", nanDescription summary.encoding⟩
    , ⟨"signaling NaN", signalingNaNDescription summary.encoding summary.fracWidth⟩
    ]
  rounding := roundingEntries summary carrier
  execution :=
    match carrier with
    | .model =>
        [ ⟨"kernels",
            "each `Model` operation dispatches to tiny tables, machine words, or the generic " ++
              "kernel by itself; no planning policy applies"⟩
        , ⟨"purpose", "specifications, conformance vectors, and backend proofs"⟩ ]
    | .configured | .staticByte | .descriptor => []
  theoremSurfaces :=
    match carrier with
    | .configured => configuredSurfaces summary operations
    | .staticByte => staticByteSurfaces operations
    | .descriptor => descriptorSurfaces operations
    | .model => modelSurfaces summary
  relatedTheorems :=
    let model (embedding : Name) : List RelatedTheorems :=
      [{ type := ``Model, embedding, surfaces := modelSurfaces summary }]
    match carrier with
    | .configured => model ``FloatLib.Floats.ExecFloat.Binary.toModel
    | .staticByte => model ``StaticByte.toModel
    | .descriptor => model ``FloatLib.Floats.ExecFloat.raw
    | .model => []
  nonclaims := nonclaimsOf summary carrier

end FloatInfo

end FloatLib.Floats.Formats.BinaryInterchange
