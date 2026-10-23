/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Runtime
public import Mathlib.Data.Nat.Sqrt

/-!
# P3109 square-root rounding by exact square comparisons

For a nonnegative rational radicand, the floor candidate is `sqrt (numerator / denominator)`
computed in natural numbers. Rounding compares the radicand with the square of an exact rational
threshold. This decides rounding of the square root even when it is irrational.

Stochastic A and B select the upper candidate at their supplied random threshold. Stochastic C
uses the half-integer threshold of its nearest-even integer rounding, including its tie parity.
The caller supplies the random word, as in §4.7.4 of the P3109 4.0.3 working-group report.

Square root, reciprocal square root, and hypotenuse follow §§4.10.8 and 4.10.14 of that unapproved
report. Each evaluates its exact radicand before the one rounding and saturation step.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

/-- Floor of the nonnegative square root of `numerator / denominator`. -/
@[inline] def sqrtFloor (numerator denominator : Nat) : Nat :=
  Nat.sqrt (numerator / denominator)

/--
Compare `sqrt (numerator / denominator)` with `threshold / scale` by squaring.
The denominator and threshold scale are positive at every arithmetic call site.
-/
@[inline] def compareSqrt (numerator denominator scale threshold : Nat) : Ordering :=
  compare (numerator * scale ^ 2) (denominator * threshold ^ 2)

/--
Select the upper candidate from exact threshold comparisons.

For stochastic A and B the threshold is the first fraction whose scaled floor reaches the
required integer. For C it is the midpoint below that integer, with the integer's tie parity.
The comparison argument lets the executable square comparisons and the real semantics share
these policy rules.
-/
def sqrtRoundDecision (format : Format) (mode : RoundingMode)
    (quantum : Int) (lower : Nat) (exact : Bool)
    (compareThreshold : Nat → Nat → Ordering) : Bool :=
  if exact then
    false
  else
    match mode with
    | .towardZero | .down => false
    | .up => true
    | .nearestAway =>
        compareThreshold 2 (2 * lower + 1) != .lt
    | .nearest =>
        let ordering := compareThreshold 2 (2 * lower + 1)
        ordering == .gt ||
          (ordering == .eq && !format.lowerCodeIsEven quantum lower)
    | .toOdd => format.lowerCodeIsEven quantum lower
    | .stochasticA random =>
        let scale := 2 ^ random.width
        let threshold := lower * scale + (scale - random.toNat)
        compareThreshold scale threshold != .lt
    | .stochasticB random =>
        let scale := 2 ^ (random.width + 1)
        let threshold := lower * scale + (scale - (2 * random.toNat + 1))
        compareThreshold scale threshold != .lt
    | .stochasticC random =>
        let unit := 2 ^ random.width
        let boundary := unit - random.toNat
        let scale := 2 * unit
        let threshold := lower * scale + (2 * boundary - 1)
        let ordering := compareThreshold scale threshold
        ordering == .gt || (ordering == .eq && boundary % 2 == 0)

/-- The executable square-root boundary test for one report rounding mode. -/
def sqrtRoundAway (format : Format) (mode : RoundingMode)
    (quantum : Int) (numerator denominator lower : Nat) : Bool :=
  sqrtRoundDecision format mode quantum lower
    (numerator == denominator * lower ^ 2) (compareSqrt numerator denominator)

/-- The report's quantum for the square root of a positive rational. -/
def sqrtQuantum (format : Format) (numerator denominator : Nat) : Int :=
  max (RationalBinary.floorLog2 numerator denominator / 2) format.minimumNormalExponent -
    Int.ofNat format.precision + 1

/--
Round the exact nonnegative square root to the descriptor's precision.

The integer division of the radicand's binary exponent by two is floor division, including
negative exponents. The scaled numerator and denominator represent the square of the significand,
so the scaling exponent is `-2 * quantum`.

Square-root callers establish that the radicand is nonnegative. On an arbitrary rational this
precision helper rounds the square root of its absolute value.
-/
def roundSqrtRatToPrecision (format : Format) (mode : RoundingMode)
    (radicand : Rat) : FloatLib.Numerics.Dyadic :=
  if radicand.num.natAbs == 0 then
    .zero
  else
    let quantum := sqrtQuantum format radicand.num.natAbs radicand.den
    let scaled :=
      RationalBinary.scaleByPowerOfTwo radicand.num.natAbs radicand.den (-2 * quantum)
    let lower := sqrtFloor scaled.1 scaled.2
    let rounded :=
      if sqrtRoundAway format mode quantum scaled.1 scaled.2 lower then lower + 1 else lower
    if rounded == 0 then .zero else ⟨false, rounded, quantum⟩

/-- Square root in the closed domain, with precision rounding before saturation. -/
def sqrtRounded (format : Format) (mode : RoundingMode) :
    NumericalValue Rat → NumericalValue FloatLib.Numerics.Dyadic
  | .exceptional _ => .exceptional (.nan)
  | .infinity true => .exceptional (.nan)
  | .infinity false => .infinity false
  | .finite value =>
      if value < 0 then .exceptional (.nan)
      else .finite (roundSqrtRatToPrecision format mode value)

/-- Apply the report saturation policy after square-root precision rounding. -/
def sqrtValue (format : Format) (policy : ProjectionPolicy) (value : NumericalValue Rat) :
    NumericalValue FloatLib.Numerics.Dyadic :=
  format.saturate policy.saturation policy.rounding (sqrtRounded format policy.rounding value)

/-- Encode the already rounded and saturated square-root datum. -/
def sqrtCode (format : Format) (policy : ProjectionPolicy) (value : NumericalValue Rat) :
    BitVec format.bitWidth :=
  BitVec.ofNat format.bitWidth (Format.Internal.encodeDatumNat format
    (sqrtValue format policy value))

/-- Exact radicand for reciprocal square root, which is NaN at zero as well as below it. -/
def rsqrtRadicand : NumericalValue Rat → NumericalValue Rat
  | .exceptional _ | .infinity true => nan
  | .infinity false => .finite 0
  | .finite value => if value ≤ 0 then nan else .finite (1 / value)

/-- Exact sum of squares for hypotenuse, where a NaN operand takes precedence over infinity. -/
def hypotRadicand : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | .infinity _, _ | _, .infinity _ => .infinity false
  | .finite left, .finite right => .finite (left * left + right * right)

end FloatLib.Floats.Formats.P3109.Arithmetic

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format : Format}

/-- Project the exact square root of a closed rational datum, rounding before saturation. -/
@[inline] def projectSqrt {format : Format} (value : NumericalValue Rat)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 format :=
  ExecFloat.Codebook.ofCode (Arithmetic.sqrtCode format { rounding := mode, saturation } value)

/--
Square root of the exact operand, projected once into `target`, by default the operand's format.
Negative inputs give NaN.
-/
@[inline] def sqrt (value : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectSqrt value.toClosedRat mode saturation

/-- Reciprocal square root with one final projection. Zero and negative inputs give NaN. -/
@[inline] def rsqrt (value : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectSqrt (Arithmetic.rsqrtRadicand value.toClosedRat) mode saturation

/-- Hypotenuse from the exact sum of squares, with no intermediate overflow or rounding. -/
@[inline] def hypot (left right : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectSqrt (Arithmetic.hypotRadicand left.toClosedRat right.toClosedRat) mode saturation

end FloatLib.Floats.ExecFloat.P3109
