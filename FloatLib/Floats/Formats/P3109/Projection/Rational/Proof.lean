/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Correctness
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Direction

/-!
# Correctness of exact-rational P3109 projection

The imported rational semantics prove the report's exact quantum, floor, parity, and selection
formulas, with direction and error theorems for deterministic modes and selection correctness for
every supplied stochastic word. This file proves that the result always fits the direct encoder's
precision grid, then reuses the same saturation-and-encoding theorem as dyadic projection.

The logarithm bound imported here is a proof theorem about exact natural-number quotients; the
P3109 runtime itself remains independent of binary-interchange representation and policy.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109
namespace Format

/--
Exact-rational precision rounding always lands on the descriptor's direct-encoding grid.

The proof is uniform in width, precision, signedness, domain, rounding mode, and stochastic bit
width. Every mode chooses one of the two adjacent integer candidates at the same exact quantum.
-/
theorem roundFiniteRatToPrecision_fitsPrecisionGrid
    (format : Format) (mode : RoundingMode) (exact : Rat) :
    format.FitsPrecisionGrid
      (format.roundFiniteRatToPrecision mode exact) := by
  unfold FitsPrecisionGrid
  unfold roundFiniteRatToPrecision
  simp only [beq_iff_eq]
  split
  next hzero =>
    simp
  next hzero =>
    let numerator := exact.num.natAbs
    let leadingExponent :=
      Numerics.RationalBinary.floorLog2 numerator exact.den
    let quantumExponent :=
      max leadingExponent format.minimumNormalExponent -
        Int.ofNat format.precision + 1
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        numerator exact.den (-quantumExponent)
    let lower := scaled.1 / scaled.2
    let rounded :=
      if Internal.roundRationalAway format mode (exact.num < 0)
          quantumExponent lower (scaled.1 % scaled.2) scaled.2 then
        lower + 1
      else
        lower
    have hnumerator : numerator ≠ 0 := by
      simpa [numerator] using hzero
    have hlower :
        lower < 2 ^ format.precision := by
      simpa [lower, scaled, quantumExponent, leadingExponent, numerator] using
        RationalRounding.quotientFloor_lt_precision format.precision
          format.minimumNormalExponent numerator exact.den hnumerator exact.den_nz
    have hrounded :
        rounded ≤ 2 ^ format.precision := by
      unfold rounded
      split <;> omega
    have hquantum :
        format.minimumQuantumExponent ≤ quantumExponent := by
      unfold quantumExponent
      exact format.quantumExponent_lower leadingExponent
    change
      (if rounded = 0 then
        Numerics.Dyadic.zero
      else
        {
          negative := exact.num < 0
          significand := rounded
          exponent := quantumExponent
        }).significand = 0 ∨
      (if rounded = 0 then
        Numerics.Dyadic.zero
      else
        {
          negative := exact.num < 0
          significand := rounded
          exponent := quantumExponent
        }).significand ≤ 2 ^ format.precision ∧
      format.minimumQuantumExponent ≤
        (if rounded = 0 then
          Numerics.Dyadic.zero
        else
          {
            negative := exact.num < 0
            significand := rounded
            exponent := quantumExponent
          }).exponent
    by_cases hroundedZero : rounded = 0
    · simp [hroundedZero]
    · simp [hroundedZero, hrounded, hquantum]

/--
Decoding exact-rational projection returns its round-then-saturate datum.

The representation theorem is shared with dyadic projection; only the proof that rational
rounding lands on the precision grid is new.
-/
theorem sameDatum_decode_projectRatCode
    (format : Format) (policy : ProjectionPolicy)
    (value : NumericalValue Rat) :
    SameDatum
      (format.decode (format.projectRatCode policy value))
      (format.projectRatValue policy value) := by
  unfold projectRatCode projectRatValue
  apply format.sameDatum_decode_encodeSaturate
  cases value with
  | finite exact =>
      exact format.roundFiniteRatToPrecision_fitsPrecisionGrid
        policy.rounding exact
  | infinity _ =>
      trivial
  | exceptional _ =>
      trivial

end Format
end FloatLib.Floats.Formats.P3109

namespace FloatLib.Floats.ExecFloat.P3109

variable {format : Formats.P3109.Format}

/-- Decoding `projectRat` exposes the exact P3109 rational round-then-saturate specification. -/
theorem decode_projectRat
    (policy : Formats.P3109.ProjectionPolicy)
    (value : NumericalValue Rat) :
    Formats.P3109.Format.SameDatum
      (decode (projectRat (format := format) policy value))
      (format.projectRatValue policy value) := by
  exact
    Formats.P3109.Format.sameDatum_decode_projectRatCode
      format policy value

end FloatLib.Floats.ExecFloat.P3109
