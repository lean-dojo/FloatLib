/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Conversion
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.RoundedReal
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Sign
public import FloatLib.Numerics.ErrorBound

/-!
# Rational values of binary floats

This file is what lets an error analysis treat stored values as exact data and literal constants
as one rounding. A finite value decodes to an exact rational, and its total real observation is
that rational. An exceptional value decodes as `0` in both.

For an IEEE descriptor, a finite conversion of a rational is its rounding to nearest, with the
error bound of one rounding, and a rational of magnitude at most the largest finite value converts
to a finite value. A rational that the format represents, as the decoding of its conversion shows,
converts with no error. Two smaller facts round it out: a certified rational enclosure of a real
reference bounds the error of a finite candidate, and clearing the sign of a finite value is exact.
-/

public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

/-- Exact rational decoding agrees with the total real observation. Exceptional values decode
as zero here, so numerical API entry points must establish finiteness on their own. -/
theorem cast_toRat_eq_toReal {format : FloatFormat} (input : Model format) :
    (((toRat? input).getD 0 : Rat) : ℝ) = toReal input := by
  cases decoded : toDyadic? input with
  | none => simp [toRat?, toReal_eq, decoded]
  | some dyadic =>
      simp [toRat?, toReal_eq, decoded, Dyadic.cast_toRat]

/-- The scaled form that rational rounding receives denotes the rational itself. -/
private theorem signedScaledRatToReal_rat (value : Rat) :
    signedScaledRatToReal (decide (value.num < 0)) value.num.natAbs value.den 0 =
      (value : ℝ) := by
  rw [Rat.cast_def]
  by_cases h : value.num < 0
  · simp [signedScaledRatToReal, scaledRatToReal, h, abs_of_neg h, neg_div]
  · simp [signedScaledRatToReal, scaledRatToReal, h,
      abs_of_nonneg (le_of_not_gt h)]

/-- For an IEEE descriptor, a finite conversion of an exact rational is its nearest-even rounding,
including at tensor-size denominators. -/
theorem toReal_ofRat_eq_roundAt {format : FloatFormat} (value : Rat)
    (hformat : format.isIEEE = true) (hfinite : isFinite (ofRat format value) = true) :
    toReal (ofRat format value) = roundAt format (value : ℝ) := by
  change toReal (roundRat format (decide (value.num < 0))
    value.num.natAbs value.den) = _
  rw [roundRat, toReal_roundRatScaled_eq_roundAt
    format _ value.num.natAbs value.den 0 hformat hfinite, signedScaledRatToReal_rat]

/-- A rational whose conversion decodes back to it converts with no error. A literal such as
`127` carries no conversion error. -/
theorem toReal_ofRat_of_toRat? {format : FloatFormat} (value : Rat)
    (hexact : toRat? (ofRat format value) = some value) :
    toReal (ofRat format value) = (value : ℝ) :=
  Algebraic.toReal_of_toRat?_eq_some hexact

/-- For an IEEE descriptor, a rational no larger in magnitude than the largest finite value
converts to a finite value. -/
theorem isFinite_ofRat {format : FloatFormat} (value : Rat)
    (hformat : format.isIEEE = true)
    (hrange : |(value : ℝ)| ≤ toReal (posMaxFinite format)) :
    isFinite (ofRat format value) = true := by
  change isFinite (roundRat format (decide (value.num < 0))
    value.num.natAbs value.den) = true
  rw [roundRat]
  exact isFinite_roundRatScaled_of_abs_le_posMaxFinite format _ _ _ 0 hformat value.den_nz
    (by rwa [signedScaledRatToReal_rat])

/-- The total real observation of a value belongs to the point interval of its rational decoding,
where an exceptional value reads as `0` in both. -/
theorem containsReal_point_toRat {format : FloatFormat} (input : Model format) :
    (Interval.point ((toRat? input).getD 0)).ContainsReal some (toReal input) := by
  apply (Interval.containsReal_some_iff _ _).mpr
  simp only [Interval.point, cast_toRat_eq_toReal, le_refl, and_self]

/-- Bounds the error of a finite implementation result by a certified rational enclosure. Both
finiteness premises are part of the numerical interface, and the statement does not relate
`input` to `candidate`. The rational budget can be evaluated apart from the proof, without
assuming that the implementation is correctly rounded. -/
theorem abs_toReal_sub_le_of_containsReal {inputFormat outputFormat : FloatFormat}
    (input : Model inputFormat) (candidate : Model outputFormat)
    (_hinput : isFinite input = true) (_hcandidate : isFinite candidate = true)
    {reference : ℝ} {bounds : Interval Rat}
    (contained : bounds.ContainsReal some reference) :
    |toReal candidate - reference| ≤
      ((max |(toRat? candidate).getD 0 - bounds.lo|
        |(toRat? candidate).getD 0 - bounds.hi| : Rat) : ℝ) := by
  simpa only [Rat.cast_max, Rat.cast_abs, Rat.cast_sub, cast_toRat_eq_toReal] using
    enclosure_error (toReal candidate) contained

/-- Clearing a finite value's sign is exact in every format with signed zero, as a real value. -/
theorem toReal_abs_of_isFinite {format : FloatFormat} (value : Model format)
    (hformat : format.supportsSignedZero = true) (hvalue : isFinite value = true) :
    toReal (abs value) = |toReal value| := by
  obtain ⟨dyadic, decoded⟩ := exists_toDyadic?_of_isFinite hvalue
  rw [toReal_eq, toDyadic?_abs_of_supportsSignedZero hformat decoded,
    toReal_eq, decoded]
  rw [Dyadic.abs_toReal]
  rfl

/-- For an IEEE descriptor, a finite cast of a rational inside an algorithm is within one rounding
error of the exact rational. -/
theorem abs_toReal_ofRat_sub_le {format : FloatFormat} (value : Rat)
    (hformat : format.isIEEE = true) (hfinite : isFinite (ofRat format value) = true) :
    |toReal (ofRat format value) - (value : ℝ)| ≤
      halfUlpAt format (value : ℝ) := by
  rw [toReal_ofRat_eq_roundAt value hformat hfinite]
  exact abs_roundAt_sub_le _ _

end FloatLib.Floats.Formats.BinaryInterchange.Model
