/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Rat.Floor
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Bounds

/-!
# Exact rational conversion for directed `Model` rounding

Normalized mathlib `Rat` values round directly into any `Model fmt`. For conventional IEEE
formats, directed overflow returns either a signed infinity or the largest finite value of the
same sign, according to the rounding direction. The conversion theorems establish the
extended-real lower and upper bounds and non-NaN results in both directions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats.Formats.Flocq

/-- Round an exact rational according to an IEEE rounding direction. -/
def roundRatQWithRounding (fmt : FloatFormat) (mode : IEEERoundingMode)
    (q : Rat) : Model fmt :=
  roundRatWithRounding fmt mode (q.num < 0) q.num.natAbs q.den

/-- Round an exact rational to nearest, ties to even. -/
def roundRatQ (fmt : FloatFormat) (q : Rat) : Model fmt :=
  roundRatQWithRounding fmt .nearestEven q

/-- Round an exact rational toward negative infinity. -/
def roundRatQDown (fmt : FloatFormat) (q : Rat) : Model fmt :=
  roundRatQWithRounding fmt .towardNegativeInfinity q

/-- Round an exact rational toward positive infinity. -/
def roundRatQUp (fmt : FloatFormat) (q : Rat) : Model fmt :=
  roundRatQWithRounding fmt .towardPositiveInfinity q

/-- The signed numerator and scale-zero representation denotes the normalized rational. -/
private theorem signedScaledRatToReal_of_rat (q : Rat) :
    signedScaledRatToReal (q.num < 0) q.num.natAbs q.den 0 = (q : ℝ) := by
  rw [Rat.cast_def]
  by_cases h : q.num < 0
  · simp [signedScaledRatToReal, scaledRatToReal, h, abs_of_neg h, neg_div]
  · simp [signedScaledRatToReal, scaledRatToReal, h, abs_of_nonneg (le_of_not_gt h)]

/-- Downward conversion of an exact rational is an extended-real lower bound. -/
theorem toEReal_roundRatQDown_le (fmt : FloatFormat) (q : Rat)
    (hfmt : fmt.isIEEE = true) :
    toEReal (roundRatQDown fmt q) ≤ ((q : ℝ) : EReal) := by
  simpa only [roundRatQDown, roundRatQWithRounding, roundRatDown, signedScaledRatToReal_of_rat]
    using toEReal_roundRatDown_le fmt (q.num < 0) q.num.natAbs q.den hfmt q.den_nz

/--
Upward conversion of an exact rational is an extended-real upper bound, including zero,
subnormal rounding, and overflow to positive infinity.
-/
theorem le_toEReal_roundRatQUp (fmt : FloatFormat) (q : Rat)
    (hfmt : fmt.isIEEE = true) :
    ((q : ℝ) : EReal) ≤ toEReal (roundRatQUp fmt q) := by
  simpa only [roundRatQUp, roundRatQWithRounding, roundRatUp, signedScaledRatToReal_of_rat]
    using le_toEReal_roundRatUp fmt (q.num < 0) q.num.natAbs q.den hfmt q.den_nz

/-- Downward conversion of a normalized rational never produces NaN. -/
theorem isNaN_roundRatQDown_eq_false (fmt : FloatFormat) (q : Rat)
    (hfmt : fmt.isIEEE = true) :
    isNaN (roundRatQDown fmt q) = false := by
  simpa [roundRatQDown, roundRatQWithRounding, roundRatDown] using
    (isNaN_roundRatDown_eq_false fmt (q.num < 0) q.num.natAbs q.den hfmt q.den_nz)

/-- Upward conversion of a normalized rational never produces NaN. -/
theorem isNaN_roundRatQUp_eq_false (fmt : FloatFormat) (q : Rat)
    (hfmt : fmt.isIEEE = true) :
    isNaN (roundRatQUp fmt q) = false := by
  simpa [roundRatQUp, roundRatQWithRounding, roundRatUp] using
    (isNaN_roundRatUp_eq_false fmt (q.num < 0) q.num.natAbs q.den hfmt q.den_nz)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
