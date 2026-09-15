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
extended-real lower bound for downward conversion and non-NaN results in both directions.
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

/-- Rewrite a rational cast into the signed numerator form used by the executable rounders. -/
private theorem ratCast_eq_signed_div (q : Rat) :
    (q : ℝ) =
      if q.num < 0 then
        -((q.num.natAbs : ℝ) / (q.den : ℝ))
      else
        (q.num.natAbs : ℝ) / (q.den : ℝ) := by
  rw [Rat.cast_def]
  split_ifs with h
  · simp [abs_of_neg h]
    ring
  · have hn : 0 ≤ q.num := le_of_not_gt h
    simp [abs_of_nonneg hn]

/-- Downward conversion of an exact rational is an extended-real lower bound. -/
theorem toEReal_roundRatQDown_le (fmt : FloatFormat) (q : Rat)
    (hfmt : fmt.isIEEE = true) :
    toEReal (roundRatQDown fmt q) ≤ ((q : ℝ) : EReal) := by
  rw [ratCast_eq_signed_div]
  by_cases h : q.num < 0
  · simpa [roundRatQDown, roundRatQWithRounding, roundRatDown,
      signedScaledRatToReal, scaledRatToReal, bpow, bpow, h,
      EReal.coe_div, EReal.coe_neg] using
      (toEReal_roundRatDown_le fmt (q.num < 0) q.num.natAbs q.den hfmt q.den_nz)
  · simpa [roundRatQDown, roundRatQWithRounding, roundRatDown,
      signedScaledRatToReal, scaledRatToReal, bpow, bpow, h, EReal.coe_div] using
      (toEReal_roundRatDown_le fmt (q.num < 0) q.num.natAbs q.den hfmt q.den_nz)

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
