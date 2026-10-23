/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Rat.Floor
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Bounds
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime

/-!
# Exact rational conversion for directed `Model` rounding

`Model.ofRat fmt q` rounds a normalized mathlib `Rat` once into any `Model fmt`, to nearest with
ties to even. `(mode := .up)` selects another direction and `(status := true)` adds the IEEE
exception flags and the ternary value. For conventional IEEE formats, directed overflow returns
either a signed infinity or the largest finite value of the same sign, according to the rounding
direction. The conversion theorems establish the extended-real lower and upper bounds and non-NaN
results in both directions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats.Formats.Flocq

/--
Round an exact rational once into `fmt`, in the direction `mode` (nearest-even by default). With
`status := true` the result is the `IEEEOutcome` carrying the exception flags and the ternary
value of that rounding.
-/
@[macro_inline] def ofRat (fmt : FloatFormat) (q : Rat) (mode : IEEERoundingMode := .nearest)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true =>
      rationalRoundingOutcomeScaled fmt mode (q.num < 0) q.num.natAbs q.den 0
        (Internal.Directed.roundRat fmt mode (q.num < 0) q.num.natAbs q.den)
  | false => Internal.Directed.roundRat fmt mode (q.num < 0) q.num.natAbs q.den

/-- Rounding a rational with `status := true` delivers the value of the same rounding. -/
@[simp] theorem value_ofRat (fmt : FloatFormat) (q : Rat) (mode : IEEERoundingMode) :
    (ofRat fmt q (mode := mode) (status := true)).value = ofRat fmt q (mode := mode) :=
  rfl

/-- The signed numerator and scale-zero representation denotes the normalized rational. -/
private theorem signedScaledRatToReal_of_rat (q : Rat) :
    signedScaledRatToReal (q.num < 0) q.num.natAbs q.den 0 = (q : ℝ) := by
  rw [Rat.cast_def]
  by_cases h : q.num < 0
  · simp [signedScaledRatToReal, scaledRatToReal, h, abs_of_neg h, neg_div]
  · simp [signedScaledRatToReal, scaledRatToReal, h, abs_of_nonneg (le_of_not_gt h)]

/-- Downward conversion of an exact rational is an extended-real lower bound. -/
theorem toEReal_ofRat_down_le (fmt : FloatFormat) (q : Rat)
    (hfmt : fmt.isIEEE = true) :
    toEReal (ofRat fmt q (mode := .down)) ≤ ((q : ℝ) : EReal) := by
  simpa only [ofRat, roundRatDown, signedScaledRatToReal_of_rat]
    using toEReal_roundRatDown_le fmt (q.num < 0) q.num.natAbs q.den hfmt q.den_nz

/--
Upward conversion of an exact rational is an extended-real upper bound, including zero,
subnormal rounding, and overflow to positive infinity.
-/
theorem le_toEReal_ofRat_up (fmt : FloatFormat) (q : Rat)
    (hfmt : fmt.isIEEE = true) :
    ((q : ℝ) : EReal) ≤ toEReal (ofRat fmt q (mode := .up)) := by
  simpa only [ofRat, roundRatUp, signedScaledRatToReal_of_rat]
    using le_toEReal_roundRatUp fmt (q.num < 0) q.num.natAbs q.den hfmt q.den_nz

/-- Downward conversion of a normalized rational never produces NaN. -/
theorem isNaN_ofRat_down_eq_false (fmt : FloatFormat) (q : Rat)
    (hfmt : fmt.isIEEE = true) :
    isNaN (ofRat fmt q (mode := .down)) = false := by
  simpa [ofRat, roundRatDown] using
    (isNaN_roundRatDown_eq_false fmt (q.num < 0) q.num.natAbs q.den hfmt q.den_nz)

/-- Upward conversion of a normalized rational never produces NaN. -/
theorem isNaN_ofRat_up_eq_false (fmt : FloatFormat) (q : Rat)
    (hfmt : fmt.isIEEE = true) :
    isNaN (ofRat fmt q (mode := .up)) = false := by
  simpa [ofRat, roundRatUp] using
    (isNaN_roundRatUp_eq_false fmt (q.num < 0) q.num.natAbs q.den hfmt q.den_nz)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
