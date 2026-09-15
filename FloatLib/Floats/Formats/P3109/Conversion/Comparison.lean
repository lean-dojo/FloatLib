/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Conversion.Runtime
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Semantics
public import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Exact meaning of conversion range comparisons

The scalable rational/dyadic comparator first tests signs and leading exponents. Its answer
is the ordinary rational order, including zero significands and negative values. This connects
the executable conversion range indicator with the mathematical finite interval.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109

private theorem compare_rat_cast (left right : Rat) :
    compare (left : Real) (right : Real) = compare left right := by
  simp [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]

private theorem compareDyadic_positive (numerator denominator : Nat)
    (value : Numerics.Dyadic) (hd : denominator ≠ 0)
    (hs : value.negative = false) (hv : value.significand ≠ 0) :
    RationalBinary.compareDyadic? false numerator denominator value =
      some (compare ((numerator : Rat) / denominator) value.toRat) := by
  have h := BinaryInterchange.Model.compareDyadicScaled?_false_eq_compare
    numerator denominator 0 value hd hs hv
  have hc : BinaryInterchange.Model.scaledRatToReal numerator denominator 0 =
      (((numerator : Rat) / denominator : Rat) : Real) := by
    simp [BinaryInterchange.Model.scaledRatToReal]
  rw [hc, ← Numerics.Dyadic.cast_toRat, compare_rat_cast] at h
  exact h

/-- The scalable comparison with an arbitrary dyadic is its exact signed rational order. -/
theorem compareDyadic_eq_compare (negative : Bool) (numerator denominator : Nat)
    (value : Numerics.Dyadic) (hd : denominator ≠ 0) :
    RationalBinary.compareDyadic? negative numerator denominator value =
      some (compare (RationalRounding.signed negative ((numerator : Rat) / denominator))
        value.toRat) := by
  have hden : (0 : Rat) < denominator := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hp : (0 : Rat) < (2 : Rat) ^ value.exponent := by positivity
  by_cases hn : numerator = 0
  · by_cases hv : value.significand = 0
    · cases negative <;>
        simp [RationalBinary.compareDyadic?, RationalBinary.compareDyadicScaled?, hd, hn, hv,
          RationalRounding.signed, Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand]
    have ht : (0 : Rat) < (value.significand : Rat) * (2 : Rat) ^ value.exponent :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hv) hp
    cases negative <;> cases hs : value.negative <;>
      simp [RationalBinary.compareDyadic?, RationalBinary.compareDyadicScaled?, hd, hn, hv,
        hs, RationalRounding.signed, Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand,
        LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq, ht, ht.ne', ht.le]
  have hnum : (0 : Rat) < (numerator : Rat) / denominator :=
    div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hden
  by_cases hv : value.significand = 0
  · cases negative <;>
      simp [RationalBinary.compareDyadic?, RationalBinary.compareDyadicScaled?, hd, hn, hv,
        RationalRounding.signed, Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand,
        LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq, hnum, hnum.ne',
        not_lt_of_ge hnum.le]
  let positive : Numerics.Dyadic := ⟨false, value.significand, value.exponent⟩
  have hpositive : (0 : Rat) < (value.significand : Rat) * (2 : Rat) ^ value.exponent :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hv) hp
  have hc := compareDyadic_positive numerator denominator positive hd rfl hv
  simp only [RationalBinary.compareDyadic?, RationalBinary.compareDyadicScaled?, hd, hn,
    hv, positive, beq_iff_eq, Bool.false_eq_true, if_false, bne_self_eq_false] at hc
  have hncompare (a b : Rat) :
      (compare a b).swap = compare (-a) (-b) := by
    rcases lt_trichotomy a b with h | h | h
    · simp [compare_lt_iff_lt.mpr h, compare_gt_iff_gt.mpr (neg_lt_neg h)]
    · simp [h]
    · simp [compare_gt_iff_gt.mpr h, compare_lt_iff_lt.mpr (neg_lt_neg h)]
  cases negative <;> cases hs : value.negative
  · simpa [RationalBinary.compareDyadic?, RationalBinary.compareDyadicScaled?, hd, hn,
      hv, hs, RationalRounding.signed, positive, Numerics.Dyadic.toRat,
      Numerics.Dyadic.signedSignificand] using hc
  · have hlt : -((value.significand : Rat) * (2 : Rat) ^ value.exponent) <
        (numerator : Rat) / denominator := by nlinarith
    simp [RationalBinary.compareDyadic?, RationalBinary.compareDyadicScaled?, hd, hn,
      hv, hs, RationalRounding.signed, Numerics.Dyadic.toRat,
      Numerics.Dyadic.signedSignificand, compare_gt_iff_gt.mpr hlt]
  · have hlt : -((numerator : Rat) / denominator) <
        (value.significand : Rat) * (2 : Rat) ^ value.exponent := by nlinarith
    simp [RationalBinary.compareDyadic?, RationalBinary.compareDyadicScaled?, hd, hn,
      hv, hs, RationalRounding.signed, Numerics.Dyadic.toRat,
      Numerics.Dyadic.signedSignificand, compare_lt_iff_lt.mpr hlt]
  · have he := Option.some.inj hc
    simp only [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand,
      Bool.false_eq_true, if_false] at he
    simp only [RationalBinary.compareDyadic?, RationalBinary.compareDyadicScaled?, hd, hn,
      hv, hs, beq_iff_eq, if_false, bne_self_eq_false,
      if_true, RationalRounding.signed]
    rw [he, hncompare]
    simp [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand, hs]

end FloatLib.Floats.Formats.P3109

namespace FloatLib.Floats.ExecFloat.P3109.Conversion

open Formats.P3109

/-- The executable exact-range test is precisely strict exclusion from the finite interval. -/
theorem exceedsFiniteRange_eq_decide (format : Format) (exact : Rat) :
    exceedsFiniteRange format exact =
      decide (exact < format.minFinite.toRat ∨ format.maxFinite.toRat < exact) := by
  have hs : RationalRounding.signed (exact.num < 0) ((exact.num.natAbs : Rat) / exact.den) =
      exact := by
    rw [← RationalRounding.magnitude_eq_ratio]
    exact RationalRounding.signed_abs exact
  simp only [exceedsFiniteRange, compareDyadic_eq_compare _ _ _ _ exact.den_ne_zero, hs]
  apply Bool.eq_iff_iff.mpr
  simp [compare_lt_iff_lt, compare_gt_iff_gt]

/-- The pre-saturation overflow indicator is strict exclusion of the rounded rational value. -/
theorem roundedExceedsFiniteRange_eq_decide (format : Format) (mode : RoundingMode)
    (exact : Rat) :
    roundedExceedsFiniteRange format mode exact =
      decide ((format.roundFiniteRatToPrecision mode exact).toRat < format.minFinite.toRat ∨
        format.maxFinite.toRat < (format.roundFiniteRatToPrecision mode exact).toRat) := by
  simp only [roundedExceedsFiniteRange, Numerics.Dyadic.Internal.compareScalable_eq_compare,
    Numerics.Dyadic.compare_eq_compare_toRat]
  apply Bool.eq_iff_iff.mpr
  simp [compare_lt_iff_lt]

end FloatLib.Floats.ExecFloat.P3109.Conversion
