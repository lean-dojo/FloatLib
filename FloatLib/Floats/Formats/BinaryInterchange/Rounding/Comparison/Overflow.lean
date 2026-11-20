/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Comparison.Directions

/-!
# The overflow flag of a rounding by comparisons

IEEE 754-2019 §7.4 signals overflow exactly when the largest finite number of the destination
is exceeded in magnitude by what the rounded result would be with an unbounded exponent range.
`roundAt fmt r mode` is that rounding of the real number `r`, so the condition is
`toReal (posMaxFinite fmt) < |roundAt fmt r mode|`, the premise of the overflow result in the
contract `RoundsTo`.

`ComparisonRounding.outcome` decides the flag by comparing the magnitude of `r` with a boundary
of the direction: the first value of the grid beyond the largest finite one when the direction
truncates the magnitude, the largest finite value when it rounds the magnitude up, and their
midpoint to nearest, where a tie overflows to nearest-even when the largest finite significand
is odd and always with ties away from zero. This module proves that the decision is the
condition of the standard, for every format descriptor and every rounding direction:

* `AlgebraicRounding.posMaxFinite_lt_abs_roundAt_iff`: the rounding of a magnitude on the grid
  exceeds the largest finite value exactly when the magnitude is past the boundary of the
  direction (`AlgebraicRounding.Overflows`).
* `ComparisonRounding.outcome_overflow_iff`, `deliver_overflow_iff`,
  `Rule.deliver_overflow_iff`, `unary_overflow_iff` and `binary_overflow_iff`: `overflow` is
  raised exactly when `toReal (posMaxFinite fmt) < |roundAt fmt r mode|`, through the flags, the
  rules and the operand tables. That includes a format that delivers its largest finite value
  where another delivers an infinity.
* `RoundsTo.eq_maxFinite` and `RoundsTo.signBit_of_toReal_ne_zero`: a finite rounding of a
  number beyond the range is the largest finite value of the sign, and a finite nonzero
  rounding has the sign bit of the number in every format.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats FloatLib.Numerics FloatLib.Floats.Formats.Flocq

variable {fmt : FloatFormat}

namespace AlgebraicRounding

/--
The magnitudes whose rounding by `rule` on the grid of `fmt` with an unbounded exponent range
exceeds the largest finite value: from the first value of the grid beyond it when the rule
truncates, beyond the largest finite value itself when the rule rounds up, and from the
midpoint of the two to nearest, where the midpoint itself counts with ties away from zero and,
with ties to even, when the largest finite significand is odd.
-/
def Overflows (fmt : FloatFormat) (rule : MagnitudeRounding) (t : ℝ) : Prop :=
  match rule with
  | .down => (overflowLimit fmt).toReal ≤ t
  | .up => toReal (posMaxFinite fmt) < t
  | .nearestEven => (overflowMidpoint fmt).toReal < t ∨
      (t = (overflowMidpoint fmt).toReal ∧ (maxFiniteDyadic fmt).significand % 2 = 1)
  | .nearestAway => (overflowMidpoint fmt).toReal ≤ t

/-- The real value of a dyadic number with a clear sign. -/
private theorem toReal_of_negative_eq_false (d : Numerics.Dyadic) (h : d.negative = false) :
    d.toReal = (d.significand : ℝ) * Flocq.bpow binaryRadix d.exponent := by
  simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, h, Flocq.bpow_binaryRadix]

/-- The largest finite value, the next value of the grid and their midpoint are multiples of
one power of two. -/
private theorem top_cell_values (fmt : FloatFormat) :
    toReal (posMaxFinite fmt) =
        ((maxFiniteDyadic fmt).significand : ℝ) *
          Flocq.bpow binaryRadix (maxFiniteDyadic fmt).exponent ∧
      (overflowLimit fmt).toReal =
        (((maxFiniteDyadic fmt).significand : ℝ) + 1) *
          Flocq.bpow binaryRadix (maxFiniteDyadic fmt).exponent ∧
      (overflowMidpoint fmt).toReal =
        (((maxFiniteDyadic fmt).significand : ℝ) + 1 / 2) *
          Flocq.bpow binaryRadix (maxFiniteDyadic fmt).exponent := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Dyadic.toReal_maxFiniteDyadic]
    exact toReal_of_negative_eq_false _ rfl
  · rw [toReal_of_negative_eq_false _ rfl]
    change (((maxFiniteDyadic fmt).significand + 1 : ℕ) : ℝ) *
      Flocq.bpow binaryRadix (maxFiniteDyadic fmt).exponent = _
    push_cast
    ring
  · rw [toReal_of_negative_eq_false _ rfl]
    change ((2 * (maxFiniteDyadic fmt).significand + 1 : ℕ) : ℝ) *
      Flocq.bpow binaryRadix ((maxFiniteDyadic fmt).exponent - 1) = _
    rw [Flocq.bpow_binaryRadix, Flocq.bpow_binaryRadix,
      zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    push_cast
    ring

/-- The canonical exponent of a magnitude in the cell of the grid above the largest finite
value. -/
private theorem cexp_of_top_cell {t : ℝ} (hlower : toReal (posMaxFinite fmt) ≤ t)
    (hupper : t < (overflowLimit fmt).toReal) :
    cexp binaryRadix (fexpOf fmt) t = (maxFiniteDyadic fmt).exponent := by
  obtain ⟨hmax, hlimit, -⟩ := top_cell_values fmt
  have hpow := Flocq.bpow.pos binaryRadix (maxFiniteDyadic fmt).exponent
  have ht : 0 < t := (toReal_posMaxFinite_pos fmt).trans_le hlower
  have hsignificand : 2 ^ fmt.fracWidth ≤ (maxFiniteDyadic fmt).significand ∧
      (maxFiniteDyadic fmt).significand + 1 ≤ 2 ^ (fmt.fracWidth + 1) := by
    have := fmt.maxFiniteFracField_lt_two_pow
    simp only [maxFiniteDyadic, pow2_eq_two_pow, pow_succ]
    omega
  have hexponent : fmt.maxNormalExponent =
      (fmt.fracWidth : ℤ) + (maxFiniteDyadic fmt).exponent := by
    simp only [maxFiniteDyadic, Int.ofNat_eq_natCast]
    ring
  have hsplit (k : ℕ) : Flocq.bpow binaryRadix ((k : ℤ) + (maxFiniteDyadic fmt).exponent) =
      ((2 ^ k : ℕ) : ℝ) * Flocq.bpow binaryRadix (maxFiniteDyadic fmt).exponent := by
    rw [Flocq.bpow.add_exp, Flocq.bpow_binaryRadix (k : ℤ), zpow_natCast]
    push_cast
    rfl
  have hlo : Flocq.bpow binaryRadix (fmt.maxNormalExponent + 1 - 1) ≤ |t| := by
    rw [abs_of_pos ht, add_sub_cancel_right, hexponent, hsplit]
    refine le_trans ?_ hlower
    rw [hmax]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsignificand.1) hpow.le
  have hhi : |t| < Flocq.bpow binaryRadix (fmt.maxNormalExponent + 1) := by
    rw [abs_of_pos ht]
    refine lt_of_lt_of_le hupper ?_
    rw [hlimit, hexponent,
      show (fmt.fracWidth : ℤ) + (maxFiniteDyadic fmt).exponent + 1 =
        ((fmt.fracWidth + 1 : ℕ) : ℤ) + (maxFiniteDyadic fmt).exponent by push_cast; ring,
      hsplit]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsignificand.2) hpow.le
  have hmagnitude := magnitude_eq_of_bpow_bounds binaryRadix t (fmt.maxNormalExponent + 1) hlo hhi
  have hfield := fmt.maxFiniteExpField_pos
  simp only [cexp, hmagnitude, fexpOf, fltExp, maxFiniteDyadic, FloatFormat.minSubnormalExponent,
    FloatFormat.minNormalExponent, FloatFormat.maxNormalExponent, Int.ofNat_eq_natCast]
  omega

/--
A magnitude in the cell of the grid above the largest finite value rounds, in every direction,
to that value or to the next value of the grid. A guard bit and a sticky bit name its place in
the cell, and the rule of the direction decides from them and from the parity of the largest
finite significand.
-/
private theorem roundAt_top_cell (mode : IEEERoundingMode) {t : ℝ}
    (hlower : toReal (posMaxFinite fmt) ≤ t) (hupper : t < (overflowLimit fmt).toReal) :
    ∃ guard sticky : Bool,
      (guard = true ↔ (overflowMidpoint fmt).toReal ≤ t) ∧
      (sticky = true ↔ t ≠ toReal (posMaxFinite fmt) ∧ t ≠ (overflowMidpoint fmt).toReal) ∧
      roundAt fmt t mode =
        if (mode.magnitudeRounding false).increment
            ((maxFiniteDyadic fmt).significand % 2 == 1) guard sticky = true
        then (overflowLimit fmt).toReal else toReal (posMaxFinite fmt) := by
  obtain ⟨hmax, hlimit, hmid⟩ := top_cell_values fmt
  have hpow := Flocq.bpow.pos binaryRadix (maxFiniteDyadic fmt).exponent
  have hcexp := cexp_of_top_cell hlower hupper
  obtain ⟨w, rfl⟩ : ∃ w : ℝ, t = w * Flocq.bpow binaryRadix (maxFiniteDyadic fmt).exponent :=
    ⟨t / Flocq.bpow binaryRadix (maxFiniteDyadic fmt).exponent,
      (div_mul_cancel₀ t hpow.ne').symm⟩
  rw [hmax] at hlower
  rw [hlimit] at hupper
  have hwlo : ((maxFiniteDyadic fmt).significand : ℝ) ≤ w := le_of_mul_le_mul_right hlower hpow
  have hwhi : w < ((maxFiniteDyadic fmt).significand : ℝ) + 1 :=
    lt_of_mul_lt_mul_right hupper hpow.le
  have hscaled : scaledMantissa binaryRadix (fexpOf fmt)
      (w * Flocq.bpow binaryRadix (maxFiniteDyadic fmt).exponent) = w := by
    rw [scaledMantissa_eq_div, hcexp, mul_div_cancel_right₀ _ hpow.ne']
  have hround (guard sticky : Bool)
      (hbracket : InbetweenInt ((maxFiniteDyadic fmt).significand : ℤ) w
        (location guard sticky)) :
      roundAt fmt (w * Flocq.bpow binaryRadix (maxFiniteDyadic fmt).exponent) mode =
        if (mode.magnitudeRounding false).increment
            ((maxFiniteDyadic fmt).significand % 2 == 1) guard sticky = true
        then (overflowLimit fmt).toReal else toReal (posMaxFinite fmt) := by
    have hlocated : Located fmt (w * Flocq.bpow binaryRadix (maxFiniteDyadic fmt).exponent)
        (maxFiniteDyadic fmt).significand (maxFiniteDyadic fmt).exponent guard sticky :=
      ⟨hcexp, by rw [hscaled]; exact hbracket⟩
    rw [hlocated.roundAt_eq mode, hmax, hlimit]
    split_ifs <;> push_cast <;> ring
  have hmidLe : (overflowMidpoint fmt).toReal ≤
      w * Flocq.bpow binaryRadix (maxFiniteDyadic fmt).exponent ↔
      ((maxFiniteDyadic fmt).significand : ℝ) + 1 / 2 ≤ w := by
    rw [hmid]
    exact ⟨fun h => le_of_mul_le_mul_right h hpow,
      fun h => mul_le_mul_of_nonneg_right h hpow.le⟩
  have hmaxEq : w * Flocq.bpow binaryRadix (maxFiniteDyadic fmt).exponent ≠
      toReal (posMaxFinite fmt) ↔ w ≠ ((maxFiniteDyadic fmt).significand : ℝ) := by
    rw [hmax]
    exact not_congr ⟨fun h => mul_right_cancel₀ hpow.ne' h, fun h => by rw [h]⟩
  have hmidEq : w * Flocq.bpow binaryRadix (maxFiniteDyadic fmt).exponent ≠
      (overflowMidpoint fmt).toReal ↔ w ≠ ((maxFiniteDyadic fmt).significand : ℝ) + 1 / 2 := by
    rw [hmid]
    exact not_congr ⟨fun h => mul_right_cancel₀ hpow.ne' h, fun h => by rw [h]⟩
  rcases lt_trichotomy w (((maxFiniteDyadic fmt).significand : ℝ) + 1 / 2) with hlt | heq | hgt
  · rcases eq_or_lt_of_le hwlo with hexact | hstrict
    · refine ⟨false, false, ?_, ?_, hround false false (.exact (by simpa using hexact.symm))⟩
      · rw [hmidLe]
        exact iff_of_false (by decide) (not_le.mpr hlt)
      · rw [hmaxEq]
        exact iff_of_false (by decide) fun h => h.1 hexact.symm
    · refine ⟨false, true, ?_, ?_, hround false true
        (.inexact .lt ⟨by simpa using hstrict, by push_cast; linarith⟩
          ((cmp_eq_lt_iff _ _).mpr (by push_cast; linarith)))⟩
      · rw [hmidLe]
        exact iff_of_false (by decide) (not_le.mpr hlt)
      · rw [hmaxEq, hmidEq]
        exact iff_of_true rfl ⟨hstrict.ne', hlt.ne⟩
  · refine ⟨true, false, ?_, ?_, hround true false
      (.inexact .eq ⟨by push_cast; linarith, by push_cast; linarith⟩
        ((cmp_eq_eq_iff _ _).mpr (by push_cast; linarith)))⟩
    · rw [hmidLe]
      exact iff_of_true rfl heq.ge
    · rw [hmidEq]
      exact iff_of_false (by decide) fun h => h.2 heq
  · refine ⟨true, true, ?_, ?_, hround true true
      (.inexact .gt ⟨by push_cast; linarith, by push_cast; linarith⟩
        ((cmp_eq_gt_iff _ _).mpr (by push_cast; linarith)))⟩
    · rw [hmidLe]
      exact iff_of_true rfl hgt.le
    · rw [hmaxEq, hmidEq]
      exact iff_of_true rfl
        ⟨(show ((maxFiniteDyadic fmt).significand : ℝ) < w by linarith).ne', hgt.ne'⟩

/--
The rounding of a real number on the grid of the format, in any direction, exceeds the largest
finite value exactly when the number is past the boundary of the rule that the direction
applies to a positive value.
-/
theorem posMaxFinite_lt_roundAt_iff (mode : IEEERoundingMode) (t : ℝ) :
    toReal (posMaxFinite fmt) < roundAt fmt t mode ↔
      Overflows fmt (mode.magnitudeRounding false) t := by
  obtain ⟨hmax, hlimit, hmid⟩ := top_cell_values fmt
  have hpow := Flocq.bpow.pos binaryRadix (maxFiniteDyadic fmt).exponent
  have hmaxMid : toReal (posMaxFinite fmt) < (overflowMidpoint fmt).toReal := by
    rw [hmax, hmid]
    linarith
  have hmidLimit : (overflowMidpoint fmt).toReal < (overflowLimit fmt).toReal := by
    rw [hmid, hlimit]
    linarith
  have hgrid := toReal_genericFormat_of_isFinite _ (isFinite_posMaxFinite fmt)
  rcases lt_or_ge t (toReal (posMaxFinite fmt)) with hbelow | hlower
  · -- Below the largest finite value nothing overflows.
    have hle : roundAt fmt t mode ≤ toReal (posMaxFinite fmt) := by
      have h := roundAt_mono fmt hbelow.le mode
      rwa [roundAt_of_genericFormat fmt hgrid mode] at h
    refine iff_of_false (not_lt.mpr hle) ?_
    generalize mode.magnitudeRounding false = rule
    cases rule with
    | down => exact fun h : (overflowLimit fmt).toReal ≤ t => by linarith
    | up => exact fun h : toReal (posMaxFinite fmt) < t => by linarith
    | nearestEven =>
        rintro (h | ⟨h, -⟩)
        · linarith
        · linarith
    | nearestAway => exact fun h : (overflowMidpoint fmt).toReal ≤ t => by linarith
  rcases lt_or_ge t (overflowLimit fmt).toReal with hupper | habove
  · -- In the cell above the largest finite value the rule decides.
    obtain ⟨guard, sticky, hguard, hsticky, hvalue⟩ := roundAt_top_cell mode hlower hupper
    have hsplit : ∀ condition : Prop, [Decidable condition] →
        (toReal (posMaxFinite fmt) <
          (if condition then (overflowLimit fmt).toReal else toReal (posMaxFinite fmt)) ↔
            condition) := by
      intro condition _
      by_cases h : condition
      · rw [ite_eq_left h]
        exact iff_of_true (hmaxMid.trans hmidLimit) h
      · rw [ite_eq_right h]
        exact iff_of_false (lt_irrefl _) h
    rw [hvalue, hsplit]
    generalize mode.magnitudeRounding false = rule
    cases rule with
    | down =>
        simp only [MagnitudeRounding.increment]
        exact iff_of_false (by decide) (not_le.mpr hupper)
    | up =>
        simp only [MagnitudeRounding.increment, Bool.or_eq_true]
        constructor
        · rintro (h | h)
          · exact hmaxMid.trans_le (hguard.mp h)
          · exact lt_of_le_of_ne hlower (Ne.symm (hsticky.mp h).1)
        · intro (h : toReal (posMaxFinite fmt) < t)
          by_cases hmidpoint : t = (overflowMidpoint fmt).toReal
          · exact .inl (hguard.mpr hmidpoint.ge)
          · exact .inr (hsticky.mpr ⟨h.ne', hmidpoint⟩)
    | nearestEven =>
        simp only [MagnitudeRounding.increment, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
        constructor
        · rintro ⟨h, h' | h'⟩
          · exact .inl (lt_of_le_of_ne (hguard.mp h) (Ne.symm (hsticky.mp h').2))
          · rcases eq_or_lt_of_le (hguard.mp h) with hequal | hless
            · exact .inr ⟨hequal.symm, h'⟩
            · exact .inl hless
        · rintro (h | ⟨h, h'⟩)
          · exact ⟨hguard.mpr h.le, .inl (hsticky.mpr ⟨(hmaxMid.trans h).ne', h.ne'⟩)⟩
          · exact ⟨hguard.mpr h.ge, .inr h'⟩
    | nearestAway =>
        simp only [MagnitudeRounding.increment]
        exact hguard
  · -- From the next value of the grid on, every direction overflows.
    obtain ⟨guard, sticky, hguard, -, hvalue⟩ :=
      roundAt_top_cell (fmt := fmt) .away hmaxMid.le hmidLimit
    have hnext : roundAt fmt (overflowMidpoint fmt).toReal .away = (overflowLimit fmt).toReal := by
      rw [hvalue]
      simp [IEEERoundingMode.magnitudeRounding, MagnitudeRounding.increment, hguard.mpr le_rfl]
    have hgridLimit := genericFormat_roundAt fmt (overflowMidpoint fmt).toReal .away
    rw [hnext] at hgridLimit
    have hge : (overflowLimit fmt).toReal ≤ roundAt fmt t mode := by
      have h := roundAt_mono fmt habove mode
      rwa [roundAt_of_genericFormat fmt hgridLimit mode] at h
    refine iff_of_true ((hmaxMid.trans hmidLimit).trans_le hge) ?_
    generalize mode.magnitudeRounding false = rule
    cases rule with
    | down => exact habove
    | up => exact (hmaxMid.trans hmidLimit).trans_le habove
    | nearestEven => exact .inl (hmidLimit.trans_le habove)
    | nearestAway => exact (hmidLimit.trans_le habove).le

/--
**Where the rounding of a real number overflows.** For every format descriptor, every rounding
direction and a magnitude `t > 0` with either sign, the rounding on the grid of the format with
an unbounded exponent range exceeds the largest finite value in magnitude exactly when `t` is
past the boundary of the rule that the direction applies to that sign.
-/
theorem posMaxFinite_lt_abs_roundAt_iff (mode : IEEERoundingMode) (negative : Bool) {t : ℝ}
    (ht : 0 < t) :
    toReal (posMaxFinite fmt) < |roundAt fmt (if negative then -t else t) mode| ↔
      Overflows fmt (mode.magnitudeRounding negative) t := by
  have hnonneg (mode : IEEERoundingMode) : 0 ≤ roundAt fmt t mode := by
    simpa only [roundAt_zero] using roundAt_mono fmt ht.le mode
  cases negative with
  | false =>
      change toReal (posMaxFinite fmt) < |roundAt fmt t mode| ↔ _
      rw [abs_of_nonneg (hnonneg mode)]
      exact posMaxFinite_lt_roundAt_iff mode t
  | true =>
      change toReal (posMaxFinite fmt) < |roundAt fmt (-t) mode| ↔ _
      rw [roundAt_neg fmt t mode, abs_neg, abs_of_nonneg (hnonneg mode.negate)]
      have h := posMaxFinite_lt_roundAt_iff (fmt := fmt) mode.negate t
      rwa [IEEERoundingMode.magnitudeRounding_negate, Bool.not_false] at h

end AlgebraicRounding

/-- A finite value that is the rounding of a number beyond the range is the largest finite
value of the sign: the direction keeps the result finite, or the format has neither an infinity
nor a NaN. -/
theorem RoundsTo.eq_maxFinite {mode : IEEERoundingMode} {x : ℝ} {sign : Bool}
    {value : Model fmt} (h : RoundsTo fmt mode x sign value)
    (hbeyond : toReal (posMaxFinite fmt) < |roundAt fmt x mode|)
    (hfinite : isFinite value = true) : value = maxFinite fmt sign := by
  have hoverflow := h.overflow hbeyond
  rw [hoverflow] at hfinite ⊢
  unfold directedOverflow at hfinite ⊢
  split_ifs at hfinite ⊢
  · have hencoding := encoding_finite_of_nativeOverflow _ hfinite
    simp [nativeOverflow, hencoding]
  · rfl

/-- A finite nonzero value that is the rounding of a nonzero number has the sign bit of that
number, in every format: only a zero and a NaN can differ. -/
theorem RoundsTo.signBit_of_toReal_ne_zero {mode : IEEERoundingMode} {x : ℝ}
    {value : Model fmt} (h : RoundsTo fmt mode x (decide (x < 0)) value) (hx : x ≠ 0)
    (hfinite : isFinite value = true) (hnonzero : toReal value ≠ 0) :
    Model.signBit value = decide (x < 0) := by
  by_cases hrange : |roundAt fmt x mode| ≤ toReal (posMaxFinite fmt)
  · have hreal := (h.finite hrange).2
    rcases lt_or_gt_of_ne hx with hnegative | hpositive
    · have hle : toReal value ≤ 0 := by
        rw [hreal]
        simpa only [roundAt_zero] using roundAt_mono fmt hnegative.le mode
      rw [decide_eq_true hnegative]
      exact signBit_eq_true_of_toReal_neg (lt_of_le_of_ne hle hnonzero)
    · have hge : 0 ≤ toReal value := by
        rw [hreal]
        simpa only [roundAt_zero] using roundAt_mono fmt hpositive.le mode
      rw [decide_eq_false (not_lt.mpr hpositive.le)]
      exact signBit_eq_false_of_toReal_pos hfinite (lt_of_le_of_ne hge (Ne.symm hnonzero))
  · rw [h.eq_maxFinite (not_le.mp hrange) hfinite]
    simp [maxFinite]

namespace ComparisonRounding

/--
The decision of `outcome` on the overflow flag of a finite delivery that is inexact and has the
largest finite magnitude: the comparisons of the magnitude of the located number, which
`magnitude` orders against a rational, with the boundary of the direction.
-/
def roundsBeyond (fmt : FloatFormat) (mode : IEEERoundingMode) (negative : Bool)
    (magnitude : ℚ → Ordering) : Bool :=
  match mode with
  | .nearest =>
      match magnitude (overflowMidpoint fmt).toRat with
      | .gt => true
      | .eq => maxFiniteMantissaOdd fmt
      | .lt => false
  | .nearestAway => magnitude (overflowMidpoint fmt).toRat != .lt
  | .towardZero | .up | .down | .away =>
      if mode.roundsAwayFromZero negative then magnitude (maxFiniteDyadic fmt).toRat == .gt
      else magnitude (overflowLimit fmt).toRat != .lt

/-- For an exact comparator of a magnitude, `roundsBeyond` holds exactly when the magnitude is
past the boundary of the direction. -/
theorem roundsBeyond_iff {magnitude : ℚ → Ordering} {t : ℝ}
    (hmagnitude : ∀ boundary : ℚ, magnitude boundary = cmp t (boundary : ℝ))
    (mode : IEEERoundingMode) (negative : Bool) :
    roundsBeyond fmt mode negative magnitude = true ↔
      AlgebraicRounding.Overflows fmt (mode.magnitudeRounding negative) t := by
  have hgt (d : Numerics.Dyadic) : (magnitude d.toRat == .gt) = true ↔ d.toReal < t := by
    rw [hmagnitude, Numerics.Dyadic.cast_toRat]
    rcases lt_trichotomy t d.toReal with h | h | h
    · rw [(cmp_eq_lt_iff _ _).mpr h]
      exact iff_of_false (by decide) (not_lt.mpr h.le)
    · rw [(cmp_eq_eq_iff _ _).mpr h]
      exact iff_of_false (by decide) (not_lt.mpr h.le)
    · rw [(cmp_eq_gt_iff _ _).mpr h]
      exact iff_of_true rfl h
  have hge (d : Numerics.Dyadic) : (magnitude d.toRat != .lt) = true ↔ d.toReal ≤ t := by
    rw [hmagnitude, Numerics.Dyadic.cast_toRat]
    rcases lt_trichotomy t d.toReal with h | h | h
    · rw [(cmp_eq_lt_iff _ _).mpr h]
      exact iff_of_false (by decide) (not_le.mpr h)
    · rw [(cmp_eq_eq_iff _ _).mpr h]
      exact iff_of_true rfl h.ge
    · rw [(cmp_eq_gt_iff _ _).mpr h]
      exact iff_of_true rfl h.le
  have hnearest : (match magnitude (overflowMidpoint fmt).toRat with
      | .gt => true
      | .eq => maxFiniteMantissaOdd fmt
      | .lt => false) = true ↔
      ((overflowMidpoint fmt).toReal < t ∨
        (t = (overflowMidpoint fmt).toReal ∧ (maxFiniteDyadic fmt).significand % 2 = 1)) := by
    rw [hmagnitude, Numerics.Dyadic.cast_toRat]
    rcases lt_trichotomy t (overflowMidpoint fmt).toReal with h | h | h
    · rw [(cmp_eq_lt_iff _ _).mpr h]
      refine iff_of_false (fun hfalse => Bool.false_ne_true hfalse) ?_
      rintro (h' | ⟨h', -⟩) <;> linarith
    · rw [(cmp_eq_eq_iff _ _).mpr h]
      constructor
      · intro hodd
        exact .inr ⟨h, by simpa [maxFiniteMantissaOdd] using hodd⟩
      · rintro (h' | ⟨-, hodd⟩)
        · linarith
        · simpa [maxFiniteMantissaOdd] using hodd
    · rw [(cmp_eq_gt_iff _ _).mpr h]
      exact iff_of_true rfl (.inl h)
  have hup : (magnitude (maxFiniteDyadic fmt).toRat == .gt) = true ↔
      toReal (posMaxFinite fmt) < t := by
    rw [← Dyadic.toReal_maxFiniteDyadic fmt]
    exact hgt _
  cases mode with
  | nearest => exact hnearest
  | nearestAway => exact hge _
  | towardZero => exact hge _
  | up =>
      cases negative
      · exact hup
      · exact hge _
  | down =>
      cases negative
      · exact hge _
      · exact hup
  | away => exact hup

/-- The comparator that `outcome` builds for the magnitude of the located number orders that
magnitude, when the sign it uses is the sign of the number. -/
theorem magnitude_abs {compare : ℚ → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (boundary : ℚ) :
    (if decide (target < 0) = true then (compare (-boundary)).swap else compare boundary) =
      cmp |target| (boundary : ℝ) := by
  by_cases h : target < 0
  · rw [ite_eq_left (decide_eq_true h), magnitude_compare hcompare, abs_of_neg h]
  · rw [ite_eq_right (by simpa using h), hcompare, abs_of_nonneg (not_lt.mp h)]

/-- The overflow flag of a finite delivery is `inexact`, the fields of the largest finite
magnitude and the decision `roundsBeyond`. -/
private theorem outcome_overflow_eq {value : Model fmt} {delivered : ℚ}
    (hdelivered : toRat? value = some delivered) (compare : ℚ → Ordering)
    (mode : IEEERoundingMode) (known : Option Ordering) :
    (outcome fmt compare value mode known).status.overflow =
      ((outcome fmt compare value mode known).status.inexact &&
        (expField value == fmt.maxFiniteExpField && fracField value == fmt.maxFiniteFracField) &&
        roundsBeyond fmt mode (signBit value) fun boundary =>
          if signBit value = true then (compare (-boundary)).swap else compare boundary) := by
  unfold outcome
  simp only [hdelivered]
  rfl

/-- A value with the fields of the largest finite magnitude has that magnitude. -/
private theorem abs_toReal_of_largest {value : Model fmt}
    (hfields : (expField value == fmt.maxFiniteExpField &&
      fracField value == fmt.maxFiniteFracField) = true) :
    |toReal value| = toReal (posMaxFinite fmt) := by
  obtain ⟨hexponent, hfraction⟩ : expField value = fmt.maxFiniteExpField ∧
      fracField value = fmt.maxFiniteFracField := by simpa using hfields
  have hvalue : value = maxFinite fmt (signBit value) := by
    have h := ofFields_signBit_expField_fracField value
    rw [hexponent, hfraction] at h
    exact h.symm
  rw [hvalue, toReal_maxFinite]
  have hpositive := toReal_posMaxFinite_pos fmt
  cases signBit value <;> simp [abs_of_pos hpositive]

/--
**The overflow flag is the overflow of the standard.** For every format descriptor and rounding
direction, a comparator of the nonzero real number `target` and a value that is the rounding of
`target` (`RoundsTo`), the outcome raises `overflow` exactly when the rounding of `target` on
the grid of the format with an unbounded exponent range exceeds the largest finite value in
magnitude (IEEE 754-2019 §7.4), whether the delivery is an infinity, a NaN or the largest
finite value.
-/
theorem outcome_overflow_iff {compare : ℚ → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (hne : target ≠ 0) {value : Model fmt} {mode : IEEERoundingMode} {known : Option Ordering}
    (hknown : ∀ ordering, known = some ordering → ordering = cmp (toReal value) target)
    (hvalue : RoundsTo fmt mode target (decide (target < 0)) value) :
    (outcome fmt compare value mode known).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt target mode| := by
  have htarget : (if decide (target < 0) = true then -|target| else |target|) = target := by
    by_cases h : target < 0
    · rw [ite_eq_left (decide_eq_true h), abs_of_neg h, _root_.neg_neg]
    · rw [ite_eq_right (by simpa using h), abs_of_nonneg (not_lt.mp h)]
  have hboundary := AlgebraicRounding.posMaxFinite_lt_abs_roundAt_iff (fmt := fmt) mode
    (decide (target < 0)) (abs_pos.mpr hne)
  rw [htarget] at hboundary
  have hdecision (h : signBit value = decide (target < 0)) :
      roundsBeyond fmt mode (signBit value) (fun boundary =>
        if signBit value = true then (compare (-boundary)).swap else compare boundary) = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt target mode| := by
    rw [h, hboundary]
    exact roundsBeyond_iff (magnitude_abs hcompare) mode _
  cases hdelivered : toRat? value with
  | none =>
      have hbeyond : toReal (posMaxFinite fmt) < |roundAt fmt target mode| := by
        by_contra hrange
        obtain ⟨q, hq, -⟩ :=
          Algebraic.exists_toRat?_of_isFinite (hvalue.finite (not_lt.mp hrange)).1
        rw [hdelivered] at hq
        exact absurd hq (by simp)
      refine iff_of_true ?_ hbeyond
      unfold outcome
      split
      · next q hq =>
          rw [hdelivered] at hq
          exact absurd hq (by simp)
      · rfl
  | some delivered =>
      have hfinite := Algebraic.isFinite_of_toRat?_eq_some hdelivered
      rw [outcome_overflow_eq hdelivered, Bool.and_eq_true, Bool.and_eq_true]
      by_cases hrange : |roundAt fmt target mode| ≤ toReal (posMaxFinite fmt)
      · -- In range: a delivery of the largest finite magnitude is not past the boundary.
        refine iff_of_false ?_ (not_lt.mpr hrange)
        rintro ⟨⟨-, hlargest⟩, hbeyond⟩
        have hmagnitude := abs_toReal_of_largest hlargest
        have hnonzero : toReal value ≠ 0 := by
          intro hzero
          rw [hzero, abs_zero] at hmagnitude
          exact (toReal_posMaxFinite_pos fmt).ne hmagnitude
        exact absurd
          ((hdecision (hvalue.signBit_of_toReal_ne_zero hne hfinite hnonzero)).mp hbeyond)
          (not_lt.mpr hrange)
      · -- Out of range: the delivery is the largest finite value of the sign, and it is inexact.
        have hbeyond := not_le.mp hrange
        refine iff_of_true ?_ hbeyond
        have hmaximum := hvalue.eq_maxFinite hbeyond hfinite
        have hfields : (expField value == fmt.maxFiniteExpField &&
            fracField value == fmt.maxFiniteFracField) = true := by
          rw [hmaximum]
          simp [maxFinite, Nat.mod_eq_of_lt fmt.maxFiniteExpField_lt_two_pow,
            Nat.mod_eq_of_lt fmt.maxFiniteFracField_lt_two_pow]
        have hsign : signBit value = decide (target < 0) := by
          rw [hmaximum]
          simp [maxFinite]
        have hinexact : (outcome fmt compare value mode known).status.inexact = true := by
          rw [outcome_inexact_iff compare target hcompare mode hknown hfinite]
          intro hexact
          have hgrid := roundAt_of_genericFormat fmt
            (toReal_genericFormat_of_isFinite value hfinite) mode
          rw [hexact] at hgrid
          rw [hgrid, ← hexact, abs_toReal_of_largest hfields] at hbeyond
          exact lt_irrefl _ hbeyond
        exact ⟨⟨hinexact, hfields⟩, (hdecision hsign).mpr hbeyond⟩

/--
**A delivery raises `overflow` exactly when the standard asks for it.** For every format
descriptor, a comparator of the nonzero real number `target` and a hint that is right about
`target` and has its sign, `deliver` raises `overflow` in the direction `mode` exactly when
`roundAt fmt target mode` exceeds the largest finite value in magnitude.
-/
theorem deliver_overflow_iff {compare : ℚ → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (hne : target ≠ 0) (mode : IEEERoundingMode) {hint : Unit → Option (Hint fmt)}
    (hsound : Hint.Sound hint target) (hsigned : Hint.Signed hint target) :
    (deliver fmt compare mode hint).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt target mode| :=
  outcome_overflow_iff hcompare hne (resolve_ternary compare mode hsound)
    (resolve_roundsTo compare hne hcompare hsound hsigned)

/-- A rule that locates the nonzero real number `target` raises `overflow` exactly when
`roundAt fmt target mode` exceeds the largest finite value in magnitude. -/
theorem Rule.deliver_overflow_iff {rule : Rule} {target : ℝ} (hrule : rule.Locates target)
    (hne : target ≠ 0) (mode : IEEERoundingMode) {hint : Unit → Option (Hint fmt)}
    (hsound : Hint.Sound hint target) (hsigned : Hint.Signed hint target) :
    (rule.deliver fmt mode hint).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt target mode| := by
  cases rule with
  | zero negative => exact absurd hrule hne
  | real compare => exact ComparisonRounding.deliver_overflow_iff hrule hne mode hsound hsigned
  | infinity negative => exact absurd hrule id
  | pole negative => exact absurd hrule id
  | invalid => exact absurd hrule id

/--
**The overflow flag of a function of one operand.** For every format descriptor, a finite
operand whose rule locates the nonzero real number `target` and a hint that is right about
`target` and has its sign at that operand, the result in the direction `mode` raises `overflow`
exactly when `roundAt fmt target mode` exceeds the largest finite value in magnitude.
-/
theorem unary_overflow_iff (rule : Operand → Rule) {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) {target : ℝ}
    (hrule : (rule (.finite (signBit x) q)).Locates target) (hne : target ≠ 0)
    (mode : IEEERoundingMode) {hint : Operand → Unit → Option (Hint fmt)}
    (hsound : Hint.Sound (hint (.finite (signBit x) q)) target)
    (hsigned : Hint.Signed (hint (.finite (signBit x) q)) target) :
    (unary rule x mode hint).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt target mode| := by
  rw [unary_of_toRat? rule hq]
  exact Rule.deliver_overflow_iff hrule hne mode hsound hsigned

/--
**The overflow flag of a function of two operands.** For every format descriptor, finite
operands whose rule locates the nonzero real number `target` and a hint that is right about
`target` and has its sign at those operands, the result in the direction `mode` raises
`overflow` exactly when `roundAt fmt target mode` exceeds the largest finite value in magnitude.
-/
theorem binary_overflow_iff (rule : Operand → Operand → Rule) {x y : Model fmt} {p q : ℚ}
    (hp : toRat? x = some p) (hq : toRat? y = some q) {target : ℝ}
    (hrule : (rule (.finite (signBit x) p) (.finite (signBit y) q)).Locates target)
    (hne : target ≠ 0) (mode : IEEERoundingMode)
    {hint : Operand → Operand → Unit → Option (Hint fmt)}
    (hsound : Hint.Sound (hint (.finite (signBit x) p) (.finite (signBit y) q)) target)
    (hsigned : Hint.Signed (hint (.finite (signBit x) p) (.finite (signBit y) q)) target) :
    (binary rule x y mode hint).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt target mode| := by
  rw [binary_of_toRat? rule hp hq]
  exact Rule.deliver_overflow_iff hrule hne mode hsound hsigned

end ComparisonRounding

end FloatLib.Floats.Formats.BinaryInterchange.Model
