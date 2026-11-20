/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Reference

/-!
# Full real report specification for exact-comparison projection

P3109 interim report v4.1, 14 September 2026, §§4.7.4–4.7.5 (unapproved draft).
The specification uses the logarithmic quantum and the exact real fractional
part. The proof compares an uncapped code bracket with the executable capped
search; saturation removes their possible difference outside the finite range.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.ComparisonRounding

/-- P3109 interim report v4.1, §4.7.4 precision rounding over the exact real magnitude and its
    fractional part. -/
noncomputable def reportRounded (format : Format) (mode : RoundingMode)
    (target : ℝ) : Numerics.Dyadic :=
  if target = 0 then .zero
  else
    let negative := decide (target < 0)
    let exponent :=
      max (Int.log 2 |target|) format.minimumNormalExponent - format.precision + 1
    let scaled := |target| / (2 : ℝ) ^ exponent
    let lower := ⌊scaled⌋₊
    let upper := RoundingFormula.roundAway mode negative
      (format.lowerCodeIsEven exponent lower) (scaled - lower)
    let rounded := if upper then lower + 1 else lower
    if rounded = 0 then .zero else ⟨negative, rounded, exponent⟩

/-- P3109 interim report v4.1, §§4.7.4–4.7.5: logarithmic precision rounding followed by
    saturation. -/
noncomputable def reportValue (format : Format) (policy : ProjectionPolicy)
    (target : ℝ) : NumericalValue Numerics.Dyadic :=
  format.saturate policy.saturation policy.rounding
    (.finite (reportRounded format policy.rounding target))

/-- Every code step is at least one minimum quantum, hence the positive grid is unbounded. -/
theorem mul_minimumQuantum_le_decode (format : Format) (index : Nat) :
    (index : Rat) * 2 ^ format.minimumQuantumExponent ≤
      (format.decodePositiveFinite index).toRat := by
  induction index with
  | zero => simp
  | succ index ih =>
      rw [format.decodePositiveFinite_succ_toRat]
      have hstep := (zpow_right_strictMono₀ (by norm_num : (1 : Rat) < 2)).monotone
        (minimumQuantumExponent_le_decodeQuantum format index)
      push_cast
      linarith

/-- Every nonnegative real lies between two consecutive values of the uncapped code grid. -/
theorem exists_code_bracket (format : Format) (target : ℝ) (hzero : 0 ≤ target) :
    ∃ index : Nat, ((format.decodePositiveFinite index).toRat : ℝ) ≤ target ∧
      target < ((format.decodePositiveFinite (index + 1)).toRat : ℝ) := by
  have hunit : (0 : ℝ) < 2 ^ format.minimumQuantumExponent := zpow_pos (by norm_num) _
  have hexists : ∃ index : Nat, target < ((format.decodePositiveFinite index).toRat : ℝ) := by
    obtain ⟨index, hindex⟩ := exists_nat_gt (target / (2 : ℝ) ^ format.minimumQuantumExponent)
    refine ⟨index, ((div_lt_iff₀ hunit).mp hindex).trans_le ?_⟩
    have hbound :
        (((index : Rat) * 2 ^ format.minimumQuantumExponent : Rat) : ℝ) ≤
          ((format.decodePositiveFinite index).toRat : ℝ) :=
      Rat.cast_le.mpr (mul_minimumQuantum_le_decode format index)
    push_cast at hbound
    simpa only [Numerics.Dyadic.cast_toRat] using hbound
  have hpositive : 0 < Nat.find hexists := by
    by_contra h
    have hz : Nat.find hexists = 0 := by omega
    have h := Nat.find_spec hexists
    rw [hz] at h
    have hnegative : target < 0 := by simpa using h
    exact hnegative.not_ge hzero
  refine ⟨Nat.find hexists - 1, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hexists (by omega))
  · simpa only [Nat.sub_add_cancel hpositive] using Nat.find_spec hexists

/-- The capped real reference is the minimum of the true lower code and the overflow cap. -/
theorem referenceLower_eq_min (format : Format) (index : Nat) (target : ℝ)
    (hlower : ((format.decodePositiveFinite index).toRat : ℝ) ≤ target)
    (hupper : target < ((format.decodePositiveFinite (index + 1)).toRat : ℝ)) :
    referenceLower format target = min index (format.maxFiniteBits + 1) := by
  unfold referenceLower
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨Nat.min_le_right _ _, ?_, ?_⟩
  · intro _
    exact (Rat.cast_le.mpr (format.decodePositiveFinite_strictMono.monotone
      (Nat.min_le_left _ _))).trans hlower
  · intro other hother hcap hle
    have hindex : index + 1 ≤ other := by omega
    exact (hupper.trans_le (Rat.cast_le.mpr
      (format.decodePositiveFinite_strictMono.monotone hindex))).not_ge hle

/-- Saturation is constant on signed dyadics whose magnitude exceeds the finite endpoint. -/
theorem saturate_mk_of_max_lt (format : Format) (policy : ProjectionPolicy)
    (negative : Bool) (significand : Nat) (exponent : Int)
    (habove : format.maxFinite.toRat < (significand : Rat) * 2 ^ exponent) :
    format.saturate policy.saturation policy.rounding
        (.finite ⟨negative, significand, exponent⟩) =
      if negative then Format.Internal.saturateBelow format policy.saturation policy.rounding
      else Format.Internal.saturateAbove format policy.saturation policy.rounding := by
  cases negative with
  | false =>
      have hcompare :
          Numerics.Dyadic.Internal.compareScalable format.maxFinite
            ⟨false, significand, exponent⟩ = .lt := by
        rw [Numerics.Dyadic.Internal.compareScalable_eq_compare,
          Numerics.Dyadic.compare_eq_lt_iff, Numerics.Dyadic.toRat_mk_false]
        exact habove
      simp [Format.saturate, hcompare]
  | true =>
      have hbelow :
          (⟨true, significand, exponent⟩ : Numerics.Dyadic).toRat <
            format.minFinite.toRat := by
        have hvalue :
            (⟨true, significand, exponent⟩ : Numerics.Dyadic).toRat =
              -((significand : Rat) * 2 ^ exponent) := by
          simp [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand]
        rw [hvalue]
        cases hsigned : format.signedness with
        | signed =>
            rw [Format.minFinite, hsigned, Numerics.Dyadic.neg_toRat]
            exact neg_lt_neg habove
        | unsigned =>
            rw [Format.minFinite, hsigned, Numerics.Dyadic.zero_toRat]
            exact neg_neg_of_pos (format.maxFinite_toRat_pos.trans habove)
      have hcompare :
          Numerics.Dyadic.Internal.compareScalable
            ⟨true, significand, exponent⟩ format.minFinite = .lt := by
        rw [Numerics.Dyadic.Internal.compareScalable_eq_compare,
          Numerics.Dyadic.compare_eq_lt_iff]
        exact hbelow
      simp [Format.saturate, hcompare]

/-- Rounding at any code above the finite endpoint gives the same exterior saturation. -/
theorem saturate_roundedAt_of_above (format : Format) (policy : ProjectionPolicy)
    (negative : Bool) (compareTarget : Rat → Ordering) (index : Nat)
    (habove : format.maxFiniteBits < index) :
    format.saturate policy.saturation policy.rounding
        (.finite (roundedAt format policy.rounding negative compareTarget index)) =
      if negative then Format.Internal.saturateBelow format policy.saturation policy.rounding
      else Format.Internal.saturateAbove format policy.saturation policy.rounding := by
  have hvalue : format.maxFinite.toRat < (format.decodePositiveFinite index).toRat :=
    format.decodePositiveFinite_strictMono habove
  have hsignificand : 0 < (format.decodePositiveFinite index).significand := by
    exact Nat.pos_of_ne_zero
      ((format.decodePositiveFinite_significand_eq_zero_iff index).not.mpr (by omega))
  have hcandidate (n : Nat) (hn : (format.decodePositiveFinite index).significand ≤ n) :
      format.saturate policy.saturation policy.rounding
          (.finite ⟨negative, n, format.decodeQuantum index⟩) =
        if negative then Format.Internal.saturateBelow format policy.saturation policy.rounding
        else Format.Internal.saturateAbove format policy.saturation policy.rounding := by
    apply saturate_mk_of_max_lt
    apply hvalue.trans_le
    rw [format.decodePositiveFinite_toRat_eq_significand_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by positivity)
  unfold roundedAt
  dsimp only
  split <;>
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      Nat.ne_of_gt hsignificand, ite_false] <;>
    exact hcandidate _ (by omega)

/-- Clipping a lower code at the overflow sentinel preserves the final saturated result. -/
theorem saturate_roundedAt_min (format : Format) (policy : ProjectionPolicy)
    (negative : Bool) (compareTarget : Rat → Ordering) (index : Nat) :
    format.saturate policy.saturation policy.rounding
        (.finite (roundedAt format policy.rounding negative compareTarget
          (min index (format.maxFiniteBits + 1)))) =
      format.saturate policy.saturation policy.rounding
        (.finite (roundedAt format policy.rounding negative compareTarget index)) := by
  by_cases hindex : index ≤ format.maxFiniteBits + 1
  · rw [Nat.min_eq_left hindex]
  · rw [Nat.min_eq_right (by omega),
      saturate_roundedAt_of_above format policy negative compareTarget _ (by omega),
      saturate_roundedAt_of_above format policy negative compareTarget index (by omega)]

/-- The capped real reference equals the full logarithmic report result after saturation. -/
theorem referenceValue_eq_reportValue (format : Format) (policy : ProjectionPolicy)
    (target : ℝ) :
    referenceValue format policy target = reportValue format policy target := by
  by_cases hzero : target = 0
  · simp [referenceValue, referenceRounded, reportValue, reportRounded, hzero]
  have hpositive : 0 < |target| := abs_pos.mpr hzero
  obtain ⟨index, hlower, hupper⟩ := exists_code_bracket format |target| hpositive.le
  unfold referenceValue referenceRounded reportValue reportRounded
  simp only [hzero, ite_false]
  rw [referenceLower_eq_min format index |target| hlower hupper,
    saturate_roundedAt_min]
  rw [roundedAt_eq_report format policy.rounding _ index |target| hpositive hlower hupper]

/-- Exact comparisons implement P3109's real logarithmic rounding and saturation for all inputs.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7.3–4.7.5.
-/
theorem value_eq_reportValue (format : Format) (policy : ProjectionPolicy)
    (compareTarget : Rat → Ordering) (target : ℝ)
    (hcompare : ∀ boundary : Rat, compareTarget boundary = cmp target (boundary : ℝ)) :
    value format policy compareTarget = reportValue format policy target := by
  rw [value_eq_referenceValue format policy compareTarget target hcompare,
    referenceValue_eq_reportValue]

end FloatLib.Floats.Formats.P3109.ComparisonRounding
