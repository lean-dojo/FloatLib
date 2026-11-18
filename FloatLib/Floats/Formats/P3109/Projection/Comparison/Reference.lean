/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Proof
public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Quantum
public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Selection

/-!
# Greatest-grid-point reference for P3109 comparison rounding

The reference selects the greatest natural code whose decoded value is at most
the nonnegative real target, capped at the first grid point above the finite
range. It does not use the executable bisection. Exact comparison then proves
equality of the rounded and saturated results. Both paths share the nine policy
threshold formulas, whose source is P3109 interim report v4.1, §4.7.4 (unapproved draft).
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.ComparisonRounding

/-- Greatest positive-grid index below a real target, including one overflow point. -/
noncomputable def referenceLower (format : Format) (target : ℝ) : Nat :=
  Nat.findGreatest
    (fun index => ((format.decodePositiveFinite index).toRat : ℝ) ≤ target)
    (format.maxFiniteBits + 1)

/-- A nonnegative target admits index zero in the greatest-grid-point specification. -/
theorem referenceLower_le_target (format : Format) (target : ℝ) (hzero : 0 ≤ target) :
    ((format.decodePositiveFinite (referenceLower format target)).toRat : ℝ) ≤ target := by
  unfold referenceLower
  apply Nat.findGreatest_spec
    (P := fun index => ((format.decodePositiveFinite index).toRat : ℝ) ≤ target)
    (Nat.zero_le _)
  simpa using hzero

/-- The capped greatest grid index is exactly the bisection result for an exact comparator. -/
theorem lowerCode_eq_referenceLower (format : Format) (compareTarget : Rat → Ordering)
    (target : ℝ) (hzero : 0 ≤ target)
    (hcompare : ∀ boundary : Rat, compareTarget boundary = cmp target (boundary : ℝ)) :
    lowerCode format compareTarget = referenceLower format target := by
  have hmax := Nat.findGreatest_le
    (P := fun index => ((format.decodePositiveFinite index).toRat : ℝ) ≤ target)
    (format.maxFiniteBits + 1)
  have hselected := referenceLower_le_target format target hzero
  have hmono : Monotone (fun index => ((format.decodePositiveFinite index).toRat : ℝ)) :=
    fun a b hab => Rat.cast_le.mpr (format.decodePositiveFinite_strictMono.monotone hab)
  unfold lowerCode
  rw [bisect_congr
    (fun index => decide
      (compareTarget (format.decodePositiveFinite index).toRat ≠ .lt))
    (fun index => decide (index ≤ referenceLower format target))
    (format.bitWidth + 1) 0 (format.maxFiniteBits + 2)]
  · apply bisect_eq_cutoff
    · exact Nat.zero_le _
    · change referenceLower format target ≤ format.maxFiniteBits + 1 at hmax
      omega
    · have hbound := format.maxFiniteBits_lt_modulus
      have hpositive := Nat.two_pow_pos format.bitWidth
      simp only [Nat.sub_zero, Nat.pow_succ, Format.modulus] at *
      omega
  · intro index _ hindex
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, hcompare, ne_eq, cmp_eq_lt_iff, not_lt]
    constructor
    · intro h
      exact Nat.le_findGreatest (by omega) h
    · intro h
      exact (hmono h).trans hselected

/-- Below the overflow index, the next grid value strictly exceeds the real target. -/
theorem referenceLower_bracket (format : Format) (target : ℝ) (hzero : 0 ≤ target)
    (hinterior : referenceLower format target < format.maxFiniteBits + 1) :
    ((format.decodePositiveFinite (referenceLower format target)).toRat : ℝ) ≤ target ∧
      target <
        ((format.decodePositiveFinite (referenceLower format target + 1)).toRat : ℝ) :=
  ⟨referenceLower_le_target format target hzero,
    lt_of_not_ge (Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hinterior)⟩

/-- A consecutive-code bracket identifies the stored significand with the scaled floor. -/
theorem floor_scaledTarget_eq_significand (format : Format) (index : Nat)
    (target : ℝ) (hzero : 0 ≤ target)
    (hlower : ((format.decodePositiveFinite index).toRat : ℝ) ≤ target)
    (hupper : target < ((format.decodePositiveFinite (index + 1)).toRat : ℝ)) :
    ⌊target / (2 : ℝ) ^ format.decodeQuantum index⌋₊ =
      (format.decodePositiveFinite index).significand := by
  have hunit : (0 : ℝ) < 2 ^ format.decodeQuantum index := zpow_pos (by norm_num) _
  rw [format.decodePositiveFinite_succ_toRat,
    format.decodePositiveFinite_toRat_eq_significand_mul] at hupper
  rw [format.decodePositiveFinite_toRat_eq_significand_mul] at hlower
  push_cast at hlower hupper
  rw [Nat.floor_eq_iff (div_nonneg hzero hunit.le), le_div_iff₀ hunit,
    div_lt_iff₀ hunit]
  exact ⟨hlower, by simpa only [add_mul, one_mul] using hupper⟩

/-- In any code bracket, executable rounding is the report's scaled fractional formula. -/
theorem roundedAt_eq_fraction (format : Format) (mode : RoundingMode)
    (negative : Bool) (index : Nat) (target : ℝ) (hzero : 0 ≤ target)
    (hlower : ((format.decodePositiveFinite index).toRat : ℝ) ≤ target)
    (hupper : target < ((format.decodePositiveFinite (index + 1)).toRat : ℝ)) :
    roundedAt format mode negative (fun boundary => cmp target (boundary : ℝ)) index =
      let exponent := format.decodeQuantum index
      let scaled := target / (2 : ℝ) ^ exponent
      let lower := ⌊scaled⌋₊
      let upper := RoundingFormula.roundAway (magnitudeMode mode negative) false
        (format.lowerCodeIsEven exponent lower) (scaled - lower)
      let rounded := if upper then lower + 1 else lower
      if rounded = 0 then .zero else ⟨negative, rounded, exponent⟩ := by
  dsimp only
  rw [floor_scaledTarget_eq_significand format index target hzero hlower hupper]
  rw [format.decodePositiveFinite_toRat_eq_significand_mul] at hlower
  push_cast at hlower
  unfold roundedAt
  dsimp only
  rw [format.roundMagnitudeUp_scaled_eq_fraction _ _ target _ hlower]

/-- Reflecting directed policies on a magnitude agrees with the signed fractional formula. -/
theorem roundAway_magnitudeMode (mode : RoundingMode) (negative lowerEven : Bool)
    (fraction : ℝ) :
    RoundingFormula.roundAway (magnitudeMode mode negative) false lowerEven fraction =
      RoundingFormula.roundAway mode negative lowerEven fraction := by
  cases negative <;> cases mode <;> rfl

/-- P3109 interim report v4.1 §4.7.4: any code bracket uses the logarithmic quantum and exact
    fraction. -/
theorem roundedAt_eq_report (format : Format) (mode : RoundingMode)
    (negative : Bool) (index : Nat) (target : ℝ) (hpositive : 0 < target)
    (hlower : ((format.decodePositiveFinite index).toRat : ℝ) ≤ target)
    (hupper : target < ((format.decodePositiveFinite (index + 1)).toRat : ℝ)) :
    roundedAt format mode negative (fun boundary => cmp target (boundary : ℝ)) index =
      let exponent :=
        max (Int.log 2 target) format.minimumNormalExponent - format.precision + 1
      let scaled := target / (2 : ℝ) ^ exponent
      let lower := ⌊scaled⌋₊
      let upper := RoundingFormula.roundAway mode negative
        (format.lowerCodeIsEven exponent lower) (scaled - lower)
      let rounded := if upper then lower + 1 else lower
      if rounded = 0 then .zero else ⟨negative, rounded, exponent⟩ := by
  rw [roundedAt_eq_fraction format mode negative index target hpositive.le hlower hupper,
    decodeQuantum_eq_log format _ target hpositive hlower hupper]
  dsimp only
  rw [roundAway_magnitudeMode]

/-- Real-comparison rounding at the independently selected greatest grid point. -/
noncomputable def referenceRounded (format : Format) (mode : RoundingMode)
    (target : ℝ) : Numerics.Dyadic :=
  if target = 0 then .zero
  else
    let negative := decide (target < 0)
    let magnitude := |target|
    roundedAt format mode negative (fun boundary => cmp magnitude (boundary : ℝ))
      (referenceLower format magnitude)

/-- Exact target comparisons refine the real greatest-grid-point rounding reference. -/
theorem rounded_eq_referenceRounded (format : Format) (mode : RoundingMode)
    (compareTarget : Rat → Ordering) (target : ℝ)
    (hcompare : ∀ boundary : Rat, compareTarget boundary = cmp target (boundary : ℝ)) :
    rounded format mode compareTarget = referenceRounded format mode target := by
  unfold rounded referenceRounded
  simp only [hcompare 0, Rat.cast_zero, cmp_eq_eq_iff]
  split
  · rfl
  next _ =>
    have hsign : (cmp target 0 == Ordering.lt) = decide (target < 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, cmp_eq_lt_iff]
    rw [hsign]
    by_cases hnegative : target < 0
    · have hnegcompare (boundary : Rat) :
          (compareTarget (-boundary)).swap = cmp (-target) (boundary : ℝ) := by
        rw [hcompare, cmp_swap, Rat.cast_neg]
        simp only [cmp, cmpUsing, neg_lt, lt_neg]
      simp only [hnegative, decide_true, ite_true, abs_of_neg hnegative]
      rw [lowerCode_eq_referenceLower format _ (-target) (neg_nonneg.mpr hnegative.le) hnegcompare]
      congr 1
      exact funext hnegcompare
    · simp only [hnegative, decide_false, Bool.false_eq_true, ite_false,
        abs_of_nonneg (le_of_not_gt hnegative)]
      rw [lowerCode_eq_referenceLower format _ target (le_of_not_gt hnegative) hcompare]
      congr 1
      exact funext hcompare

/-- The real reference applies the report saturation rule after neighbor selection. -/
noncomputable def referenceValue (format : Format) (policy : ProjectionPolicy)
    (target : ℝ) : NumericalValue Numerics.Dyadic :=
  format.saturate policy.saturation policy.rounding
    (.finite (referenceRounded format policy.rounding target))

/-- Executable saturation agrees with real comparison and greatest-grid-point selection. -/
theorem value_eq_referenceValue (format : Format) (policy : ProjectionPolicy)
    (compareTarget : Rat → Ordering) (target : ℝ)
    (hcompare : ∀ boundary : Rat, compareTarget boundary = cmp target (boundary : ℝ)) :
    value format policy compareTarget = referenceValue format policy target := by
  unfold value referenceValue
  rw [rounded_eq_referenceRounded format policy.rounding compareTarget target hcompare]

end FloatLib.Floats.Formats.P3109.ComparisonRounding
