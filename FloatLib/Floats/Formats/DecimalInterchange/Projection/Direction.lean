/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Semantics

/-!
# Directed projection bounds

Without overflow, the returned datum is finite and bounds the exact input from the side the
rounding direction prescribes. Every finite result does that, even on overflow. Rounding toward
positive saturates a negative overflow to the most negative finite datum, which lies above the
input, and rounding toward negative saturates a positive overflow to the greatest one. Rounding
toward zero can't increase the magnitude, with or without overflow. The bounds cover subnormal
results and both signs of an exact zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Rounding toward positive without overflow, projecting a magnitude with either sign gives a
finite datum at least the signed exact value. -/
theorem projectMagnitude_up_le (f : Format) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hq : (roundedPair f .up s x).2 ≤ f.maxQuantum) :
    ∃ value, (projectMagnitude f .up s x preferred).value.toRat? = some value ∧
      (if s then -x else x) ≤ value := by
  exact ⟨_, projectMagnitude_value f .up s x preferred hq,
    RoundingMode.le_roundAt_up s hx _⟩

/-- Rounding toward negative without overflow, projecting a magnitude with either sign gives a
finite datum at most the signed exact value. -/
theorem projectMagnitude_down_le (f : Format) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hq : (roundedPair f .down s x).2 ≤ f.maxQuantum) :
    ∃ value, (projectMagnitude f .down s x preferred).value.toRat? = some value ∧
      value ≤ (if s then -x else x) := by
  exact ⟨_, projectMagnitude_value f .down s x preferred hq,
    RoundingMode.roundAt_down_le s hx _⟩

/-- Rounding toward positive, every finite datum projected from a magnitude with sign `s` is at
least the signed exact value. Unlike `projectMagnitude_up_le`, this covers overflow: an
overflowing negative input saturates to the most negative finite datum, which lies above it, and an
overflowing positive one delivers `+∞`, which has no rational value. -/
theorem le_projectMagnitude_up_of_toRat?_eq_some (f : Format) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (value : ℚ) (preferred : Int)
    (hv : (projectMagnitude f .up s x preferred).value.toRat? = some value) :
    (if s then -x else x) ≤ value := by
  by_cases hq : (roundedPair f .up s x).2 ≤ f.maxQuantum
  · obtain ⟨rounded, hrounded, hle⟩ := projectMagnitude_up_le f s hx preferred hq
    obtain rfl : value = rounded := Option.some.inj (hv.symm.trans hrounded)
    exact hle
  · have hq' := lt_of_not_ge hq
    have hlt := maxFinite_lt_of_roundedPair_overflow f .up s hx hq'
    cases s <;> simp [projectMagnitude_eq, hq', RoundingMode.overflowToInfinity, Format.maxFinite,
      Datum.toRat?_eq] at hv
    rw [← hv]
    simpa using hlt.le

/-- Rounding toward negative, every finite datum projected from a magnitude with sign `s` is at most
the signed exact value. Unlike `projectMagnitude_down_le`, this covers overflow: an
overflowing positive input saturates to the greatest finite datum, which lies below it, and an
overflowing negative one delivers `-∞`, which has no rational value. -/
theorem projectMagnitude_down_le_of_toRat?_eq_some (f : Format) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (value : ℚ) (preferred : Int)
    (hv : (projectMagnitude f .down s x preferred).value.toRat? = some value) :
    value ≤ (if s then -x else x) := by
  by_cases hq : (roundedPair f .down s x).2 ≤ f.maxQuantum
  · obtain ⟨rounded, hrounded, hle⟩ := projectMagnitude_down_le f s hx preferred hq
    obtain rfl : value = rounded := Option.some.inj (hv.symm.trans hrounded)
    exact hle
  · have hq' := lt_of_not_ge hq
    have hlt := maxFinite_lt_of_roundedPair_overflow f .down s hx hq'
    cases s <;> simp [projectMagnitude_eq, hq', RoundingMode.overflowToInfinity, Format.maxFinite,
      Datum.toRat?_eq] at hv
    rw [← hv]
    simpa using hlt.le

/-- If upward rounding does not overflow, the projected datum is finite and an upper bound on the
exact rational input. `le_project_up_of_toRat?_eq_some` covers every finite result. -/
theorem le_project_up (f : Format) (x : ℚ) (preferred : Int)
    (negativeZero : Bool)
    (hfinite : (project f .up x preferred negativeZero).status.overflow = false) :
    ∃ value, (project f .up x preferred negativeZero).value.toRat? = some value ∧
      x ≤ value := by
  have hq := project_quantum_le_of_no_overflow f .up x preferred negativeZero
    hfinite
  simpa only [project, signed_abs] using projectMagnitude_up_le f
    (if x = 0 then negativeZero else decide (x < 0)) (abs_nonneg x) preferred hq

/-- If downward rounding does not overflow, the projected datum is finite and a lower bound on the
exact rational input. `project_down_le_of_toRat?_eq_some` covers every finite result. -/
theorem project_down_le (f : Format) (x : ℚ) (preferred : Int)
    (negativeZero : Bool)
    (hfinite : (project f .down x preferred negativeZero).status.overflow = false) :
    ∃ value, (project f .down x preferred negativeZero).value.toRat? = some value ∧
      value ≤ x := by
  have hq := project_quantum_le_of_no_overflow f .down x preferred negativeZero
    hfinite
  simpa only [project, signed_abs] using projectMagnitude_down_le f
    (if x = 0 then negativeZero else decide (x < 0)) (abs_nonneg x) preferred hq

/-- Every finite upward-rounded datum is an upper bound on the exact rational input, also when the
projection overflows and saturates to the most negative finite datum. -/
theorem le_project_up_of_toRat?_eq_some (f : Format) (x value : ℚ) (preferred : Int)
    (negativeZero : Bool)
    (hv : (project f .up x preferred negativeZero).value.toRat? = some value) :
    x ≤ value := by
  simpa only [signed_abs] using le_projectMagnitude_up_of_toRat?_eq_some f
    (if x = 0 then negativeZero else decide (x < 0)) (abs_nonneg x) value preferred hv

/-- Every finite downward-rounded datum is a lower bound on the exact rational input, also when the
projection overflows and saturates to the greatest finite datum. -/
theorem project_down_le_of_toRat?_eq_some (f : Format) (x value : ℚ) (preferred : Int)
    (negativeZero : Bool)
    (hv : (project f .down x preferred negativeZero).value.toRat? = some value) :
    value ≤ x := by
  simpa only [signed_abs] using projectMagnitude_down_le_of_toRat?_eq_some f
    (if x = 0 then negativeZero else decide (x < 0)) (abs_nonneg x) value preferred hv

/-- Rounding toward zero cannot increase the magnitude, and the result is always finite: an
overflow delivers the greatest finite datum, which lies below the exact magnitude. -/
theorem abs_project_towardZero_le (f : Format) (x : ℚ) (preferred : Int)
    (negativeZero : Bool) :
    ∃ value, (project f .towardZero x preferred negativeZero).value.toRat? = some value ∧
      |value| ≤ |x| := by
  let s := if x = 0 then negativeZero else decide (x < 0)
  by_cases hq : (roundedPair f .towardZero s |x|).2 ≤ f.maxQuantum
  · refine ⟨_, projectMagnitude_value f .towardZero s |x| preferred hq, ?_⟩
    have hu : 0 < (10 : ℚ) ^ roundingQuantum f |x| := zpow_pos (by norm_num) _
    have h := RoundingMode.roundMagnitude_towardZero_le s (div_nonneg (abs_nonneg x) hu.le)
    have hs := mul_le_mul_of_nonneg_right h hu.le
    rw [div_mul_cancel₀ _ hu.ne'] at hs
    have habs : |(if s then (-1 : ℚ) else 1)| = 1 := by cases s <;> norm_num
    have hc : (0 : ℚ) ≤ RoundingMode.towardZero.roundMagnitude s
        (|x| / (10 : ℚ) ^ roundingQuantum f |x|) := Nat.cast_nonneg _
    simpa only [RoundingMode.roundAt, abs_mul, habs, one_mul,
      abs_of_nonneg hc, abs_of_pos hu] using hs
  · have hq' := lt_of_not_ge hq
    have hlt := maxFinite_lt_of_roundedPair_overflow f .towardZero s (abs_nonneg x) hq'
    have hm : (0 : ℚ) ≤ ((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum :=
      mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
    refine ⟨(if s then -1 else 1) * ((f.coefficientBound - 1 : Nat) : ℚ) *
      (10 : ℚ) ^ f.maxQuantum, ?_, ?_⟩
    · simp [project, s, projectMagnitude_eq, hq', RoundingMode.overflowToInfinity,
        Format.maxFinite, Datum.toRat?_eq]
    · cases s <;> simpa [abs_of_nonneg hm] using hlt.le

end FloatLib.Floats.Formats.DecimalInterchange
