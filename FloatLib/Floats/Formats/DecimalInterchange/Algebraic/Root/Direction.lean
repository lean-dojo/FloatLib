/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Root.Proof

/-!
# Directed rounding of signed integer-degree roots

Negative roots flip the directed modes. Rounding a negative result's coefficient up moves the
signed value down, so upward and downward coefficient rounding swap roles, and with that swap the
delivered signed datum lies on the side of the exact signed real root that each directed mode
promises.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Rounding toward positive, a nonoverflowing rounded root is finite and at least the signed real
root, for either sign of the result. -/
theorem le_rootMagnitude_up (f : Format) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (rootMagnitude f .up s degree x preferred).status.overflow = false) :
    ∃ value : ℚ,
      (rootMagnitude f .up s degree x preferred).value.toRat? = some value ∧
        (if s then -1 else 1) * realRoot degree (x : ℝ) ≤ (value : ℝ) := by
  obtain ⟨value, hv, he⟩ :=
    rootMagnitude_value_sub_realRoot f .up s hn hx preferred hfinite
  refine ⟨value, hv, ?_⟩
  have hu : 0 < (10 : ℝ) ^ rootQuantum f degree x := zpow_pos (by norm_num) _
  have hy : 0 ≤ x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x) :=
    div_nonneg hx (zpow_pos (by norm_num) _).le
  have hg : 0 ≤ (if s then -1 else 1 : ℝ) *
      ((RoundingMode.up.rootRound s degree
          (x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x)) : ℝ) -
        realRoot degree ((x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x) : ℚ) : ℝ)) := by
    cases s
    · simpa using le_rootRound_directed_up false hn hy
    · simpa using rootRound_directed_down_le true hn hy
  linarith [mul_nonneg hg hu.le]

/-- Rounding a root toward negative is rounding toward positive with the result sign reversed: the
flags agree and the delivered datums are negations of each other, including infinities and the
greatest finite datum on overflow. -/
theorem rootMagnitude_down (f : Format) (s : Bool) (degree : Nat) (x : ℚ)
    (preferred : Int) :
    rootMagnitude f .down s degree x preferred =
      { value := (rootMagnitude f .up (!s) degree x preferred).value.negate
        status := (rootMagnitude f .up (!s) degree x preferred).status } := by
  have hr : rootPair f .down s degree x = rootPair f .up (!s) degree x := by
    cases s <;> rfl
  simp only [rootMagnitude, hr]
  split
  · cases s <;> rfl
  · cases s <;> simp only [apply_ite Datum.negate] <;> rfl

/-- Rounding toward negative, a nonoverflowing rounded root is finite and at most the signed real
root, for either sign of the result. It is the upward bound for the opposite sign, negated. -/
theorem rootMagnitude_down_le (f : Format) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (rootMagnitude f .down s degree x preferred).status.overflow = false) :
    ∃ value : ℚ,
      (rootMagnitude f .down s degree x preferred).value.toRat? = some value ∧
        (value : ℝ) ≤ (if s then -1 else 1) * realRoot degree (x : ℝ) := by
  rw [rootMagnitude_down] at hfinite ⊢
  obtain ⟨value, hv, hle⟩ := le_rootMagnitude_up f (!s) hn hx preferred hfinite
  refine ⟨-value, Datum.negate_toRat?_of_eq_some hv, ?_⟩
  cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hle ⊢ <;>
    push_cast <;> linarith

/-- Rounding toward zero, a rounded root is finite and no larger in magnitude than the real root.
An overflow delivers the greatest finite datum, which lies below the root. -/
theorem abs_rootMagnitude_towardZero_le (f : Format) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int) :
    ∃ value : ℚ,
      (rootMagnitude f .towardZero s degree x preferred).value.toRat? = some value ∧
        |(value : ℝ)| ≤ realRoot degree (x : ℝ) := by
  by_cases hq : (rootPair f .towardZero s degree x).2 ≤ f.maxQuantum
  swap
  · have hq' := lt_of_not_ge hq
    have hlt := maxFinite_lt_realRoot_of_overflow f .towardZero s hn hx hq'
    have hm : (0 : ℝ) ≤ ((f.coefficientBound - 1 : Nat) : ℝ) * (10 : ℝ) ^ f.maxQuantum :=
      mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
    refine ⟨(if s then -1 else 1) * ((f.coefficientBound - 1 : Nat) : ℚ) *
      (10 : ℚ) ^ f.maxQuantum, ?_, ?_⟩
    · simp [rootMagnitude, hq', RoundingMode.overflowToInfinity, Format.maxFinite,
        Datum.toRat?_eq]
    · cases s <;> simpa [abs_of_nonneg hm] using hlt.le
  refine ⟨_, rootMagnitude_value f .towardZero s degree x preferred hq, ?_⟩
  let q := rootQuantum f degree x
  have hy : 0 ≤ x / (10 : ℚ) ^ ((degree : Int) * q) :=
    div_nonneg hx (zpow_pos (by norm_num) _).le
  have hu : 0 < (10 : ℝ) ^ q := zpow_pos (by norm_num) _
  have hs := mul_le_mul_of_nonneg_right (rootRound_towardZero_le s hn hy) hu.le
  rw [realRoot_scaled hn hx] at hs
  cases s <;> simpa only [Bool.false_eq_true, ↓reduceIte, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one,
    abs_mul, abs_neg, abs_one, one_mul, Nat.abs_cast, abs_zpow,
    abs_of_pos (by norm_num : (0 : ℝ) < 10)] using hs

end FloatLib.Floats.Formats.DecimalInterchange
