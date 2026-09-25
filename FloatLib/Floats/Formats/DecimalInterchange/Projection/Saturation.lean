/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Proof

/-!
# Saturated projection and exponent clamping

At or above `10^(maxQuantum + precision)` every magnitude overflows, and the outcome depends only
on the rounding direction and sign. Strictly between zero and half the least quantum, every
magnitude rounds on the least-quantum grid to the same coefficient, with inexact and underflow.
These two facts show that `projectScaled` computes the same outcome as projecting the unclamped
magnitude.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Every magnitude at or above `10^(maxQuantum + precision)` delivers the overflow outcome. -/
theorem projectMagnitude_of_overflow (f : Format) (mode : RoundingMode) (s : Bool) {x : ℚ}
    (hx : (10 : ℚ) ^ (f.maxQuantum + (f.precision : Int)) ≤ x) (preferred : Int) :
    projectMagnitude f mode s x preferred =
      { value := if mode.overflowToInfinity s then .infinity s else f.maxFinite s
        status := { overflow := true, inexact := true } } := by
  have hx0 : 0 ≤ x := le_trans (zpow_pos (by norm_num) _).le hx
  have hq : f.maxQuantum < roundingQuantum f x := by
    by_contra h
    push Not at h
    have hlt := div_roundingQuantum_lt f hx0
    have hu : 0 < (10 : ℚ) ^ (roundingQuantum f x) := zpow_pos (by norm_num) _
    rw [div_lt_iff₀ hu, Format.coefficientBound_eq] at hlt
    push_cast at hlt
    have hle : (10 : ℚ) ^ f.precision * (10 : ℚ) ^ (roundingQuantum f x) ≤
        (10 : ℚ) ^ (f.maxQuantum + (f.precision : Int)) := by
      rw [add_comm, zpow_add₀ (by norm_num), zpow_natCast]
      exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) h) (by positivity)
    linarith
  have h2 : f.maxQuantum < (roundedPair f mode s x).2 := by
    unfold roundedPair
    exact lt_of_lt_of_le hq (f.le_carry_quantum _ _)
  rw [projectMagnitude_eq]
  simp only [h2, ↓reduceIte]

/-- Below one half, each rounding direction rounds a positive rational to the same integer. -/
theorem roundMagnitude_eq_of_pos_of_lt_half (mode : RoundingMode) (s : Bool) {y : ℚ}
    (hy0 : 0 < y) (hy : y < 1 / 2) :
    mode.roundMagnitude s y = mode.roundMagnitude s (1 / 4) := by
  have hf : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
  have hf' : ⌊(1 / 4 : ℚ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num)
  have h1 : ¬ (1 < 2 * y) := by linarith
  have h2 : ¬ (2 * y = 1) := by intro h; linarith
  have h3 : ¬ (1 ≤ 2 * y) := by linarith
  rw [RoundingMode.roundMagnitude_eq, RoundingMode.roundMagnitude_eq]
  simp only [hf, hf', Nat.cast_zero, sub_zero]
  cases mode <;> cases s <;> norm_num [RoundingMode.increment, h1, h2, h3, hy0]

/--
Every magnitude strictly between zero and half the least quantum rounds to the least quantum,
with the coefficient chosen by the rounding direction alone, and signals inexact and underflow.
-/
theorem projectMagnitude_of_tiny (f : Format) (mode : RoundingMode) (s : Bool) {x : ℚ}
    (hx0 : 0 < x) (hx : x < (10 : ℚ) ^ f.minQuantum / 2) (preferred : Int) :
    projectMagnitude f mode s x preferred =
      { value := .finite s (mode.roundMagnitude s (1 / 4)) f.minQuantum
        status := { inexact := true, underflow := true } } := by
  have hu : 0 < (10 : ℚ) ^ f.minQuantum := zpow_pos (by norm_num) _
  have hcb : (1 : ℚ) < f.coefficientBound := by exact_mod_cast f.one_lt_coefficientBound
  have hq : roundingQuantum f x = f.minQuantum := by
    apply le_antisymm _ (roundingQuantum_ge_min f x)
    apply roundingQuantum_le f hx0.le le_rfl
    nlinarith
  have hy0 : 0 < x / (10 : ℚ) ^ f.minQuantum := div_pos hx0 hu
  have hy : x / (10 : ℚ) ^ f.minQuantum < 1 / 2 := by
    rw [div_lt_iff₀ hu]
    linarith
  have hc : mode.roundAt s x f.minQuantum = mode.roundMagnitude s (1 / 4) :=
    roundMagnitude_eq_of_pos_of_lt_half mode s hy0 hy
  have hc1 : mode.roundMagnitude s (1 / 4) ≤ 1 := by
    have := mode.roundMagnitude_le_floor_add_one s (1 / 4)
    rwa [Nat.floor_eq_zero.mpr (by norm_num : (1 / 4 : ℚ) < 1)] at this
  have hne : mode.roundMagnitude s (1 / 4) ≠ f.coefficientBound := by
    have := f.one_lt_coefficientBound
    omega
  have hpair : roundedPair f mode s x = (mode.roundMagnitude s (1 / 4), f.minQuantum) := by
    show Numerics.RadixText.carry 10 ⟨f.precision, f.precision_pos⟩
      (mode.roundAt s x (roundingQuantum f x)) (roundingQuantum f x) = _
    rw [hq, hc, f.carry_eq]
    simp only [hne, ↓reduceIte]
  have hinexact : ((mode.roundMagnitude s (1 / 4) : Nat) : ℚ) * (10 : ℚ) ^ f.minQuantum ≠ x := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with h | h <;> rw [h]
    · simp only [Nat.cast_zero, zero_mul]
      exact hx0.ne
    · simp only [Nat.cast_one, one_mul]
      intro h'
      linarith
  have hunder : x < f.minNormal := by
    unfold Format.minNormal
    have : (1 : ℚ) ≤ (10 : ℚ) ^ (f.precision - 1) := one_le_pow₀ (by norm_num)
    nlinarith
  rw [projectMagnitude_eq, hpair]
  simp only [not_lt.mpr f.minQuantum_le_maxQuantum, ↓reduceIte, hinexact, hunder, ne_eq,
    not_false_eq_true, decide_true, Bool.and_true]

private theorem pow_le_scaled (c : Nat) (hc : c ≠ 0) {h e : Int} (he : h ≤ e) :
    (10 : ℚ) ^ h ≤ (c : ℚ) * (10 : ℚ) ^ e := by
  have h1 : (1 : ℚ) ≤ c := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
  calc (10 : ℚ) ^ h ≤ (10 : ℚ) ^ e := zpow_le_zpow_right₀ (by norm_num) he
    _ = 1 * (10 : ℚ) ^ e := (one_mul _).symm
    _ ≤ (c : ℚ) * (10 : ℚ) ^ e := mul_le_mul_of_nonneg_right h1 (zpow_pos (by norm_num) _).le

private theorem scaled_lt_half (m : Int) (c : Nat) (hc : c ≠ 0) {e : Int}
    (he : e ≤ m - (c.log2 : Int) - 2) :
    0 < (c : ℚ) * (10 : ℚ) ^ e ∧ (c : ℚ) * (10 : ℚ) ^ e < (10 : ℚ) ^ m / 2 := by
  have hcpos : (0 : ℚ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
  refine ⟨mul_pos hcpos (zpow_pos (by norm_num) _), ?_⟩
  have hc2 : (c : ℚ) < (10 : ℚ) ^ (c.log2 + 1) := by
    have h := (Nat.lt_log2_self (n := c))
    have h' : 2 ^ (c.log2 + 1) ≤ 10 ^ (c.log2 + 1) := Nat.pow_le_pow_left (by norm_num) _
    exact_mod_cast lt_of_lt_of_le h h'
  have hpow : (10 : ℚ) ^ (c.log2 + 1) * (10 : ℚ) ^ e ≤ (10 : ℚ) ^ (m - 1) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    apply zpow_le_zpow_right₀ (by norm_num)
    push_cast
    omega
  have hm : (10 : ℚ) ^ (m - 1) = (10 : ℚ) ^ m / 10 := by
    rw [zpow_sub₀ (by norm_num), zpow_one]
  have hu : 0 < (10 : ℚ) ^ m := zpow_pos (by norm_num) _
  have he' : 0 < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
  calc (c : ℚ) * (10 : ℚ) ^ e < (10 : ℚ) ^ (c.log2 + 1) * (10 : ℚ) ^ e :=
        mul_lt_mul_of_pos_right hc2 he'
    _ ≤ (10 : ℚ) ^ m / 10 := hm ▸ hpow
    _ < (10 : ℚ) ^ m / 2 := by linarith

/-- Clamping the exponent never changes a scaled projection. -/
theorem projectScaled_eq (f : Format) (mode : RoundingMode) (negative : Bool) (coefficient : Nat)
    (exponent preferred : Int) :
    projectScaled f mode negative coefficient exponent preferred =
      projectMagnitude f mode negative ((coefficient : ℚ) * (10 : ℚ) ^ exponent) preferred := by
  unfold projectScaled clampScaledExponent
  by_cases hc : coefficient = 0
  · subst hc
    simp
  · simp only [hc, ↓reduceIte]
    have hmin := f.minQuantum_le_maxQuantum
    by_cases hhi : f.maxQuantum + (f.precision : Int) < exponent
    · rw [min_eq_left hhi.le, max_eq_right (by omega),
        projectMagnitude_of_overflow f mode negative (pow_le_scaled _ hc le_rfl),
        projectMagnitude_of_overflow f mode negative (pow_le_scaled _ hc hhi.le)]
    · by_cases hlo : exponent < f.minQuantum - (coefficient.log2 : Int) - 2
      · rw [min_eq_right (by omega), max_eq_left hlo.le]
        obtain ⟨h₁, h₂⟩ := scaled_lt_half f.minQuantum coefficient hc
          (le_refl (f.minQuantum - (coefficient.log2 : Int) - 2))
        obtain ⟨h₃, h₄⟩ := scaled_lt_half f.minQuantum coefficient hc hlo.le
        rw [projectMagnitude_of_tiny f mode negative h₁ h₂,
          projectMagnitude_of_tiny f mode negative h₃ h₄]
      · rw [min_eq_right (not_lt.mp hhi), max_eq_right (not_lt.mp hlo)]

end FloatLib.Floats.Formats.DecimalInterchange
