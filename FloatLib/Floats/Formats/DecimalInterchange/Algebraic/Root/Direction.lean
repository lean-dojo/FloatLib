/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Root.Proof

/-!
# Directed rounding of signed integer-degree roots

Upward and downward coefficient rounding exchange roles for negative results.
The resulting signed datum bounds the exact signed real root.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

theorem le_rootMagnitude_towardPositive (f : Format) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (rootMagnitude f .towardPositive s degree x preferred).status.overflow = false) :
    ∃ value : ℚ,
      (rootMagnitude f .towardPositive s degree x preferred).value.toRat? = some value ∧
        (if s then -1 else 1) * realRoot degree (x : ℝ) ≤ (value : ℝ) := by
  have hq := rootMagnitude_quantum_le_of_no_overflow f .towardPositive
    s degree x preferred hfinite
  refine ⟨_, rootMagnitude_value f .towardPositive s degree x preferred hq, ?_⟩
  let q := rootQuantum f degree x
  let y := x / (10 : ℚ) ^ ((degree : Int) * q)
  have hy : 0 ≤ y := div_nonneg hx (zpow_pos (by norm_num) _).le
  have hu : 0 < (10 : ℝ) ^ q := zpow_pos (by norm_num) _
  have hg : (if s then -1 else 1) * realRoot degree (y : ℝ) ≤
      (if s then -1 else 1) * (RoundingMode.towardPositive.rootRound s degree y : ℝ) := by
    cases s
    · simpa only [Bool.false_eq_true, ↓reduceIte, one_mul] using
        le_rootRound_directed_up false hn hy
    · simpa only [↓reduceIte, neg_one_mul] using
        neg_le_neg (rootRound_directed_down_le true hn hy)
  have hs := mul_le_mul_of_nonneg_right hg hu.le
  rw [mul_assoc, realRoot_scaled hn hx] at hs
  cases s <;> simpa only [Bool.false_eq_true, ↓reduceIte, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using hs

theorem rootMagnitude_towardNegative_le (f : Format) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (rootMagnitude f .towardNegative s degree x preferred).status.overflow = false) :
    ∃ value : ℚ,
      (rootMagnitude f .towardNegative s degree x preferred).value.toRat? = some value ∧
        (value : ℝ) ≤ (if s then -1 else 1) * realRoot degree (x : ℝ) := by
  have hq := rootMagnitude_quantum_le_of_no_overflow f .towardNegative
    s degree x preferred hfinite
  refine ⟨_, rootMagnitude_value f .towardNegative s degree x preferred hq, ?_⟩
  let q := rootQuantum f degree x
  let y := x / (10 : ℚ) ^ ((degree : Int) * q)
  have hy : 0 ≤ y := div_nonneg hx (zpow_pos (by norm_num) _).le
  have hu : 0 < (10 : ℝ) ^ q := zpow_pos (by norm_num) _
  have hg : (if s then -1 else 1) *
        (RoundingMode.towardNegative.rootRound s degree y : ℝ) ≤
      (if s then -1 else 1) * realRoot degree (y : ℝ) := by
    cases s
    · simpa only [Bool.false_eq_true, ↓reduceIte, one_mul] using
        rootRound_directed_down_le false hn hy
    · simpa only [↓reduceIte, neg_one_mul] using
        neg_le_neg (le_rootRound_directed_up true hn hy)
  have hs := mul_le_mul_of_nonneg_right hg hu.le
  rw [mul_assoc, mul_assoc, realRoot_scaled hn hx] at hs
  cases s <;> simpa only [Bool.false_eq_true, ↓reduceIte, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one,
    mul_assoc] using hs

theorem abs_rootMagnitude_towardZero_le (f : Format) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (rootMagnitude f .towardZero s degree x preferred).status.overflow = false) :
    ∃ value : ℚ,
      (rootMagnitude f .towardZero s degree x preferred).value.toRat? = some value ∧
        |(value : ℝ)| ≤ realRoot degree (x : ℝ) := by
  have hq := rootMagnitude_quantum_le_of_no_overflow f .towardZero
    s degree x preferred hfinite
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
