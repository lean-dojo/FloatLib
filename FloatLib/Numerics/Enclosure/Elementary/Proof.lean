/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Runtime
public import FloatLib.Numerics.Enclosure.Rational.Proof
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Proved exponential and logarithm enclosures

The bounds below describe the output of the rational algorithms, including truncation error.
They use Mathlib's `Real.exp_bound` and `Real.abs_log_sub_add_sum_range_le`.

The exponential reduction is valid for every rational input. The logarithm theorem requires a
positive argument, so a format must handle its own zero and exceptional values before calling it.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure

open RationalInterval

/-- The rational Taylor sum denotes the corresponding real Taylor polynomial. -/
theorem cast_expTaylor (x : ℚ) (n : Nat) :
    (expTaylor x n : ℝ) =
      ∑ i ∈ Finset.range n, (x : ℝ) ^ i / (i.factorial : ℝ) := by
  simp [expTaylor]

/-- The rational error radius is the real Taylor remainder estimate. -/
theorem cast_expRadius (x : ℚ) (n : Nat) :
    (expRadius x n : ℝ) =
      |(x : ℝ)| ^ n * ((n + 1 : Nat) : ℝ) / ((n.factorial : ℝ) * n) := by
  simp [expRadius]

/-- The executable exponential polynomial satisfies its computed absolute-error bound. -/
theorem abs_exp_sub_expTaylor_le (x : ℚ) (degree : Nat) (hx : |x| ≤ 1) :
    |Real.exp (x : ℝ) - (expTaylor x (degree + 1) : ℝ)| ≤
      (expRadius x (degree + 1) : ℝ) := by
  rw [cast_expTaylor, cast_expRadius]
  have hreal : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
  simpa [mul_div_assoc, Nat.succ_eq_add_one] using
    Real.exp_bound hreal (Nat.succ_pos degree)

/-- Taylor truncation and its rational remainder bound enclose the small exponential. -/
theorem contains_expSmall (x : ℚ) (degree : Nat) (hx : |x| ≤ 1) :
    (expSmall x degree).Contains (Real.exp (x : ℝ)) :=
  contains_around (abs_exp_sub_expTaylor_le x degree hx)

/-- Dividing by the executable binary reduction scale puts the argument inside the unit ball. -/
theorem abs_div_expScale_lt_one (x : ℚ) :
    |x / (2 : ℚ) ^ expScale x| < 1 := by
  have hden : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
  have habs : |x| < ((x.num.natAbs / x.den + 1 : Nat) : ℚ) := by
    calc
      |x| = |(x.num : ℚ)| / (x.den : ℚ) := by
        conv_lhs => rw [← x.num_div_den]
        rw [abs_div, abs_of_pos hden]
      _ < ((x.num.natAbs / x.den + 1 : Nat) : ℚ) := by
        apply (div_lt_iff₀ hden).mpr
        simpa [mul_comm] using
          (show (x.num.natAbs : ℚ) <
            ((x.den * (x.num.natAbs / x.den + 1) : Nat) : ℚ) by
              exact_mod_cast Nat.lt_mul_div_succ x.num.natAbs x.den_pos)
  have hpower : ((x.num.natAbs / x.den + 1 : Nat) : ℚ) ≤
      (2 : ℚ) ^ expScale x := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_log2_self (n := x.num.natAbs / x.den)))
  rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ expScale x)]
  exact (div_lt_one (by positivity)).mpr (habs.trans_le hpower)

/-- Binary argument reduction is inverted by the matching power of the exponential. -/
theorem exp_reduced_pow (x : ℚ) :
    Real.exp ((x / 2 ^ expScale x : ℚ) : ℝ) ^ (2 ^ expScale x) =
      Real.exp (x : ℝ) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- Exact repeated squaring restores the exponential after binary argument reduction. -/
theorem contains_exp (x : ℚ) (degree : Nat) :
    (exp x degree).Contains (Real.exp (x : ℝ)) := by
  have hsmall := contains_expSmall (x / 2 ^ expScale x) degree
    (abs_div_expScale_lt_one x).le
  have hresult := contains_squareRepeat hsmall (Real.exp_pos _).le (expScale x)
  have hrestore := exp_reduced_pow x
  simpa only [exp, hrestore] using hresult

/-- The rational logarithm polynomial denotes the real Taylor sum. -/
theorem cast_logOneSubTaylor (x : ℚ) (n : Nat) :
    (logOneSubTaylor x n : ℝ) =
      ∑ i ∈ Finset.range n, (x : ℝ) ^ (i + 1) / ((i + 1 : Nat) : ℝ) := by
  simp [logOneSubTaylor]

/-- The executable logarithm polynomial satisfies its computed absolute-error bound. -/
theorem abs_log_add_logOneSubTaylor_le (x : ℚ) (degree : Nat) (hx : |x| < 1) :
    |Real.log (1 - (x : ℝ)) + (logOneSubTaylor x degree : ℝ)| ≤
      (logOneSubRadius x degree : ℝ) := by
  have hreal : |(x : ℝ)| < 1 := by exact_mod_cast hx
  simpa [cast_logOneSubTaylor, logOneSubRadius, add_comm] using
    Real.abs_log_sub_add_sum_range_le hreal degree

/-- Taylor truncation encloses `log (1 - x)` when `|x| < 1`. -/
theorem contains_logOneSub (x : ℚ) (degree : Nat) (hx : |x| < 1) :
    (logOneSub x degree).Contains (Real.log (1 - (x : ℝ))) := by
  apply contains_around
  simpa using abs_log_add_logOneSubTaylor_le x degree hx

/-- The logarithm change of variable maps a positive input into `(-1, 1)`. -/
theorem abs_log_argument_lt_one (x : ℚ) (hx : 0 < x) :
    |(x - 1) / (x + 1)| < 1 := by
  have hden : 0 < x + 1 := by linarith
  rw [abs_lt]
  constructor
  · apply (lt_div_iff₀ hden).mpr
    linarith
  · apply (div_lt_iff₀ hden).mpr
    linarith

/-- The transformed logarithms reconstruct the original positive argument. -/
theorem log_argument_identity (x : ℚ) (hx : 0 < x) :
    Real.log (1 + (((x - 1) / (x + 1) : ℚ) : ℝ)) -
      Real.log (1 - (((x - 1) / (x + 1) : ℚ) : ℝ)) = Real.log (x : ℝ) := by
  let t : ℚ := (x - 1) / (x + 1)
  have ht : |t| < 1 := abs_log_argument_lt_one x hx
  have hreal : 0 < (x : ℝ) := by exact_mod_cast hx
  have htReal : |(t : ℝ)| < 1 := by exact_mod_cast ht
  have hplus : 0 < 1 + (t : ℝ) := by linarith [(abs_lt.mp htReal).1]
  have hminus : 0 < 1 - (t : ℝ) := by linarith [(abs_lt.mp htReal).2]
  have hquotient : (1 + (t : ℝ)) / (1 - (t : ℝ)) = (x : ℝ) := by
    dsimp [t]
    push_cast
    field_simp
    ring
  change Real.log (1 + (t : ℝ)) - Real.log (1 - (t : ℝ)) = _
  rw [← Real.log_div hplus.ne' hminus.ne', hquotient]

/-- The rational series encloses the exact logarithm of every positive argument. -/
theorem contains_logSeries (x : ℚ) (degree : Nat) (hx : 0 < x) :
    (logSeries x degree).Contains (Real.log (x : ℝ)) := by
  let t : ℚ := (x - 1) / (x + 1)
  have ht : |t| < 1 := abs_log_argument_lt_one x hx
  have hfirst := contains_logOneSub (-t) degree (by simpa using ht)
  have hsecond := contains_logOneSub t degree ht
  have hresult := contains_sub hfirst hsecond
  simpa only [logSeries, t, Rat.cast_neg, sub_neg_eq_add, log_argument_identity x hx] using hresult

/-- Removing the computed power of two puts an argument at least one into `[1, 2)`. -/
theorem div_logScale_bounds (x : ℚ) (hx : 1 ≤ x) :
    1 ≤ x / 2 ^ logScale x ∧ x / 2 ^ logScale x < 2 := by
  have hfloor : (Nat.floor x) ≠ 0 := Nat.ne_of_gt (Nat.floor_pos.mpr hx)
  have hpower : (2 : ℚ) ^ logScale x ≤ x := by
    calc
      _ ≤ (Nat.floor x : ℚ) := by exact_mod_cast Nat.log2_self_le hfloor
      _ ≤ x := Nat.floor_le (by linarith)
  have hnext : x < (2 : ℚ) ^ (logScale x + 1) := by
    calc
      x < (Nat.floor x : ℚ) + 1 := Nat.lt_floor_add_one x
      _ ≤ (2 : ℚ) ^ (logScale x + 1) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.lt_log2_self (n := Nat.floor x))
  constructor
  · exact (one_le_div (by positivity)).mpr hpower
  · apply (div_lt_iff₀ (by positivity)).mpr
    simpa [pow_succ, mul_comm] using hnext

/-- The transformed series argument is uniformly small after binary reduction. -/
theorem log_reduced_argument_bounds (x : ℚ) (hx : 1 ≤ x) :
    let reduced := x / 2 ^ logScale x
    0 ≤ (reduced - 1) / (reduced + 1) ∧
      (reduced - 1) / (reduced + 1) < 1 / 3 := by
  dsimp only
  obtain ⟨hlower, hupper⟩ := div_logScale_bounds x hx
  have hden : 0 < x / 2 ^ logScale x + 1 := by linarith
  constructor
  · exact div_nonneg (by linarith) hden.le
  · apply (div_lt_iff₀ hden).mpr
    linarith

/-- The removed power of two contributes its exact integer multiple of `log 2`. -/
theorem log_reduction_identity (x : ℚ) (hx : 0 < x) :
    Real.log ((x / 2 ^ logScale x : ℚ) : ℝ) +
      (logScale x : ℝ) * Real.log 2 = Real.log (x : ℝ) := by
  have hreal : 0 < (x : ℝ) := by exact_mod_cast hx
  push_cast
  rw [Real.log_div hreal.ne' (by positivity), Real.log_pow]
  ring

/-- Binary argument reduction and reconstruction preserve logarithm containment. -/
theorem contains_logLarge (x : ℚ) (degree : Nat) (hx : 0 < x) :
    (logLarge x degree).Contains (Real.log (x : ℝ)) := by
  have hfirst := contains_logSeries (x / 2 ^ logScale x) degree (by positivity)
  have hsecond := contains_scaleNonnegative
    (contains_logSeries 2 degree (by norm_num))
    (factor := (logScale x : ℚ)) (by positivity)
  simpa only [logLarge, Rat.cast_natCast, Rat.cast_ofNat, log_reduction_identity x hx] using
    contains_add hfirst hsecond

/-- The reduced rational algorithm encloses the exact logarithm of every positive argument. -/
theorem contains_log (x : ℚ) (degree : Nat) (hx : 0 < x) :
    (log x degree).Contains (Real.log (x : ℝ)) := by
  unfold log
  split
  · have h := contains_neg (contains_logLarge x⁻¹ degree (inv_pos.mpr hx))
    simpa only [Rat.cast_inv, Real.log_inv, neg_neg] using h
  · exact contains_logLarge x degree hx

end FloatLib.Numerics.Enclosure
