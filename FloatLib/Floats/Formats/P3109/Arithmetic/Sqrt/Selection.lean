/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Proof
public import FloatLib.Floats.Formats.P3109.Projection.RealSelection

/-!
# Square-root stochastic selection formulas

The executable squared-threshold comparisons implement the floor and RNITE formulas of §4.7.4
on the fractional part of the actual real square root. These equalities include exact roots and
every supplied stochastic word. They make no probability or randomness-quality claim.

Reference: P3109 unapproved interim report 4.0.3, revision `34f5964`, §§4.7.4, 4.10.8.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

/-- Fractional part of the exact real square root, before selecting an integer candidate. -/
noncomputable def sqrtFraction (numerator denominator : Nat) : Real :=
  Real.sqrt ((numerator : Real) / denominator) - sqrtFloor numerator denominator

/-- The square-root fractional part lies in `[0, 1)` for every positive denominator. -/
theorem sqrtFraction_bounds (numerator denominator : Nat) (hd : 0 < denominator) :
    0 ≤ sqrtFraction numerator denominator ∧ sqrtFraction numerator denominator < 1 := by
  have h := sqrtFloor_real_bounds numerator denominator hd
  dsimp only [sqrtFraction]
  constructor <;> linarith

/-- Executable stochastic A is the report's floor formula for the root's exact fractional part. -/
theorem sqrtRoundAway_stochasticA (format : Format) (quantum : Int) (random : RandomBits)
    (numerator denominator : Nat) (hd : 0 < denominator) :
    sqrtRoundAway format (.stochasticA random) quantum numerator denominator
        (sqrtFloor numerator denominator) =
      decide (2 ^ random.width ≤
        ⌊sqrtFraction numerator denominator * 2 ^ random.width⌋₊ + random.toNat) := by
  rw [sqrtRoundAway_eq_real _ _ _ _ _ _ hd]
  have hr := RationalRounding.random_lt_modulus random
  have hroot := (sqrtFloor_real_bounds numerator denominator hd).1
  by_cases he : Real.sqrt ((numerator : Real) / denominator) = sqrtFloor numerator denominator
  · simp [sqrtRoundAwayReal, sqrtRoundDecision, sqrtFraction, he, Nat.not_le.mpr hr]
  · simp only [sqrtRoundAwayReal, sqrtRoundDecision, he, decide_false, Bool.false_eq_true,
      if_false]
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, ne_eq, compare_lt_iff_lt, decide_eq_true_eq, not_lt]
    simpa only [sqrtFraction, Nat.cast_pow, Nat.cast_ofNat] using
      (RealRounding.floor_selection_iff _ _ _ _ (Nat.two_pow_pos _) hr hroot).symm

/-- Executable stochastic B is the report's doubled-word floor formula. -/
theorem sqrtRoundAway_stochasticB (format : Format) (quantum : Int) (random : RandomBits)
    (numerator denominator : Nat) (hd : 0 < denominator) :
    sqrtRoundAway format (.stochasticB random) quantum numerator denominator
        (sqrtFloor numerator denominator) =
      decide (2 ^ (random.width + 1) ≤
        ⌊sqrtFraction numerator denominator * 2 ^ (random.width + 1)⌋₊ +
          (2 * random.toNat + 1)) := by
  rw [sqrtRoundAway_eq_real _ _ _ _ _ _ hd]
  have hr : 2 * random.toNat + 1 < 2 ^ (random.width + 1) := by
    have := RationalRounding.random_lt_modulus random
    rw [pow_succ]
    omega
  have hroot := (sqrtFloor_real_bounds numerator denominator hd).1
  by_cases he : Real.sqrt ((numerator : Real) / denominator) = sqrtFloor numerator denominator
  · simp [sqrtRoundAwayReal, sqrtRoundDecision, sqrtFraction, he, Nat.not_le.mpr hr]
  · simp only [sqrtRoundAwayReal, sqrtRoundDecision, he, decide_false, Bool.false_eq_true,
      if_false]
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, ne_eq, compare_lt_iff_lt, decide_eq_true_eq, not_lt]
    simpa only [sqrtFraction, Nat.cast_pow, Nat.cast_ofNat] using
      (RealRounding.floor_selection_iff _ _ _ _ (Nat.two_pow_pos _) hr hroot).symm

/-- Executable stochastic C is RNITE of the exact fraction, including even upper-boundary ties. -/
theorem sqrtRoundAway_stochasticC (format : Format) (quantum : Int) (random : RandomBits)
    (numerator denominator : Nat) (hd : 0 < denominator) :
    sqrtRoundAway format (.stochasticC random) quantum numerator denominator
        (sqrtFloor numerator denominator) =
      decide (2 ^ random.width ≤
        RealRounding.nearestEven (sqrtFraction numerator denominator * 2 ^ random.width) +
          random.toNat) := by
  rw [sqrtRoundAway_eq_real _ _ _ _ _ _ hd]
  have hr := RationalRounding.random_lt_modulus random
  have hroot := (sqrtFloor_real_bounds numerator denominator hd).1
  by_cases he : Real.sqrt ((numerator : Real) / denominator) = sqrtFloor numerator denominator
  · simp [sqrtRoundAwayReal, sqrtRoundDecision, sqrtFraction, he, Nat.not_le.mpr hr,
      RealRounding.nearestEven]
  · simp only [sqrtRoundAwayReal, sqrtRoundDecision, he, decide_false, Bool.false_eq_true,
      if_false]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, compare_gt_iff_gt,
      compare_eq_iff_eq, decide_eq_true_eq]
    simpa only [sqrtFraction, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
      (RealRounding.nearestEven_selection_iff _ _ _ _ (Nat.two_pow_pos _) hr hroot).symm

end FloatLib.Floats.Formats.P3109.Arithmetic
