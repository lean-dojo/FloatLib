/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Proof
public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Selection

/-!
# Square-root stochastic selection formulas

Stochastic rounding of a square root needs the fractional part of the real root, which may be
irrational. The executable squared-threshold comparisons implement the floor and RNITE formulas of
§4.7.4 on that fractional part, for exact roots too and for every supplied stochastic word. These
equalities say nothing about probability or the quality of the random bits.

Reference: P3109 unapproved interim report v4.1, 14 September 2026, §§4.7.4, 4.10.8.
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
  exact ⟨sub_nonneg.mpr h.1, (sub_lt_iff_lt_add').mpr h.2⟩

/-- Executable stochastic A is the report's floor formula for the root's exact fractional part. -/
theorem sqrtRoundAway_stochasticA (format : Format) (quantum : Int) (random : RandomBits)
    (numerator denominator : Nat) (hd : 0 < denominator) :
    sqrtRoundAway format (.stochasticA random) quantum numerator denominator
        (sqrtFloor numerator denominator) =
      decide (2 ^ random.width ≤
        ⌊sqrtFraction numerator denominator * 2 ^ random.width⌋₊ + random.toNat) := by
  rw [sqrtRoundAway_eq_real _ _ _ _ _ _ hd]
  exact format.roundMagnitudeUp_stochasticA quantum random _ _
    (sqrtFloor_real_bounds numerator denominator hd).1

/-- Executable stochastic B is the report's doubled-word floor formula. -/
theorem sqrtRoundAway_stochasticB (format : Format) (quantum : Int) (random : RandomBits)
    (numerator denominator : Nat) (hd : 0 < denominator) :
    sqrtRoundAway format (.stochasticB random) quantum numerator denominator
        (sqrtFloor numerator denominator) =
      decide (2 ^ (random.width + 1) ≤
        ⌊sqrtFraction numerator denominator * 2 ^ (random.width + 1)⌋₊ +
          (2 * random.toNat + 1)) := by
  rw [sqrtRoundAway_eq_real _ _ _ _ _ _ hd]
  exact format.roundMagnitudeUp_stochasticB quantum random _ _
    (sqrtFloor_real_bounds numerator denominator hd).1

/-- Executable stochastic C is RNITE of the exact fraction, including even upper-boundary ties. -/
theorem sqrtRoundAway_stochasticC (format : Format) (quantum : Int) (random : RandomBits)
    (numerator denominator : Nat) (hd : 0 < denominator) :
    sqrtRoundAway format (.stochasticC random) quantum numerator denominator
        (sqrtFloor numerator denominator) =
      decide (2 ^ random.width ≤
        RoundingFormula.nearestEven (sqrtFraction numerator denominator * 2 ^ random.width) +
          random.toNat) := by
  rw [sqrtRoundAway_eq_real _ _ _ _ _ _ hd]
  exact format.roundMagnitudeUp_stochasticC quantum random _ _
    (sqrtFloor_real_bounds numerator denominator hd).1

end FloatLib.Floats.Formats.P3109.Arithmetic
