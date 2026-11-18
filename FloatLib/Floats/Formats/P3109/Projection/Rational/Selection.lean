/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Rational.Runtime
public import FloatLib.Floats.Formats.P3109.Projection.Formula
public import Mathlib.Data.Rat.Floor

/-!
# Rational meaning of P3109 rounding decisions

The fractional part the report talks about is an exact rational, so natural division gives its
floor, and comparing quotient and remainder gives nearest-even integer rounding. With these facts
every executable rounding decision matches §4.7.4, for each possible supplied stochastic word. We
assume nothing about the distribution or quality of the random bits.

Reference: P3109 unapproved interim report v4.1, 14 September 2026, §4.7.4.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.RationalRounding

/-- Division splits a nonnegative rational into its integer part and exact remainder. -/
theorem div_eq_quotient_add_fraction (numerator denominator : Nat) (hd : 0 < denominator) :
    (numerator : Rat) / denominator =
      (numerator / denominator : Nat) + (numerator % denominator : Nat) / denominator := by
  have hcast : (numerator : Rat) =
      (denominator : Rat) * (numerator / denominator : Nat) + (numerator % denominator : Nat) := by
    exact_mod_cast (Nat.div_add_mod numerator denominator).symm
  have hd' : (denominator : Rat) ≠ 0 := by positivity
  calc
    (numerator : Rat) / denominator =
        ((denominator : Rat) * (numerator / denominator : Nat) +
          (numerator % denominator : Nat)) / denominator :=
            congrArg (fun x : Rat => x / (denominator : Rat)) hcast
    _ = _ := by field_simp

/-- A remainder fraction is below one half if and only if `2 * remainder < denominator`. -/
theorem fraction_lt_half (remainder denominator : Nat) (hd : 0 < denominator) :
    (remainder : Rat) / denominator < 1 / 2 ↔ 2 * remainder < denominator := by
  have hd' : (0 : Rat) < denominator := by exact_mod_cast hd
  rw [div_lt_div_iff₀ hd' (by norm_num : (0 : Rat) < 2)]
  norm_cast
  omega

/-- A remainder fraction is one half if and only if `denominator = 2 * remainder`. -/
theorem fraction_eq_half (remainder denominator : Nat) (hd : 0 < denominator) :
    (remainder : Rat) / denominator = 1 / 2 ↔ denominator = 2 * remainder := by
  have hd' : (denominator : Rat) ≠ 0 := by positivity
  rw [div_eq_div_iff hd' (by norm_num : (2 : Rat) ≠ 0)]
  norm_cast
  omega

/-- Quotient/remainder nearest-even rounding implements the report's mathematical RNITE. -/
theorem roundQuotientEven_eq_nearestEven (numerator denominator : Nat) (hd : 0 < denominator) :
    roundQuotientEven numerator denominator = RoundingFormula.nearestEven ((numerator : Rat) /
      denominator) := by
  have hbelow :
      (numerator : Rat) / denominator < (numerator / denominator : Nat) + 1 / 2 ↔
        2 * (numerator % denominator) < denominator := by
    rw [div_eq_quotient_add_fraction numerator denominator hd, add_lt_add_iff_left]
    exact fraction_lt_half _ _ hd
  have htie :
      (numerator : Rat) / denominator = (numerator / denominator : Nat) + 1 / 2 ↔
        denominator = 2 * (numerator % denominator) := by
    rw [div_eq_quotient_add_fraction numerator denominator hd, add_right_inj]
    exact fraction_eq_half _ _ hd
  simp only [RoundingFormula.nearestEven, Rat.natFloor_natCast_div_natCast, hbelow, htie,
    roundQuotientEven,
    beq_iff_eq]
  split_ifs <;> omega

/-- Binary scaling followed by natural division is the floor of the exact scaled fraction. -/
theorem scaleRationalFractionFloor_eq (remainder denominator bits : Nat) :
    Format.Internal.scaleRationalFractionFloor remainder denominator bits =
      ⌊((remainder : Rat) / denominator) * 2 ^ bits⌋₊ := by
  rw [Format.Internal.scaleRationalFractionFloor, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  rw [div_mul_eq_mul_div]
  norm_cast

/-- The stochastic-C helper computes mathematical nearest-even rounding of the scaled fraction. -/
theorem scaleRationalFractionNearestEven_eq (remainder denominator bits : Nat)
    (hd : 0 < denominator) :
    Format.Internal.scaleRationalFractionNearestEven remainder denominator bits =
      RoundingFormula.nearestEven (((remainder : Rat) / denominator) * 2 ^ bits) := by
  rw [Format.Internal.scaleRationalFractionNearestEven,
    roundQuotientEven_eq_nearestEven _ _ hd, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  congr 1
  push_cast
  ring

/-- Every supplied word is strictly below the modulus specified by its width. -/
theorem random_lt_modulus (random : RandomBits) : random.toNat < 2 ^ random.width :=
  random.bits.isLt

/-- An exact integer is unchanged even by stochastic rounding, for every supplied word. -/
@[simp] theorem roundAway_zero (mode : RoundingMode) (negative lowerEven : Bool) :
    RoundingFormula.roundAway mode negative lowerEven (0 : Rat) = false := by
  cases mode <;>
    simp only [RoundingFormula.roundAway, RoundingFormula.nearestEven, lt_self_iff_false,
      decide_false, Bool.false_and, one_div, inv_nonpos, decide_eq_false_iff_not, not_le,
      Nat.ofNat_pos, inv_neg'', zero_eq_inv, OfNat.zero_ne_ofNat, Bool.or_false, not_lt,
      Nat.ofNat_nonneg, zero_mul, Nat.floor_zero, zero_add, Nat.cast_zero, inv_pos,
      Nat.zero_mod, and_true, or_false, ite_true]
  all_goals
    rename_i random
    have h := random_lt_modulus random
    have hdouble : 2 * random.toNat + 1 < 2 ^ (random.width + 1) := by
      rw [pow_succ]
      omega
    omega

/-- All nine executable decisions agree with the report's exact rational formulas. -/
theorem roundRationalAwayWithParity_eq (mode : RoundingMode) (negative lowerEven : Bool)
    (remainder denominator : Nat) (hd : 0 < denominator) :
    Format.Internal.roundRationalAwayWithParity mode negative lowerEven remainder denominator =
      RoundingFormula.roundAway mode negative lowerEven ((remainder : Rat) / denominator) := by
  by_cases hr : remainder = 0
  · simp [Format.Internal.roundRationalAwayWithParity, hr]
  have hd' : (0 : Rat) < denominator := by exact_mod_cast hd
  have hr' : (0 : Rat) < (remainder : Rat) / denominator := by
    exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hr) hd'
  have hhalf := fraction_eq_half remainder denominator hd
  have hbelow := fraction_lt_half remainder denominator hd
  have habove : 1 / 2 < (remainder : Rat) / denominator ↔
      denominator < 2 * remainder := by
    rw [← not_le, le_iff_lt_or_eq, hbelow, hhalf]
    omega
  have hatleast : 1 / 2 ≤ (remainder : Rat) / denominator ↔
      denominator ≤ 2 * remainder := by
    rw [← not_lt, hbelow]
    omega
  simp only [one_div] at habove hatleast hhalf
  cases mode <;>
    simp [Format.Internal.roundRationalAwayWithParity, RoundingFormula.roundAway, hr, hr',
      habove, hatleast,
      hhalf, scaleRationalFractionFloor_eq, scaleRationalFractionNearestEven_eq _ _ _ hd]
  rfl

end FloatLib.Floats.Formats.P3109.RationalRounding
