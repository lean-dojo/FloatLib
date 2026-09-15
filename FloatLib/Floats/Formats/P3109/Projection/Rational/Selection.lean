/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Rational.Runtime
public import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

/-!
# Rational meaning of P3109 rounding decisions

The report's fractional part is an exact rational. Natural division implements its floor, and
quotient/remainder comparisons implement nearest-even integer rounding. These facts identify
every executable rounding decision with §4.7.4, including each possible supplied stochastic word.
No distribution or randomness-quality assumption is made.

Reference: P3109 unapproved interim report 4.0.3, revision `34f5964`, §4.7.4.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.RationalRounding

/-- Nearest integer to a nonnegative rational, with ties sent to the even integer. -/
def nearestEven (value : Rat) : Nat :=
  let lower : Nat := ⌊value⌋₊
  if value < lower + 1 / 2 ∨ (value = lower + 1 / 2 ∧ lower % 2 = 0) then lower
  else lower + 1

/-- The report's rounding decision in terms of the exact fractional part. -/
def roundAway (mode : RoundingMode) (negative lowerEven : Bool) (fraction : Rat) : Bool :=
  match mode with
  | .towardZero => false
  | .towardPositive => decide (0 < fraction) && !negative
  | .towardNegative => decide (0 < fraction) && negative
  | .nearestTiesToAway => decide (1 / 2 ≤ fraction)
  | .nearestTiesToEven =>
      decide (1 / 2 < fraction) || (decide (fraction = 1 / 2) && !lowerEven)
  | .toOdd => decide (0 < fraction) && lowerEven
  | .stochasticA random =>
      decide (2 ^ random.width ≤ ⌊fraction * 2 ^ random.width⌋₊ + random.toNat)
  | .stochasticB random =>
      decide (2 ^ (random.width + 1) ≤
        ⌊fraction * 2 ^ (random.width + 1)⌋₊ + (2 * random.toNat + 1))
  | .stochasticC random =>
      decide (2 ^ random.width ≤ nearestEven (fraction * 2 ^ random.width) + random.toNat)

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

/-- The exact remainder fraction is below one half precisely under the integer comparison. -/
theorem fraction_lt_half (remainder denominator : Nat) (hd : 0 < denominator) :
    (remainder : Rat) / denominator < 1 / 2 ↔ 2 * remainder < denominator := by
  have hd' : (0 : Rat) < denominator := by exact_mod_cast hd
  rw [div_lt_div_iff₀ hd' (by norm_num : (0 : Rat) < 2)]
  norm_cast
  omega

/-- Equality at a halfway point is an exact integer equality. -/
theorem fraction_eq_half (remainder denominator : Nat) (hd : 0 < denominator) :
    (remainder : Rat) / denominator = 1 / 2 ↔ denominator = 2 * remainder := by
  have hd' : (denominator : Rat) ≠ 0 := by positivity
  rw [div_eq_div_iff hd' (by norm_num : (2 : Rat) ≠ 0)]
  norm_cast
  omega

/-- Quotient/remainder nearest-even rounding implements the report's mathematical RNITE. -/
theorem roundQuotientEven_eq_nearestEven (numerator denominator : Nat) (hd : 0 < denominator) :
    roundQuotientEven numerator denominator = nearestEven ((numerator : Rat) / denominator) := by
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
  simp only [nearestEven, Rat.natFloor_natCast_div_natCast, hbelow, htie, roundQuotientEven,
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
      nearestEven (((remainder : Rat) / denominator) * 2 ^ bits) := by
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
    roundAway mode negative lowerEven 0 = false := by
  cases mode <;> simp [roundAway, nearestEven]
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
      roundAway mode negative lowerEven ((remainder : Rat) / denominator) := by
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
    simp [Format.Internal.roundRationalAwayWithParity, roundAway, hr, hr', habove, hatleast,
      hhalf, scaleRationalFractionFloor_eq, scaleRationalFractionNearestEven_eq _ _ _ hd]
  rfl

end FloatLib.Floats.Formats.P3109.RationalRounding
