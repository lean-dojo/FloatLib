/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Digits
public import FloatLib.Numerics.Exact.RadixText.PrecisionProof
public import FloatLib.Numerics.Exact.DecimalText.PrecisionProof
public import FloatLib.Numerics.Exact.HexText.Proof

/-! # Requested-precision guarantees for binary character output

The integer rounder is independent of the external radix and the binary
descriptor. The shared radix laws then give coefficient bounds, fixed points
and the numerical interpretation of the emitted characters.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

/-- Every output rounding direction fixes a nonnegative integer. -/
@[simp] theorem roundTextMagnitude_natCast (mode : IEEERoundingMode)
    (negative : Bool) (n : Nat) :
    roundTextMagnitude mode negative (n : Rat) = n := by
  have h := roundRatEven_intCast (n : Int)
  simp only [Int.cast_natCast] at h
  cases mode <;> cases negative <;> simp [roundTextMagnitude, h]

/-- Nearest-even integer output has error at most one half on a nonnegative magnitude. -/
theorem roundTextMagnitude_nearest_error (negative : Bool) (x : Rat) (hx : 0 ≤ x) :
    |(roundTextMagnitude .nearest negative x : Rat) - x| ≤ 1 / 2 := by
  have hn : 0 ≤ roundRatEven x := by
    simp [roundRatEven, not_lt.mpr (Rat.num_nonneg.mpr hx)]
  have hcast : ((roundRatEven x).natAbs : Rat) = (roundRatEven x : Rat) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun n : Int => (n : Rat)) (Int.natAbs_of_nonneg hn)
  simpa only [roundTextMagnitude, hcast] using roundRatEven_error_le_half x

/--
Nearest-away integer output of a nonnegative magnitude exceeds a natural bound exactly when the
magnitude reaches the bound plus one half.
-/
theorem lt_roundTextMagnitude_nearestAway_iff (negative : Bool) (x : Rat) (hx : 0 ≤ x)
    (bound : Nat) :
    bound < roundTextMagnitude .nearestAway negative x ↔ (bound : Rat) + 1 / 2 ≤ x := by
  simp only [roundTextMagnitude]
  rw [lt_roundQuotient_nearestAway_iff _ _ _ x.den_nz]
  have hden : (0 : Rat) < (x.den : Rat) := by exact_mod_cast x.den_pos
  have hvalue : ((x.num.natAbs : Nat) : Rat) / (x.den : Rat) = x := by
    rw [Nat.cast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hx), Rat.num_div_den]
  constructor
  · intro h
    have hcast : (((2 * bound + 1) * x.den : Nat) : Rat) ≤ ((2 * x.num.natAbs : Nat) : Rat) := by
      exact_mod_cast h
    push_cast at hcast
    rw [← hvalue, le_div_iff₀ hden]
    linarith
  · intro h
    rw [← hvalue, le_div_iff₀ hden] at h
    have hcast : (((2 * bound + 1) * x.den : Nat) : Rat) ≤ ((2 * x.num.natAbs : Nat) : Rat) := by
      push_cast
      linarith
    exact_mod_cast hcast

/-- An external magnitude rounder never falls below floor. -/
theorem floor_le_roundTextMagnitude (mode : IEEERoundingMode)
    (negative : Bool) (x : Rat) :
    ⌊x⌋₊ ≤ roundTextMagnitude mode negative x := by
  cases mode with
  | nearest =>
      by_cases hx : 0 ≤ x
      · have he := (abs_le.mp (roundTextMagnitude_nearest_error negative x hx)).1
        by_contra hn
        have hn' : (roundTextMagnitude .nearest negative x : Rat) + 1 ≤ (⌊x⌋₊ : Rat) := by
          exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
        have hf := Nat.floor_le hx
        linarith
      · simp [Nat.floor_eq_zero.mpr (by linarith : x < 1)]
  | nearestAway =>
      by_cases hx : 0 ≤ x
      · have hbelow := (lt_roundTextMagnitude_nearestAway_iff negative x hx
          (roundTextMagnitude .nearestAway negative x)).not.mp (lt_irrefl _)
        by_contra hn
        have hn' : (roundTextMagnitude .nearestAway negative x : Rat) + 1 ≤ (⌊x⌋₊ : Rat) := by
          exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
        have hf := Nat.floor_le hx
        linarith
      · simp [Nat.floor_eq_zero.mpr (by linarith : x < 1)]
  | towardZero => exact le_rfl
  | up => cases negative <;> simp [roundTextMagnitude, Nat.floor_le_ceil]
  | down => cases negative <;> simp [roundTextMagnitude, Nat.floor_le_ceil]
  | away => exact Nat.floor_le_ceil x

/-- An integer upper bound on a magnitude also bounds its rounded coefficient. -/
theorem roundTextMagnitude_le_nat (mode : IEEERoundingMode)
    (negative : Bool) (x : Rat) (n : Nat) (hx : 0 ≤ x) (hn : x ≤ (n : Rat)) :
    roundTextMagnitude mode negative x ≤ n := by
  have hf : ⌊x⌋₊ ≤ n := by exact_mod_cast (Nat.floor_le hx).trans hn
  have hc : ⌈x⌉₊ ≤ n := Nat.ceil_le.mpr hn
  cases mode with
  | nearest =>
      have he := (abs_le.mp (roundTextMagnitude_nearest_error negative x hx)).2
      by_contra h
      have h' : (n : Rat) + 1 ≤ (roundTextMagnitude .nearest negative x : Rat) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
      linarith
  | nearestAway =>
      by_contra h
      have habove := (lt_roundTextMagnitude_nearestAway_iff negative x hx n).mp
        (Nat.lt_of_not_ge h)
      linarith
  | towardZero => exact hf
  | up => cases negative <;> assumption
  | down => cases negative <;> assumption
  | away => exact hc

/-- Requested decimal output has exactly the requested digit count for nonzero inputs. -/
theorem significantDecimal_coefficient_bounds (mode : IEEERoundingMode)
    (value : DecimalText.Decimal) (digits : ℕ+) (hc : value.significand ≠ 0) :
    10 ^ ((digits : Nat) - 1) ≤
      (DecimalText.significantDecimal (roundTextMagnitude mode) value digits).significand ∧
      (DecimalText.significantDecimal (roundTextMagnitude mode) value digits).significand <
        10 ^ (digits : Nat) :=
  RadixText.significant_coefficient_bounds 10 (by decide) (roundTextMagnitude mode)
    (floor_le_roundTextMagnitude mode) (roundTextMagnitude_le_nat mode)
    value.negative value.significand value.exponent digits hc

/-- Enough decimal digits preserve the exact value, for any binary descriptor and direction. -/
theorem significantDecimal_exact (mode : IEEERoundingMode) (value : DecimalText.Decimal)
    (digits : ℕ+) (hc : value.significand < 10 ^ (digits : Nat)) :
    (DecimalText.significantDecimal (roundTextMagnitude mode) value digits).toRat = value.toRat := by
  have h := RadixText.significant_exact 10 (by decide) (roundTextMagnitude mode)
    (roundTextMagnitude_natCast mode) value.negative value.significand value.exponent digits hc
  have hs := DecimalText.significantDecimal_negative (roundTextMagnitude mode) value digits
  cases hv : value.negative
  · simpa [DecimalText.Decimal.toRat, hs, hv, DecimalText.significantDecimal,
      DecimalText.carryDecimal, DecimalText.roundDecimal, RadixText.significant,
      DecimalText.significantQuantum] using h
  · simpa [DecimalText.Decimal.toRat, hs, hv, DecimalText.significantDecimal,
      DecimalText.carryDecimal, DecimalText.roundDecimal, RadixText.significant,
      DecimalText.significantQuantum] using congrArg Neg.neg h

/-- Decimal precision output parses to the grid-rounded value. -/
theorem parse_formatDyadicText_significant_decimal (mode : IEEERoundingMode)
    (value : Numerics.Dyadic) (digits : ℕ+) :
    DecimalText.parse (formatDyadicText mode .decimal (.significant digits) value).text =
      some (DecimalText.significantDecimal (roundTextMagnitude mode)
        (DecimalText.ofDyadic value) digits).toRat := by
  simp [formatDyadicText]

/-- Hexadecimal precision output parses to the complete rounded dyadic, including signed zero. -/
theorem parse_formatDyadicText_significant_hexadecimal (mode : IEEERoundingMode)
    (value : Numerics.Dyadic) (digits : ℕ+) :
    HexText.parse (formatDyadicText mode .hexadecimal (.significant digits) value).text =
      some (HexText.significant (roundTextMagnitude mode) value digits) := by
  simp [formatDyadicText]

/-- Decimal output raises inexact exactly when its numerical value changes. -/
theorem formatDyadicText_decimal_inexact_iff (mode : IEEERoundingMode)
    (value : Numerics.Dyadic) (digits : ℕ+) :
    (formatDyadicText mode .decimal (.significant digits) value).status.inexact = true ↔
      (DecimalText.significantDecimal (roundTextMagnitude mode)
        (DecimalText.ofDyadic value) digits).toRat ≠ value.toRat := by
  simp [formatDyadicText]

/-- Hexadecimal output raises inexact exactly when its numerical value changes. -/
theorem formatDyadicText_hexadecimal_inexact_iff (mode : IEEERoundingMode)
    (value : Numerics.Dyadic) (digits : ℕ+) :
    (formatDyadicText mode .hexadecimal (.significant digits) value).status.inexact = true ↔
      (HexText.significant (roundTextMagnitude mode) value digits).toRat ≠ value.toRat := by
  simp [formatDyadicText]

/-- At a halfway integer, the common output rounder selects the even neighbor. -/
theorem roundTextMagnitude_nearest_midpoint (negative : Bool) (n : Nat) :
    roundTextMagnitude .nearest negative ((n : Rat) + 1 / 2) =
      if n % 2 = 0 then n else n + 1 := by
  have h := roundRatEven_half_step (n : Int)
  simp only [Int.cast_natCast] at h
  simp only [roundTextMagnitude, h]
  split <;> split <;> simp_all <;> omega

/-- The same half-grid error guarantee holds in any external radix greater than one. -/
theorem significantMagnitude_nearest_error (radix : Nat) (hradix : 1 < radix)
    (negative : Bool) (coefficient : Nat) (quantum : Int) (digits : ℕ+) :
    |((RadixText.significant radix (roundTextMagnitude .nearest) negative
        coefficient quantum digits).1 : Rat) *
        (radix : Rat) ^ (RadixText.significant radix (roundTextMagnitude .nearest)
          negative coefficient quantum digits).2 -
      (coefficient : Rat) * (radix : Rat) ^ quantum| ≤
        (radix : Rat) ^ RadixText.significantQuantum radix coefficient quantum digits / 2 := by
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    RadixText.significant_error radix (Nat.zero_lt_of_lt hradix)
      (roundTextMagnitude .nearest) (1 / 2)
      roundTextMagnitude_nearest_error negative coefficient quantum digits

/-- Nearest-even decimal output has at most half a requested decimal grid unit of error. -/
theorem significantDecimal_nearest_error (value : DecimalText.Decimal) (digits : ℕ+) :
    |(DecimalText.significantDecimal (roundTextMagnitude .nearest) value digits).toRat -
        value.toRat| ≤
      (10 : Rat) ^ DecimalText.significantQuantum value.significand value.exponent digits / 2 := by
  have h := significantMagnitude_nearest_error 10 (by decide) value.negative
    value.significand value.exponent digits
  cases hs : value.negative <;>
    simpa [DecimalText.Decimal.toRat, DecimalText.significantDecimal,
      DecimalText.carryDecimal, DecimalText.roundDecimal, DecimalText.significantQuantum,
      RadixText.significant, hs, neg_mul, neg_sub_neg, neg_add_eq_sub, abs_sub_comm] using h

/-- Nearest-even hexadecimal output has at most half a requested hexadecimal grid unit of error. -/
theorem significantHex_nearest_error (value : Numerics.Dyadic) (digits : ℕ+) :
    |(HexText.significant (roundTextMagnitude .nearest) value digits).toRat - value.toRat| ≤
      (16 : Rat) ^ RadixText.significantQuantum 16 (HexText.radixPair value).1
        (HexText.radixPair value).2 digits / 2 := by
  have h := significantMagnitude_nearest_error 16 (by decide) value.negative
    (HexText.radixPair value).1 (HexText.radixPair value).2 digits
  simp only [Nat.cast_ofNat] at h
  rw [HexText.radixPair_value] at h
  cases hs : value.negative <;>
    simpa [HexText.significant, Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand,
      hs, ← HexText.sixteen_zpow, neg_mul, neg_sub_neg, neg_add_eq_sub, abs_sub_comm] using h

/-- Requested hexadecimal output has exactly the requested digit count for nonzero input. -/
theorem significantHex_coefficient_bounds (mode : IEEERoundingMode)
    (value : Numerics.Dyadic) (digits : ℕ+) (hc : value.significand ≠ 0) :
    16 ^ ((digits : Nat) - 1) ≤
      (HexText.significant (roundTextMagnitude mode) value digits).significand ∧
      (HexText.significant (roundTextMagnitude mode) value digits).significand <
        16 ^ (digits : Nat) := by
  apply RadixText.significant_coefficient_bounds 16 (by decide) (roundTextMagnitude mode)
    (floor_le_roundTextMagnitude mode) (roundTextMagnitude_le_nat mode)
  exact Nat.mul_ne_zero hc (Nat.two_pow_pos _).ne'

private theorem directedTextBounds (negative : Bool) (magnitude unit : Rat)
    (hmagnitude : 0 ≤ magnitude) (hunit : 0 < unit) :
    let signed := (if negative then (-1 : Rat) else 1) * magnitude
    let rounded := fun mode => (if negative then (-1 : Rat) else 1) *
      (roundTextMagnitude mode negative (magnitude / unit) : Rat) * unit
    signed ≤ rounded .up ∧
      rounded .down ≤ signed ∧
      |rounded .towardZero| ≤ |signed| := by
  dsimp only
  have hx : 0 ≤ magnitude / unit := div_nonneg hmagnitude hunit.le
  have hf := mul_le_mul_of_nonneg_right (Nat.floor_le hx) hunit.le
  have hc := mul_le_mul_of_nonneg_right (Nat.le_ceil (magnitude / unit)) hunit.le
  rw [div_mul_cancel₀ _ hunit.ne'] at hf hc
  have hfloor : (0 : Rat) ≤ (⌊magnitude / unit⌋₊ : Rat) * unit :=
    mul_nonneg (Nat.cast_nonneg _) hunit.le
  cases negative <;>
    simp only [roundTextMagnitude, Bool.false_eq_true, ite_false, ite_true,
      one_mul, neg_mul, abs_neg, abs_of_nonneg hmagnitude,
      abs_of_nonneg hfloor] <;> constructor
  · exact hc
  · exact ⟨hf, hf⟩
  · exact neg_le_neg hf
  · exact ⟨neg_le_neg hc, hf⟩

private theorem significantDecimal_directed_bounds (value : DecimalText.Decimal) (digits : ℕ+) :
    value.toRat ≤
        (DecimalText.significantDecimal (roundTextMagnitude .up)
          value digits).toRat ∧
      (DecimalText.significantDecimal (roundTextMagnitude .down)
        value digits).toRat ≤ value.toRat ∧
      |(DecimalText.significantDecimal (roundTextMagnitude .towardZero) value digits).toRat| ≤
        |value.toRat| := by
  have h := directedTextBounds value.negative
    ((value.significand : Rat) * (10 : Rat) ^ value.exponent)
    ((10 : Rat) ^ DecimalText.significantQuantum value.significand value.exponent digits)
    (mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num : (0 : Rat) < 10) _).le)
    (zpow_pos (by norm_num : (0 : Rat) < 10) _)
  simp only [DecimalText.significantDecimal_value]
  cases hs : value.negative <;>
    simpa [DecimalText.Decimal.toRat, hs, mul_assoc] using h

/-- Decimal output rounded toward positive infinity is at least the exact input. -/
theorem le_significantDecimal_up (value : DecimalText.Decimal)
    (digits : ℕ+) :
    value.toRat ≤ (DecimalText.significantDecimal
      (roundTextMagnitude .up) value digits).toRat :=
  (significantDecimal_directed_bounds value digits).1

/-- Decimal output rounded toward negative infinity is at most the exact input. -/
theorem significantDecimal_down_le (value : DecimalText.Decimal)
    (digits : ℕ+) :
    (DecimalText.significantDecimal (roundTextMagnitude .down)
      value digits).toRat ≤ value.toRat :=
  (significantDecimal_directed_bounds value digits).2.1

/-- Decimal output rounded toward zero cannot increase the magnitude. -/
theorem significantDecimal_towardZero_abs_le (value : DecimalText.Decimal) (digits : ℕ+) :
    |(DecimalText.significantDecimal (roundTextMagnitude .towardZero) value digits).toRat| ≤
      |value.toRat| :=
  (significantDecimal_directed_bounds value digits).2.2

private theorem significantHex_directed_bounds (value : Numerics.Dyadic) (digits : ℕ+) :
    value.toRat ≤ (HexText.significant (roundTextMagnitude .up)
        value digits).toRat ∧
      (HexText.significant (roundTextMagnitude .down)
        value digits).toRat ≤ value.toRat ∧
      |(HexText.significant (roundTextMagnitude .towardZero) value digits).toRat| ≤
        |value.toRat| := by
  have h := directedTextBounds value.negative
    (((HexText.radixPair value).1 : Rat) * (16 : Rat) ^ (HexText.radixPair value).2)
    ((16 : Rat) ^ RadixText.significantQuantum 16 (HexText.radixPair value).1
      (HexText.radixPair value).2 digits)
    (mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num : (0 : Rat) < 16) _).le)
    (zpow_pos (by norm_num : (0 : Rat) < 16) _)
  simp only [HexText.significant_value, RadixText.roundCoefficient]
  rw [HexText.radixPair_value] at h
  cases hs : value.negative <;>
    simpa [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand, hs, mul_assoc,
      HexText.radixPair_value] using h

/-- Hexadecimal output toward positive infinity is at least the exact input. -/
theorem le_significantHex_up (value : Numerics.Dyadic) (digits : ℕ+) :
    value.toRat ≤ (HexText.significant (roundTextMagnitude .up)
      value digits).toRat :=
  (significantHex_directed_bounds value digits).1

/-- Hexadecimal output toward negative infinity is at most the exact input. -/
theorem significantHex_down_le (value : Numerics.Dyadic) (digits : ℕ+) :
    (HexText.significant (roundTextMagnitude .down) value digits).toRat ≤
      value.toRat :=
  (significantHex_directed_bounds value digits).2.1

/-- Hexadecimal output toward zero cannot increase the magnitude. -/
theorem significantHex_towardZero_abs_le (value : Numerics.Dyadic) (digits : ℕ+) :
    |(HexText.significant (roundTextMagnitude .towardZero) value digits).toRat| ≤
      |value.toRat| :=
  (significantHex_directed_bounds value digits).2.2

end FloatLib.Floats.Formats.BinaryInterchange.Model
