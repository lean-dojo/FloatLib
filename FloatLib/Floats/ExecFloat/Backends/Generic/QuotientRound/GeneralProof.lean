/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.QuotientRound.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime
public import Mathlib.Tactic.Linarith

/-!
# Exactness of single-quotient rounding

If `num = den * q + r`, with `r < den`, dividing `2 * num` yields `2 * q` below the
midpoint and `2 * q + 1` at or above it. Thus its low two bits and the equality test
`den * quotient = 2 * num` contain precisely the information needed for ties to even.
The low-word product can only reject that equality; a collision is checked in full.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteQuotientRound

open FloatLib.Numerics

private theorem low_one_eq_zero (n : Nat) :
    UInt64.ofNat n &&& 1 = 0 ↔ n % 2 = 0 := by
  rw [← UInt64.toNat_inj]
  simp only [UInt64.toNat_and, UInt64.toNat_ofNat', UInt64.toNat_zero,
    UInt64.toNat_one, Nat.and_one_is_mod]
  norm_num [UInt64.size]

private theorem and_two_eq_zero (n : Nat) :
    n &&& 2 = 0 ↔ n / 2 % 2 = 0 := by
  have hhalf : (n &&& 2) / 2 = n / 2 % 2 := by
    rw [Nat.and_div_two]
    simp
  have heven : (n &&& 2) % 2 = 0 := by
    have := Nat.and_mod_two_eq_one (a := n) (b := 2)
    omega
  omega

private theorem low_two_eq_zero (n : Nat) :
    UInt64.ofNat n &&& 2 = 0 ↔ n / 2 % 2 = 0 := by
  rw [← UInt64.toNat_inj]
  simp only [UInt64.toNat_and, UInt64.toNat_ofNat', UInt64.toNat_zero]
  norm_num [UInt64.size]
  rw [and_two_eq_zero]
  omega

private theorem roundEvenDoubled_eq (doubled den : Nat) :
    roundEvenDoubled doubled den =
      let quotient := doubled / den
      let lower := quotient / 2
      if quotient % 2 == 0 then lower
      else if lower % 2 != 0 then lower + 1
      else if quotient * den != doubled then lower + 1
      else lower := by
  simp only [roundEvenDoubled, Nat.shiftRight_eq_div_pow, Nat.pow_one,
    beq_iff_eq, bne_iff_ne, ne_eq, low_one_eq_zero, low_two_eq_zero]
  split
  · rfl
  split
  · rfl
  by_cases hproduct : doubled / den * den = doubled
  · have hlow : UInt64.ofNat (doubled / den) * UInt64.ofNat den =
        UInt64.ofNat doubled := by
      rw [← UInt64.ofNat_mul, hproduct]
    simp [hproduct, hlow]
  · simp [hproduct]

/-- The extra quotient bit implements exact nearest-even rounding for every nonzero divisor. -/
theorem roundEvenDoubled_twice (num den : Nat) (hden : den ≠ 0) :
    roundEvenDoubled (2 * num) den = roundQuotientEven num den := by
  have hpos : 0 < den := Nat.pos_of_ne_zero hden
  have hrem := Nat.mod_lt num hpos
  have hdiv := Nat.div_add_mod num den
  rw [roundEvenDoubled_eq]
  unfold roundQuotientEven
  by_cases hbelow : 2 * (num % den) < den
  · have hquotient : 2 * num / den = 2 * (num / den) := by
      apply Nat.div_eq_of_lt_le <;> nlinarith only [hdiv, hbelow, Nat.zero_le (num % den)]
    simp [hquotient, hbelow]
  · have hquotient : 2 * num / den = 2 * (num / den) + 1 := by
      apply Nat.div_eq_of_lt_le <;> nlinarith
    have hlower : (2 * (num / den) + 1) / 2 = num / den := by omega
    rw [hquotient]
    simp only [hlower, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.one_mod,
      Nat.one_ne_zero, beq_iff_eq, bne_iff_ne, ite_false, hbelow]
    by_cases habove : den < 2 * (num % den)
    · have hproduct : (2 * (num / den) + 1) * den ≠ 2 * num := by nlinarith
      simp [habove, hproduct]
    · have hproduct : (2 * (num / den) + 1) * den = 2 * num := by nlinarith
      simp [habove, hproduct]
      split <;> simp_all

/-- Fusing the binary scale into the doubled numerator preserves quotient rounding. -/
theorem roundEvenScaled_eq (num den : Nat) (shift : Int) (hden : den ≠ 0) :
    roundEvenScaled num den shift =
      let scaled := RationalBinary.scaleByPowerOfTwo num den shift
      roundQuotientEven scaled.1 scaled.2 := by
  cases shift with
  | ofNat shift =>
      simp only [roundEvenScaled, RationalBinary.scaleByPowerOfTwo, Nat.shiftLeft_add]
      rw [show (num <<< shift) <<< 1 = 2 * (num <<< shift) by
        simp [Nat.shiftLeft_eq, Nat.mul_comm]]
      exact roundEvenDoubled_twice _ _ hden
  | negSucc shift =>
      simp only [roundEvenScaled, RationalBinary.scaleByPowerOfTwo]
      rw [show num <<< 1 = 2 * num by simp [Nat.shiftLeft_eq, Nat.mul_comm]]
      apply roundEvenDoubled_twice
      simp [Nat.shiftLeft_eq, hden]

/-- The one-quotient ceiling agrees with the reference, including its zero conventions. -/
theorem ceilQuotient_eq (num den : Nat) : ceilQuotient num den = quotCeil num den := by
  by_cases hden : den = 0
  · simp [ceilQuotient, quotCeil, hden]
  by_cases hnum : num = 0
  · simp [ceilQuotient, quotCeil, hnum, hden]
  have hpos : 0 < den := Nat.pos_of_ne_zero hden
  have hrem := Nat.mod_lt num hpos
  have hdiv := Nat.div_add_mod num den
  have hsucc : num - 1 + 1 = num := by omega
  simp only [ceilQuotient, quotCeil, hnum, hden, beq_iff_eq, Bool.or_eq_true,
    or_self, ite_false]
  by_cases hexact : num % den = 0
  · have hqpos : 0 < num / den := by nlinarith
    have hqsucc : num / den - 1 + 1 = num / den := by omega
    have hquotient : (num - 1) / den = num / den - 1 := by
      apply Nat.div_eq_of_lt_le <;> nlinarith
    simp [hexact, hquotient, hqsucc]
  · have hquotient : (num - 1) / den = num / den := by
      have hremPos : 0 < num % den := Nat.pos_of_ne_zero hexact
      apply Nat.div_eq_of_lt_le <;> nlinarith
    simp [hexact, hquotient]

/-- Directed rounding uses the same lower and upper adjacent integers as the reference. -/
theorem roundDirectedScaled_eq (up : Bool) (num den : Nat) (shift : Int) :
    roundDirectedScaled up num den shift =
      let scaled := RationalBinary.scaleByPowerOfTwo num den shift
      roundQuotDirected up scaled.1 scaled.2 := by
  simp only [roundDirectedScaled, roundQuotDirected, ceilQuotient_eq]

/-- The IEEE branch preserves every threshold, carry, signed zero, and subnormal tie. -/
theorem ieeeRoundAtExponent_eq (fmt : FloatFormat) (sign : Bool) (num den : Nat)
    (exponent rationalExponent : Int) (hfmt : fmt.isIEEE = true)
    (hlog : rationalExponent = RationalBinary.floorLog2 num den) :
    ieeeRoundAtExponent fmt sign num den exponent rationalExponent =
      ieeeRoundRatScaled fmt sign num den exponent hfmt := by
  subst rationalExponent
  by_cases hden : den = 0
  · simp [ieeeRoundAtExponent, ieeeRoundRatScaled, hden]
  · unfold ieeeRoundAtExponent ieeeRoundRatScaled
    simp_rw [roundEvenScaled_eq num den _ hden]
    rw [roundEvenScaled_eq num den _ hden]
    rfl

/-- Custom descriptor policies use the same exact quotient and packing semantics. -/
theorem generalRoundAtExponent_eq (fmt : FloatFormat) (sign : Bool) (num den : Nat)
    (exponent rationalExponent : Int)
    (hlog : rationalExponent = RationalBinary.floorLog2 num den) :
    generalRoundAtExponent fmt sign num den exponent rationalExponent =
      roundRatScaledGeneral fmt sign num den exponent := by
  subst rationalExponent
  by_cases hden : den = 0
  · simp [generalRoundAtExponent, roundRatScaledGeneral, hden]
  · simp only [generalRoundAtExponent, roundRatScaledGeneral, roundEvenScaled_eq num den _ hden]

/-- Both directed magnitudes agree with the reference rational rounder. -/
theorem directedRoundAtExponent_eq (fmt : FloatFormat) (up sign : Bool) (num den : Nat)
    (exponent rationalExponent : Int)
    (hlog : rationalExponent = RationalBinary.floorLog2 num den) :
    directedRoundAtExponent fmt up sign num den exponent rationalExponent =
      roundRatMagnitudeDirectedScaled fmt up sign num den exponent := by
  subst rationalExponent
  simp only [directedRoundAtExponent, roundRatMagnitudeDirectedScaled, roundDirectedScaled_eq]

/-- A correct rational exponent suffices for exact agreement in every IEEE rounding direction. -/
theorem roundAtExponent_eq (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (num den : Nat) (exponent rationalExponent : Int)
    (hlog : rationalExponent = RationalBinary.floorLog2 num den) :
    roundAtExponent fmt mode sign num den exponent rationalExponent =
      roundRatWithRoundingScaled fmt mode sign num den exponent := by
  cases mode with
  | nearestEven =>
      by_cases hfmt : fmt.isIEEE = true
      · simp [roundAtExponent, roundRatWithRoundingScaled, roundRatScaled,
          hfmt, ieeeRoundAtExponent_eq _ _ _ _ _ _ hfmt hlog]
      · simp [roundAtExponent, roundRatWithRoundingScaled, roundRatScaled,
          hfmt, generalRoundAtExponent_eq _ _ _ _ _ _ hlog]
  | towardZero | towardPositiveInfinity | towardNegativeInfinity =>
      simp only [roundAtExponent, roundRatWithRoundingScaled,
        directedRoundAtExponent_eq _ _ _ _ _ _ _ hlog]

/-- The standalone rounder refines exact rational rounding without width or format restrictions. -/
theorem roundScaled_eq (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (num den : Nat) (exponent : Int) :
    roundScaled fmt mode sign num den exponent =
      roundRatWithRoundingScaled fmt mode sign num den exponent :=
  roundAtExponent_eq _ _ _ _ _ _ _ rfl

/--
Two normalized significands of the same precision have ratio in `(1/2, 2)`.
Their relative order therefore determines its binary exponent.
-/
theorem floorLog2_eq_of_normal (precision num den : Nat)
    (hnum : 2 ^ precision ≤ num ∧ num < 2 ^ (precision + 1))
    (hden : 2 ^ precision ≤ den ∧ den < 2 ^ (precision + 1)) :
    RationalBinary.floorLog2 num den = if den ≤ num then 0 else -1 := by
  have hnumNe := Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hnum.1)
  have hdenNe := Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hden.1)
  have hnumLog := (Nat.log2_eq_iff hnumNe).2 hnum
  have hdenLog := (Nat.log2_eq_iff hdenNe).2 hden
  unfold RationalBinary.floorLog2
  rw [hnumLog, hdenLog, sub_self]
  norm_num
  by_cases hle : den ≤ num
  · have hltTwice : num < den * 2 := calc
      num < 2 ^ (precision + 1) := hnum.2
      _ = 2 ^ precision * 2 := pow_succ 2 precision
      _ ≤ den * 2 := Nat.mul_le_mul_right 2 hden.1
    have hnotLt := Nat.not_lt_of_ge hle
    have hnotTwice : ¬den * 2 ≤ num := by omega
    simp [RationalBinary.lessThanPowerOfTwo, RationalBinary.atLeastPowerOfTwo,
      hle, hnotLt, hnotTwice, Nat.shiftLeft_eq]
  · have hlt := Nat.lt_of_not_ge hle
    simp [RationalBinary.lessThanPowerOfTwo, RationalBinary.atLeastPowerOfTwo,
      hle, hlt, Nat.shiftLeft_eq]

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteQuotientRound
