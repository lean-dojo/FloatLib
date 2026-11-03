/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Scaling
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.NearestEven

/-!
# Directed integer rounding of nonnegative rational quotients

The quotient operations used by directed rational rounding satisfy format-independent order
bounds. Floor rounding lies below the exact real quotient, ceiling rounding lies above it, and
integer lower and upper thresholds are preserved in the expected directions. The ceiling is
`Numerics.roundQuotient .up`. Whether a quotient is an exact tie, as nearest-away rounding needs to
know, depends only on the rational it represents.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats.Formats.Flocq

section

/-! ## Natural quotient bounds -/

/-- The floor quotient is no larger than the ceiling quotient. -/
theorem div_le_roundQuotient_up (numerator denominator : Nat) :
    numerator / denominator ≤ Numerics.roundQuotient .up numerator denominator := by
  by_cases hdenominator : denominator = 0
  · simp [hdenominator, Numerics.roundQuotient_up_eq]
  · by_cases hremainder : numerator % denominator = 0
    · simp [Numerics.roundQuotient_up_eq, hdenominator, hremainder]
    · simp [Numerics.roundQuotient_up_eq, hdenominator, hremainder]

/-- The ceiling quotient is at most one larger than the floor quotient. -/
theorem roundQuotient_up_le_div_add_one (numerator denominator : Nat) :
    Numerics.roundQuotient .up numerator denominator ≤ numerator / denominator + 1 := by
  by_cases hdenominator : denominator = 0
  · simp [hdenominator, Numerics.roundQuotient_up_eq]
  · by_cases hremainder : numerator % denominator = 0
    · simp [Numerics.roundQuotient_up_eq, hdenominator, hremainder]
    · simp [Numerics.roundQuotient_up_eq, hdenominator, hremainder]

/-- Multiplying the floor quotient back by its denominator does not exceed the numerator. -/
theorem div_mul_le_numerator (numerator denominator : Nat) :
    numerator / denominator * denominator ≤ numerator :=
  Nat.div_mul_le_self numerator denominator

/-! ## Exact real enclosure -/

/--
The executable natural ceiling is the exact integer ceiling of the represented real quotient. A zero
denominator gives zero on both sides.
-/
theorem ceil_div_eq_roundQuotient_up (numerator denominator : Nat) :
    (⌈(numerator : Real) / (denominator : Real)⌉ : Int) =
      Int.ofNat (Numerics.roundQuotient .up numerator denominator) := by
  by_cases hdenominator : denominator = 0
  · simp [hdenominator, Numerics.roundQuotient_up_eq]
  let quotient := numerator / denominator
  let remainder := numerator % denominator
  have hdivision :
      denominator * quotient + remainder = numerator := by
    simpa [quotient, remainder] using Nat.div_add_mod numerator denominator
  have hdivisionReal :
      ((denominator * quotient : Nat) : Real) + (remainder : Real) =
        (numerator : Real) := by
    exact_mod_cast hdivision
  have hdenominatorReal : (denominator : Real) ≠ 0 := by
    exact_mod_cast hdenominator
  have hsplit :
      (numerator : Real) / (denominator : Real) =
        (quotient : Real) + (remainder : Real) / (denominator : Real) := by
    have h :=
      congrArg (fun value : Real => value / (denominator : Real)) hdivisionReal
    simp [add_div, hdenominatorReal] at h
    simpa [Nat.cast_div] using h.symm
  by_cases hremainder : remainder = 0
  · rw [hsplit, hremainder]
    simp [Numerics.roundQuotient_up_eq, hdenominator, quotient, remainder, hremainder]
  · have hdenominatorPos : (0 : Real) < denominator := by
      exact_mod_cast Nat.pos_of_ne_zero hdenominator
    have hremainderPos : (0 : Real) < remainder := by
      exact_mod_cast Nat.pos_of_ne_zero hremainder
    have hremainderLt : (remainder : Real) < denominator := by
      exact_mod_cast Nat.mod_lt numerator (Nat.pos_of_ne_zero hdenominator)
    have hfractionPos :
        0 < (remainder : Real) / (denominator : Real) :=
      div_pos hremainderPos hdenominatorPos
    have hfractionLe :
        (remainder : Real) / (denominator : Real) ≤ 1 :=
      (div_le_one hdenominatorPos).2 hremainderLt.le
    have hroundUp :
        Numerics.roundQuotient .up numerator denominator = quotient + 1 := by
      simp [Numerics.roundQuotient_up_eq, hdenominator, quotient, remainder, hremainder]
    rw [hsplit, hroundUp, Int.ceil_eq_iff]
    constructor <;> norm_num <;> linarith

/-- The exact real quotient lies below its natural ceiling quotient. -/
theorem div_le_natCast_roundQuotient_up (numerator denominator : Nat) :
    (numerator : Real) / (denominator : Real) ≤
      (Numerics.roundQuotient .up numerator denominator : Real) := by
  have hceil := Int.le_ceil ((numerator : Real) / (denominator : Real))
  rw [ceil_div_eq_roundQuotient_up] at hceil
  exact_mod_cast hceil

/-- Multiplying the ceiling quotient back by a nonzero denominator covers the numerator. -/
theorem numerator_le_roundQuotient_up_mul
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    numerator ≤ Numerics.roundQuotient .up numerator denominator * denominator := by
  have hdenominatorPos : (0 : Real) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  have hreal := (div_le_iff₀ hdenominatorPos).mp
    (div_le_natCast_roundQuotient_up numerator denominator)
  exact_mod_cast hreal

/-- Downward quotient rounding is a lower bound on the exact real quotient. -/
theorem natCast_roundQuotDirected_false_le (numerator denominator : Nat) :
    (roundQuotDirected false numerator denominator : Real) ≤
      (numerator : Real) / (denominator : Real) := by
  simpa [roundQuotDirected] using
    (Nat.cast_div_le : ((numerator / denominator : Nat) : Real) ≤ numerator / denominator)

/-- Upward quotient rounding is an upper bound on the exact real quotient. -/
theorem le_natCast_roundQuotDirected_true (numerator denominator : Nat) :
    (numerator : Real) / (denominator : Real) ≤
      (roundQuotDirected true numerator denominator : Real) := by
  simpa [roundQuotDirected] using
    div_le_natCast_roundQuotient_up numerator denominator

/-! ## Exact rational invariance -/

/-- Directed quotient rounding depends only on the represented nonnegative rational. -/
theorem roundQuotDirected_eq_of_rat_eq
    (roundUp : Bool)
    (numerator denominator numerator' denominator' : Nat)
    (hvalue :
      (numerator : Real) / (denominator : Real) =
        (numerator' : Real) / (denominator' : Real)) :
    roundQuotDirected roundUp numerator denominator =
      roundQuotDirected roundUp numerator' denominator' := by
  cases roundUp
  · simp only [roundQuotDirected, Bool.false_eq_true, ite_false]
    apply Int.ofNat_inj.mp
    calc
      Int.ofNat (numerator / denominator) =
          ⌊(numerator : Real) / (denominator : Real)⌋ :=
        (floor_real_nat_div numerator denominator).symm
      _ = ⌊(numerator' : Real) / (denominator' : Real)⌋ :=
        congrArg Int.floor hvalue
      _ = Int.ofNat (numerator' / denominator') :=
        floor_real_nat_div numerator' denominator'
  · simp only [roundQuotDirected, ite_true]
    apply Int.ofNat_inj.mp
    calc
      Int.ofNat (Numerics.roundQuotient .up numerator denominator) =
          ⌈(numerator : Real) / (denominator : Real)⌉ :=
        (ceil_div_eq_roundQuotient_up numerator denominator).symm
      _ = ⌈(numerator' : Real) / (denominator' : Real)⌉ :=
        congrArg Int.ceil hvalue
      _ = Int.ofNat (Numerics.roundQuotient .up numerator' denominator') :=
        ceil_div_eq_roundQuotient_up numerator' denominator'

/-- Two successive power-of-two scalings denote one scaling by the summed exponent. -/
private theorem scaleByPowerOfTwo_twice_ratio
    (numerator denominator : Nat) (firstExponent secondExponent : Int) :
    let first :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator firstExponent
    let second :=
      Numerics.RationalBinary.scaleByPowerOfTwo first.1 first.2 secondExponent
    let combined :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        numerator denominator (firstExponent + secondExponent)
    (second.1 : Real) / (second.2 : Real) = (combined.1 : Real) / (combined.2 : Real) := by
  dsimp only
  rw [scaleByPowerOfTwo_real, scaleByPowerOfTwo_real]
  change
    ((Numerics.RationalBinary.scaleByPowerOfTwo
        numerator denominator firstExponent).1 : Real) /
          ((Numerics.RationalBinary.scaleByPowerOfTwo
            numerator denominator firstExponent).2 : Real) *
        bpow secondExponent =
      scaledRatToReal numerator denominator (firstExponent + secondExponent)
  rw [scaleByPowerOfTwo_real]
  exact scaledRatToReal_mul_bpow
    numerator denominator firstExponent secondExponent

/-- Successive exact binary scalings may be combined before directed quotient rounding. -/
theorem roundQuotDirected_scaleByPowerOfTwo_add
    (roundUp : Bool) (numerator denominator : Nat)
    (firstExponent secondExponent : Int) :
    let first :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        numerator denominator firstExponent
    let second :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        first.1 first.2 secondExponent
    let combined :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        numerator denominator (firstExponent + secondExponent)
    roundQuotDirected roundUp second.1 second.2 =
      roundQuotDirected roundUp combined.1 combined.2 := by
  dsimp only
  apply roundQuotDirected_eq_of_rat_eq
  exact scaleByPowerOfTwo_twice_ratio numerator denominator firstExponent secondExponent

/--
Whether a quotient is an exact tie, twice its remainder equal to its denominator, depends only on
the represented nonnegative rational.
-/
theorem two_mul_mod_eq_iff_of_rat_eq
    (numerator denominator numerator' denominator' : Nat)
    (hdenominator : denominator ≠ 0) (hdenominator' : denominator' ≠ 0)
    (hvalue :
      (numerator : Real) / (denominator : Real) =
        (numerator' : Real) / (denominator' : Real)) :
    2 * (numerator % denominator) = denominator ↔
      2 * (numerator' % denominator') = denominator' := by
  apply Numerics.two_mul_mod_eq_iff_of_mul_eq _ _ _ _ hdenominator hdenominator'
  have hdenominatorReal : (denominator : Real) ≠ 0 := by
    exact_mod_cast hdenominator
  have hdenominatorReal' : (denominator' : Real) ≠ 0 := by
    exact_mod_cast hdenominator'
  rw [div_eq_div_iff hdenominatorReal hdenominatorReal'] at hvalue
  exact_mod_cast hvalue

/-- Successive exact binary scalings may be combined before testing for an exact quotient tie. -/
theorem two_mul_mod_scaleByPowerOfTwo_add_iff
    (numerator denominator : Nat)
    (firstExponent secondExponent : Int) (hdenominator : denominator ≠ 0) :
    let first :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        numerator denominator firstExponent
    let second :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        first.1 first.2 secondExponent
    let combined :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        numerator denominator (firstExponent + secondExponent)
    2 * (second.1 % second.2) = second.2 ↔
      2 * (combined.1 % combined.2) = combined.2 := by
  dsimp only
  apply two_mul_mod_eq_iff_of_rat_eq
  · exact Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero _ _ _
      (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
        numerator denominator firstExponent hdenominator)
  · exact Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
      numerator denominator (firstExponent + secondExponent) hdenominator
  · exact scaleByPowerOfTwo_twice_ratio numerator denominator firstExponent secondExponent

/-! ## Preservation of integer thresholds -/

/-- An integer lower bound on a quotient survives either directed integer rounding. -/
theorem le_roundQuotDirected_of_mul_le
    (roundUp : Bool) (numerator denominator lower : Nat)
    (hdenominator : denominator ≠ 0)
    (hlower : lower * denominator ≤ numerator) :
    lower ≤ roundQuotDirected roundUp numerator denominator := by
  have hfloor :
      lower ≤ numerator / denominator :=
    (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hdenominator)).2 hlower
  cases roundUp with
  | false => simpa [roundQuotDirected] using hfloor
  | true =>
      simpa [roundQuotDirected] using
        hfloor.trans (div_le_roundQuotient_up numerator denominator)

/--
A strict integer upper bound on a quotient bounds either directed integer rounding. The bound
forces a nonzero denominator.
-/
theorem roundQuotDirected_le_of_lt_mul
    (roundUp : Bool) (numerator denominator upper : Nat)
    (hupper : numerator < upper * denominator) :
    roundQuotDirected roundUp numerator denominator ≤ upper := by
  have hdenominator : denominator ≠ 0 := by
    rintro rfl
    simp at hupper
  have hfloor :
      numerator / denominator < upper :=
    (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hdenominator)).2 hupper
  cases roundUp with
  | false =>
      simpa [roundQuotDirected] using hfloor.le
  | true =>
      simp only [roundQuotDirected, ite_true]
      exact (roundQuotient_up_le_div_add_one numerator denominator).trans (by omega)

/--
A real power-of-two lower bound survives either directed integer rounding. The bound forces a
nonzero denominator.
-/
theorem pow2_le_roundQuotDirected_of_le_div
    (roundUp : Bool) (numerator denominator exponent : Nat)
    (hlower :
      ((pow2 exponent : Nat) : Real) ≤
        (numerator : Real) / (denominator : Real)) :
    pow2 exponent ≤ roundQuotDirected roundUp numerator denominator := by
  have hdenominator : denominator ≠ 0 := by
    rintro rfl
    have hpositive : (0 : Real) < ((pow2 exponent : Nat) : Real) := by
      rw [pow2_eq_two_pow]
      exact_mod_cast Nat.two_pow_pos exponent
    simp only [Nat.cast_zero, div_zero] at hlower
    linarith
  have hdenominatorPos : (0 : Real) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  have hmulReal :
      ((pow2 exponent : Nat) : Real) * denominator ≤ numerator :=
    (le_div_iff₀ hdenominatorPos).mp hlower
  have hmulNat : pow2 exponent * denominator ≤ numerator := by
    exact_mod_cast hmulReal
  exact le_roundQuotDirected_of_mul_le roundUp numerator denominator
    (pow2 exponent) hdenominator hmulNat

/-- A strict real power-of-two upper bound strictly bounds downward integer rounding. -/
theorem roundQuotDirected_false_lt_pow2_of_div_lt
    (numerator denominator exponent : Nat)
    (hupper :
      (numerator : Real) / (denominator : Real) <
        ((pow2 exponent : Nat) : Real)) :
    roundQuotDirected false numerator denominator < pow2 exponent := by
  have hreal := (natCast_roundQuotDirected_false_le numerator denominator).trans_lt hupper
  exact_mod_cast hreal

/-- A strict real power-of-two upper bound weakly bounds either directed integer rounding. -/
theorem roundQuotDirected_le_pow2_of_div_lt
    (roundUp : Bool) (numerator denominator exponent : Nat)
    (hupper :
      (numerator : Real) / (denominator : Real) <
        ((pow2 exponent : Nat) : Real)) :
    roundQuotDirected roundUp numerator denominator ≤ pow2 exponent := by
  by_cases hdenominator : denominator = 0
  · cases roundUp <;> simp [roundQuotDirected, hdenominator, Numerics.roundQuotient_up_eq]
  have hdenominatorPos : (0 : Real) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  have hmulReal :
      (numerator : Real) < ((pow2 exponent : Nat) : Real) * denominator :=
    (div_lt_iff₀ hdenominatorPos).mp hupper
  have hmulNat : numerator < pow2 exponent * denominator := by
    exact_mod_cast hmulReal
  exact roundQuotDirected_le_of_lt_mul roundUp numerator denominator
    (pow2 exponent) hmulNat

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
