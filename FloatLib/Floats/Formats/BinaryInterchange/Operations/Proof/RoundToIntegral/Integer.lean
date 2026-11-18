/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.RealSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Nearest

import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact

/-!
# Integer selection from exact dyadics

The unbounded integral-rounding kernel computes floor, ceiling, truncation, away-from-zero,
nearest-even or nearest-away according to its rounding mode. Its result lies between the floor and
ceiling, and truncation does not increase absolute value. Integrality is characterized by the
absence of fractional bits.

## References

* IEEE 754-2019, Sections 4.3.2 and 5.9 (directed and integral rounding).
  https://doi.org/10.1109/IEEESTD.2019.8766229
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics
open FloatLib.Floats.Formats.Flocq

/-- Exact zero rounds to integer zero in every direction. -/
@[simp] theorem roundDyadicToInt_zero (mode : IEEERoundingMode) :
    roundDyadicToInt mode Numerics.Dyadic.zero = 0 := by
  simp [roundDyadicToInt, Numerics.Dyadic.zero]

private theorem roundDyadicToInt_nearest_kernel
    (value : Numerics.Dyadic) :
    roundDyadicToInt .nearest value =
      if value.negative then
        -Int.ofNat
          (roundMantissaAtExponentEven
            value.significand value.exponent 0)
      else
        Int.ofNat
          (roundMantissaAtExponentEven
            value.significand value.exponent 0) := by
  rcases value with ⟨negative, significand, exponent⟩
  by_cases hsignificand : significand = 0
  · subst significand
    simp [roundDyadicToInt, roundMantissaAtExponentEven,
      Numerics.roundShiftRightEven_def]
  · cases exponent with
    | ofNat shift =>
        cases negative <;> cases shift <;>
          simp [roundDyadicToInt, hsignificand,
            roundMantissaAtExponentEven]
    | negSucc shift =>
        have hle : Int.negSucc shift ≤ 0 := by omega
        cases negative <;>
          simp [roundDyadicToInt, hsignificand,
            roundMantissaAtExponentEven, hle]

private theorem roundDyadicToInt_up_kernel
    (value : Numerics.Dyadic) :
    roundDyadicToInt .up value =
      roundSignedMantissaAtExponentUp value.negative
        value.significand value.exponent 0 := by
  rcases value with ⟨negative, significand, exponent⟩
  by_cases hsignificand : significand = 0
  · subst significand
    cases negative <;> cases exponent <;>
      simp [roundDyadicToInt,
        roundSignedMantissaAtExponentUp, roundMantissaAtExponentDown,
        roundMantissaAtExponentUp, Numerics.shiftRightCeil]
  · cases exponent with
    | ofNat shift =>
        cases negative <;> cases shift <;>
          simp [roundDyadicToInt, hsignificand,
            roundSignedMantissaAtExponentUp, roundMantissaAtExponentDown,
            roundMantissaAtExponentUp, Numerics.shiftRightCeil]
    | negSucc shift =>
        cases negative <;>
          simp [roundDyadicToInt, hsignificand,
            roundSignedMantissaAtExponentUp, roundMantissaAtExponentDown,
            roundMantissaAtExponentUp, Numerics.shiftRightCeil,
            shiftRightRemainder]

private theorem roundDyadicToInt_towardZero_kernel
    (value : Numerics.Dyadic) :
    roundDyadicToInt .towardZero value =
      if value.negative then
        -Int.ofNat
          (roundMantissaAtExponentDown
            value.significand value.exponent 0)
      else
        Int.ofNat
          (roundMantissaAtExponentDown
            value.significand value.exponent 0) := by
  rcases value with ⟨negative, significand, exponent⟩
  by_cases hsignificand : significand = 0
  · subst significand
    cases negative <;> cases exponent <;>
      simp [roundDyadicToInt, roundMantissaAtExponentDown]
  · cases exponent with
    | ofNat shift =>
        cases negative <;> cases shift <;>
          simp [roundDyadicToInt, hsignificand,
            roundMantissaAtExponentDown]
    | negSucc shift =>
        cases negative <;>
          simp [roundDyadicToInt, hsignificand,
            roundMantissaAtExponentDown]

private theorem roundDyadicToInt_towardZero_by_sign
    (value : Numerics.Dyadic) :
    roundDyadicToInt .towardZero value =
      if value.negative then ⌈value.toReal⌉ else ⌊value.toReal⌋ := by
  rw [roundDyadicToInt_towardZero_kernel]
  cases hnegative : value.negative
  · simp only [Bool.false_eq_true, ite_false]
    have hsemantic :=
      floor_scaledDyadic false value.significand value.exponent 0
    simpa [floorRound, roundSignedMantissaAtExponentDown,
      Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
      hnegative, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using hsemantic.symm
  · simp only [ite_true]
    have hsemantic :=
      ceil_scaledDyadic true value.significand value.exponent 0
    simpa [ceilRound, roundSignedMantissaAtExponentUp,
      Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
      hnegative, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using hsemantic.symm

/--
Nearest-even integer rounding has its usual mathematical meaning, independently of the stored
dyadic exponent or magnitude.
-/
theorem roundDyadicToInt_nearest (value : Numerics.Dyadic) :
    roundDyadicToInt .nearest value = nearestEven value.toReal := by
  rw [roundDyadicToInt_nearest_kernel]
  have hsemantic :=
    nearestEven_scaledDyadic value.negative value.significand
      value.exponent 0
  simpa [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
    Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
    hsemantic.symm

/-- Rounding toward positive infinity computes the mathematical ceiling. -/
theorem roundDyadicToInt_up
    (value : Numerics.Dyadic) :
    roundDyadicToInt .up value = ⌈value.toReal⌉ := by
  rw [roundDyadicToInt_up_kernel]
  have hsemantic :=
    ceil_scaledDyadic value.negative value.significand value.exponent 0
  simpa [ceilRound, Numerics.Dyadic.toReal,
    Numerics.Dyadic.signedSignificand,
    Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using hsemantic.symm

/--
Integer rounding toward negative infinity is negated integer rounding toward positive infinity of
the negated dyadic: the magnitude rule of each direction is the other's on the opposite sign.
-/
private theorem roundDyadicToInt_down_eq_neg_up_neg (value : Numerics.Dyadic) :
    roundDyadicToInt .down value = -roundDyadicToInt .up value.neg := by
  rcases value with ⟨negative, significand, exponent⟩
  cases negative <;> cases exponent <;>
    simp only [roundDyadicToInt, beq_iff_eq, Bool.false_eq_true, ↓reduceIte, Nat.shiftLeft_eq',
    Int.ofNat_eq_natCast, Int.natCast_shiftLeft, Dyadic.neg_eq, Bool.not_false, Bool.true_or,
    Nat.shiftRight_eq', Int.natCast_shiftRight, Bool.not_true, Bool.false_or, Nat.cast_ite,
    Nat.cast_add, Nat.cast_one] <;> split_ifs <;> simp

/-- Rounding toward negative infinity computes the mathematical floor. -/
theorem roundDyadicToInt_down
    (value : Numerics.Dyadic) :
    roundDyadicToInt .down value = ⌊value.toReal⌋ := by
  rw [roundDyadicToInt_down_eq_neg_up_neg, roundDyadicToInt_up, Dyadic.toReal_neg, Int.ceil_neg,
    _root_.neg_neg]

/--
Rounding toward zero truncates the exact dyadic: nonnegative values use floor and negative values
use ceiling.
-/
theorem roundDyadicToInt_towardZero (value : Numerics.Dyadic) :
    roundDyadicToInt .towardZero value =
      if 0 ≤ value.toReal then ⌊value.toReal⌋ else ⌈value.toReal⌉ := by
  rw [roundDyadicToInt_towardZero_by_sign]
  by_cases hsignificand : value.significand = 0
  · simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
      hsignificand]
  · cases hnegative : value.negative
    · have hnonnegative := Dyadic.toReal_nonneg_of_negative_eq_false hnegative
      simp only [Bool.false_eq_true, ite_false]
      rw [ite_eq_left hnonnegative]
    · have hnegativeReal := Dyadic.toReal_lt_zero_of_negative_eq_true hnegative hsignificand
      simp only [ite_true]
      rw [ite_eq_right (not_le.mpr hnegativeReal)]

/--
Nearest rounding with ties away from zero of a nonnegative rational is nearest-away quotient
rounding of its numerator and denominator.
-/
private theorem nearestChoice_tieAway_div_eq_roundQuotient (num den : Nat) (hden : den ≠ 0) :
    nearestChoice nearestAwayChoice ((num : ℝ) / (den : ℝ)) =
      Int.ofNat (roundQuotient .nearestAway num den) := by
  have hdenPos : (0 : ℝ) < den := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hden)
  have hfloor : ⌊(num : ℝ) / (den : ℝ)⌋ = ((num / den : Nat) : Int) :=
    floor_real_nat_div num den
  have hfract : Int.fract ((num : ℝ) / (den : ℝ)) = ((num % den : Nat) : ℝ) / (den : ℝ) := by
    simpa only [Int.fract, floor_real_nat_div, Int.cast_natCast] using
      (Int.fract_div_natCast_eq_div_natCast_mod (m := num) (n := den) (k := ℝ))
  have hlt : ((num % den : Nat) : ℝ) / (den : ℝ) < 1 / 2 ↔ 2 * (num % den) < den := by
    rw [div_lt_iff₀ hdenPos]
    constructor
    · intro h
      have hcast : ((2 * (num % den) : Nat) : ℝ) < (den : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hcast
    · intro h
      have hcast : ((2 * (num % den) : Nat) : ℝ) < (den : ℝ) := by exact_mod_cast h
      push_cast at hcast
      linarith
  have hgt : 1 / 2 < ((num % den : Nat) : ℝ) / (den : ℝ) ↔ den < 2 * (num % den) := by
    rw [lt_div_iff₀ hdenPos]
    constructor
    · intro h
      have hcast : (den : ℝ) < ((2 * (num % den) : Nat) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hcast
    · intro h
      have hcast : (den : ℝ) < ((2 * (num % den) : Nat) : ℝ) := by exact_mod_cast h
      push_cast at hcast
      linarith
  have hchoose : nearestAwayChoice ((num / den : Nat) : Int) = true := by
    simp only [nearestAwayChoice, decide_eq_true_eq]
    exact Int.natCast_nonneg _
  rw [roundQuotient_nearestAway_eq_div_add num den hden]
  unfold nearestChoice
  simp only [hfloor, hfract, gt_iff_lt, hlt, hgt, hchoose, ite_true, Int.ofNat_eq_natCast]
  split_ifs <;> push_cast <;> omega

/-- Negating an exact dyadic negates its nearest-away integer. -/
private theorem roundDyadicToInt_nearestAway_neg (significand : Nat) (exponent : Int) :
    roundDyadicToInt .nearestAway { negative := true, significand, exponent } =
      -roundDyadicToInt .nearestAway { negative := false, significand, exponent } := by
  by_cases hsignificand : significand = 0
  · simp [roundDyadicToInt, hsignificand]
  · cases exponent <;> simp [roundDyadicToInt, hsignificand]

/--
Nearest rounding with ties away from zero of a nonnegative dyadic is the executable magnitude
rounding of `roundDyadicToInt`.
-/
private theorem nearestChoice_tieAway_scaledNat (significand : Nat) (exponent : Int) :
    nearestChoice nearestAwayChoice ((significand : ℝ) * (2 : ℝ) ^ exponent) =
      roundDyadicToInt .nearestAway { negative := false, significand, exponent } := by
  by_cases hsignificand : significand = 0
  · subst significand
    have hzero := nearestChoice_intCast nearestAwayChoice 0
    simp only [Int.cast_zero] at hzero
    simp [roundDyadicToInt, hzero]
  cases exponent with
  | ofNat shift =>
      have hvalue : (significand : ℝ) * (2 : ℝ) ^ (Int.ofNat shift) =
          (((Nat.shiftLeft significand shift : Nat) : Int) : ℝ) := by
        simp [Nat.shiftLeft_eq, zpow_natCast]
      rw [hvalue, nearestChoice_intCast]
      simp [roundDyadicToInt, hsignificand]
  | negSucc shift =>
      have hvalue : (significand : ℝ) * (2 : ℝ) ^ (Int.negSucc shift) =
          (significand : ℝ) / ((2 ^ (shift + 1) : Nat) : ℝ) := by
        rw [zpow_negSucc]
        push_cast
        rfl
      rw [hvalue, nearestChoice_tieAway_div_eq_roundQuotient _ _ (Nat.two_pow_pos _).ne',
        ← Numerics.roundShiftRight_eq_roundQuotient]
      simp [roundDyadicToInt, hsignificand]

/--
Nearest-away integer rounding is Flocq's nearest rounding with ties away from zero, independently
of the stored dyadic exponent or magnitude.
-/
theorem roundDyadicToInt_nearestAway (value : Numerics.Dyadic) :
    roundDyadicToInt .nearestAway value = nearestChoice nearestAwayChoice value.toReal := by
  rcases value with ⟨negative, significand, exponent⟩
  cases negative
  · have hreal : ({ negative := false, significand, exponent } : Numerics.Dyadic).toReal =
        (significand : ℝ) * (2 : ℝ) ^ exponent := by
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]
    rw [hreal, nearestChoice_tieAway_scaledNat]
  · have hreal : ({ negative := true, significand, exponent } : Numerics.Dyadic).toReal =
        -((significand : ℝ) * (2 : ℝ) ^ exponent) := by
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]
    have hneg := congrFun negRound_nearestChoice_tieAway ((significand : ℝ) * (2 : ℝ) ^ exponent)
    simp only [negRound] at hneg
    rw [hreal, roundDyadicToInt_nearestAway_neg, ← nearestChoice_tieAway_scaledNat, ← hneg,
      _root_.neg_neg]

private theorem roundDyadicToInt_away_by_sign (value : Numerics.Dyadic) :
    roundDyadicToInt .away value =
      if value.negative then roundDyadicToInt .down value
      else roundDyadicToInt .up value := by
  rcases value with ⟨negative, significand, exponent⟩
  by_cases hsignificand : significand = 0
  · subst significand
    cases negative <;> simp [roundDyadicToInt]
  · cases exponent with
    | ofNat shift =>
        cases negative <;> simp [roundDyadicToInt, hsignificand]
    | negSucc shift =>
        cases negative <;>
          simp [roundDyadicToInt, hsignificand, Numerics.shiftRightCeil,
            Numerics.shiftRightRemainder]

/--
Rounding away from zero takes the ceiling of a nonnegative exact dyadic and the floor of a
negative one.
-/
theorem roundDyadicToInt_away (value : Numerics.Dyadic) :
    roundDyadicToInt .away value =
      if 0 ≤ value.toReal then ⌈value.toReal⌉ else ⌊value.toReal⌋ := by
  rw [roundDyadicToInt_away_by_sign]
  by_cases hsignificand : value.significand = 0
  · have hzero : value.toReal = 0 := by
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hsignificand]
    simp [roundDyadicToInt, hsignificand, hzero]
  · cases hnegative : value.negative
    · have hnonnegative := Dyadic.toReal_nonneg_of_negative_eq_false hnegative
      simp only [Bool.false_eq_true, ite_false]
      rw [ite_eq_left hnonnegative, roundDyadicToInt_up]
    · have hnegativeReal := Dyadic.toReal_lt_zero_of_negative_eq_true hnegative hsignificand
      simp only [ite_true]
      rw [ite_eq_right (not_le.mpr hnegativeReal), roundDyadicToInt_down]

/-- A dyadic with a nonnegative exponent is already an integer. -/
theorem dyadicIsIntegral_ofNat
    (negative : Bool) (significand exponent : Nat) :
    dyadicIsIntegral
      { negative, significand, exponent := Int.ofNat exponent } = true := by
  simp [dyadicIsIntegral]

/-- Dyadic zero is integral independently of its stored sign and exponent. -/
@[simp] theorem dyadicIsIntegral_zero
    (negative : Bool) (exponent : Int) :
    dyadicIsIntegral
      { negative, significand := 0, exponent } = true := by
  simp [dyadicIsIntegral]

/--
An exact dyadic is integral just when no negative binary exponent leaves a fractional bit.

For exponent `-(shift + 1)`, this says that `2^(shift + 1)` divides the significand. A
nonnegative exponent is always integral.
-/
theorem dyadicIsIntegral_iff (value : Numerics.Dyadic) :
    dyadicIsIntegral value = true ↔
      match value.exponent with
      | .ofNat _ => True
      | .negSucc shift => 2 ^ (shift + 1) ∣ value.significand := by
  rcases value with ⟨negative, significand, exponent⟩
  cases exponent with
  | ofNat exponent =>
      simp [dyadicIsIntegral]
  | negSucc shift =>
      by_cases hsignificand : significand = 0
      · simp [dyadicIsIntegral, hsignificand]
      · simp [dyadicIsIntegral, hsignificand,
          Numerics.shiftRightRemainder_eq_mod,
          Nat.dvd_iff_mod_eq_zero]

/-- Integer rounding in every direction returns the floor or the ceiling of the exact value. -/
theorem roundDyadicToInt_eq_floor_or_ceil (mode : IEEERoundingMode) (value : Numerics.Dyadic) :
    roundDyadicToInt mode value = ⌊value.toReal⌋ ∨
      roundDyadicToInt mode value = ⌈value.toReal⌉ := by
  cases mode with
  | nearest =>
      rw [roundDyadicToInt_nearest]
      exact valid_round_eq_floor_or_ceil nearestEven value.toReal
  | nearestAway =>
      rw [roundDyadicToInt_nearestAway]
      exact nearestChoice_eq_floor_or_ceil nearestAwayChoice value.toReal
  | towardZero =>
      rw [roundDyadicToInt_towardZero]
      split_ifs <;> simp
  | up => exact Or.inr (roundDyadicToInt_up value)
  | down => exact Or.inl (roundDyadicToInt_down value)
  | away =>
      rw [roundDyadicToInt_away]
      split_ifs <;> simp

/-- Every rounding direction lands at or above the floor of the exact value. -/
theorem floor_le_roundDyadicToInt (mode : IEEERoundingMode) (value : Numerics.Dyadic) :
    ⌊value.toReal⌋ ≤ roundDyadicToInt mode value := by
  rcases roundDyadicToInt_eq_floor_or_ceil mode value with h | h <;> rw [h]
  exact Int.floor_le_ceil _

/-- Every rounding direction lands at or below the ceiling of the exact value. -/
theorem roundDyadicToInt_le_ceil (mode : IEEERoundingMode) (value : Numerics.Dyadic) :
    roundDyadicToInt mode value ≤ ⌈value.toReal⌉ := by
  rcases roundDyadicToInt_eq_floor_or_ceil mode value with h | h <;> rw [h]
  exact Int.floor_le_ceil _

/-- Truncation toward zero cannot increase the magnitude of an exact dyadic. -/
theorem abs_roundDyadicToInt_towardZero_le (value : Numerics.Dyadic) :
    |((roundDyadicToInt .towardZero value : Int) : ℝ)| ≤ |value.toReal| := by
  rw [roundDyadicToInt_towardZero]
  by_cases hv : 0 ≤ value.toReal
  · rw [ite_eq_left hv, abs_of_nonneg hv, abs_of_nonneg]
    · exact Int.floor_le _
    · exact_mod_cast Int.floor_nonneg.mpr hv
  · have hv0 : value.toReal ≤ 0 := (not_le.mp hv).le
    rw [ite_eq_right hv, abs_of_nonpos hv0, abs_of_nonpos]
    · exact neg_le_neg (Int.le_ceil _)
    · exact_mod_cast Int.ceil_nonpos.mpr hv0

end Model
end FloatLib.Floats.Formats.BinaryInterchange
