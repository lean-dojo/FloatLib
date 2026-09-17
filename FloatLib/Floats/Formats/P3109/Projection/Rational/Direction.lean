/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Rational.Semantics

/-!
# Deterministic rational precision-rounding guarantees

These results derive direction, error bounds, and tie selection from the proved rational
formula. They hold before saturation, whose overflow behavior is deliberately separate.
The common quantum-level results apply to both P3109 descriptors and external binary formats.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.RationalRounding

/-- The report fractional part of a nonnegative scaled magnitude lies in `[0, 1)`. -/
theorem fraction_bounds (scaled : Rat) (hnonneg : 0 ≤ scaled) :
    0 ≤ scaled - ⌊scaled⌋₊ ∧ scaled - ⌊scaled⌋₊ < 1 := by
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one scaled
  constructor <;> linarith

/-- Every mode selects one of the adjacent integer candidates. -/
theorem roundedInteger_bounds (mode : RoundingMode) (negative : Bool) (parity : Nat → Bool)
    (scaled : Rat) :
    ⌊scaled⌋₊ ≤ roundedInteger mode negative parity scaled ∧
      roundedInteger mode negative parity scaled ≤ ⌊scaled⌋₊ + 1 := by
  dsimp only [roundedInteger]
  split <;> omega

/-- Exact integers are preserved for every mode, including every stochastic word. -/
theorem roundedInteger_natCast (mode : RoundingMode) (negative : Bool) (parity : Nat → Bool)
    (value : Nat) :
    roundedInteger mode negative parity value = value := by
  simp [roundedInteger]

/-- Every selected integer is less than one unit from the input, even for stochastic modes. -/
theorem roundedInteger_error_lt_one (mode : RoundingMode) (negative : Bool)
    (parity : Nat → Bool) (scaled : Rat) (hnonneg : 0 ≤ scaled) :
    |(roundedInteger mode negative parity scaled : Rat) - scaled| < 1 := by
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one scaled
  by_cases hz : scaled - (⌊scaled⌋₊ : Rat) = 0
  · simp only [roundedInteger, hz, roundAway_zero, Bool.false_eq_true, ite_false]
    rw [abs_lt]
    constructor <;> linarith
  · have hpos : (⌊scaled⌋₊ : Rat) < scaled := by
      apply lt_of_le_of_ne hlo
      intro heq
      apply hz
      linarith
    dsimp only [roundedInteger]
    split_ifs <;> push_cast <;> rw [abs_lt] <;> constructor <;> linarith

/-- Truncation is the lower integer candidate. -/
theorem roundedInteger_towardZero (negative : Bool) (parity : Nat → Bool) (scaled : Rat) :
    roundedInteger .towardZero negative parity scaled = ⌊scaled⌋₊ := by
  simp [roundedInteger, roundAway]

/-- Rounding up in magnitude brackets a nonnegative input within one integer unit. -/
theorem roundedInteger_up (parity : Nat → Bool) (scaled : Rat) (hnonneg : 0 ≤ scaled) :
    scaled ≤ (roundedInteger .towardPositive false parity scaled : Rat) ∧
      (roundedInteger .towardPositive false parity scaled : Rat) < scaled + 1 := by
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one scaled
  simp only [roundedInteger, roundAway, Bool.not_false, Bool.and_true, decide_eq_true_eq]
  split_ifs <;> push_cast <;> constructor <;> linarith

/-- The nearest-away candidate is at most one half-unit from the exact scaled value. -/
theorem roundedInteger_nearestTiesToAway_error (negative : Bool) (parity : Nat → Bool)
    (scaled : Rat) (hnonneg : 0 ≤ scaled) :
    |(roundedInteger .nearestTiesToAway negative parity scaled : Rat) - scaled| ≤ 1 / 2 := by
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one scaled
  simp only [roundedInteger, roundAway, decide_eq_true_eq]
  split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- The nearest-even candidate is at most one half-unit away, for either lower-code parity. -/
theorem roundedInteger_nearestTiesToEven_error (negative : Bool) (parity : Nat → Bool)
    (scaled : Rat) (hnonneg : 0 ≤ scaled) :
    |(roundedInteger .nearestTiesToEven negative parity scaled : Rat) - scaled| ≤ 1 / 2 := by
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one scaled
  cases hp : parity ⌊scaled⌋₊
  · simp only [roundedInteger, roundAway, hp, Bool.not_false, Bool.and_true,
      Bool.or_eq_true, decide_eq_true_eq]
    simp only [eq_comm (a := scaled - (⌊scaled⌋₊ : Rat)) (b := 1 / 2), ← le_iff_lt_or_eq]
    split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith
  · simp only [roundedInteger, roundAway, hp, Bool.not_true, Bool.and_false,
      Bool.or_false, decide_eq_true_eq]
    split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- On a halfway input, nearest-away selects the greater magnitude. -/
theorem roundedInteger_nearestTiesToAway_tie (negative : Bool) (parity : Nat → Bool)
    (scaled : Rat) (htie : scaled - ⌊scaled⌋₊ = 1 / 2) :
    roundedInteger .nearestTiesToAway negative parity scaled = ⌊scaled⌋₊ + 1 := by
  simp [roundedInteger, roundAway, htie]

/-- On a halfway input, nearest-even selects the lower candidate precisely when its code is even. -/
theorem roundedInteger_nearestTiesToEven_tie (negative : Bool) (parity : Nat → Bool)
    (scaled : Rat) (htie : scaled - ⌊scaled⌋₊ = 1 / 2) :
    roundedInteger .nearestTiesToEven negative parity scaled =
      if parity ⌊scaled⌋₊ then ⌊scaled⌋₊ else ⌊scaled⌋₊ + 1 := by
  cases hp : parity ⌊scaled⌋₊ <;> simp [roundedInteger, roundAway, htie, hp]

/-- With significand parity, the selected halfway candidate is an even integer. -/
theorem roundedInteger_nearestTiesToEven_tie_even (negative : Bool) (scaled : Rat)
    (htie : scaled - ⌊scaled⌋₊ = 1 / 2) :
    roundedInteger .nearestTiesToEven negative (fun lower => decide (lower % 2 = 0))
        scaled % 2 = 0 := by
  rw [roundedInteger_nearestTiesToEven_tie _ _ _ htie]
  simp only [decide_eq_true_eq]
  split_ifs <;> omega

/-- With significand parity, inexact round-to-odd selects an odd integer. -/
theorem roundedInteger_toOdd_odd (negative : Bool) (scaled : Rat)
    (hinexact : 0 < scaled - ⌊scaled⌋₊) :
    roundedInteger .toOdd negative (fun lower => decide (lower % 2 = 0)) scaled % 2 = 1 := by
  simp only [roundedInteger, roundAway, hinexact, decide_true, Bool.true_and, decide_eq_true_eq]
  split_ifs <;> omega

/-- The scaled magnitude is nonnegative at every quantum. -/
theorem scaledMagnitude_nonneg (value : Rat) (quantum : Int) :
    0 ≤ scaledMagnitude value quantum :=
  mul_nonneg (abs_nonneg value) (le_of_lt (zpow_pos (by norm_num) _))

/-- Restoring the quantum recovers the exact input magnitude. -/
theorem scaledMagnitude_mul_quantum (value : Rat) (quantum : Int) :
    scaledMagnitude value quantum * (2 : Rat) ^ quantum = |value| := by
  rw [scaledMagnitude, zpow_neg, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]

/-- Applying a sign does not change absolute magnitude. -/
theorem abs_signed (negative : Bool) (value : Rat) : |signed negative value| = |value| := by
  cases negative <;> simp [signed]

/-- Error in the scaled integer is converted to value error by the positive quantum. -/
theorem roundAt_error (mode : RoundingMode) (quantum : Int) (parity : Nat → Bool) (value : Rat) :
    |roundAt mode quantum parity value - value| =
      |(roundedInteger mode (value.num < 0) parity (scaledMagnitude value quantum) : Rat) -
        scaledMagnitude value quantum| * (2 : Rat) ^ quantum := by
  have hx : value = signed (value.num < 0)
      (scaledMagnitude value quantum * (2 : Rat) ^ quantum) := by
    rw [scaledMagnitude_mul_quantum, signed_abs]
  conv_lhs => arg 1; arg 2; rw [hx]
  unfold roundAt
  cases hn : decide (value.num < 0) <;>
    simp only [signed, Bool.false_eq_true, ite_false, ite_true]
  · rw [← sub_mul, abs_mul,
      abs_of_pos (zpow_pos (by norm_num : (0 : Rat) < 2) quantum)]
  · rw [neg_sub_neg, ← sub_mul, abs_sub_comm, abs_mul,
      abs_of_pos (zpow_pos (by norm_num : (0 : Rat) < 2) quantum)]

/-- Every mode stays within one quantum before saturation, for every supplied stochastic word. -/
theorem roundAt_error_lt_quantum (mode : RoundingMode) (quantum : Int) (parity : Nat → Bool)
    (value : Rat) :
    |roundAt mode quantum parity value - value| < (2 : Rat) ^ quantum := by
  rw [roundAt_error]
  simpa using mul_lt_mul_of_pos_right
    (roundedInteger_error_lt_one mode (value.num < 0) parity _
      (scaledMagnitude_nonneg value quantum))
    (zpow_pos (by norm_num : (0 : Rat) < 2) quantum)

/-- Nearest-away rounding has error at most half the chosen quantum. -/
theorem roundAt_nearestTiesToAway_error (quantum : Int) (parity : Nat → Bool) (value : Rat) :
    |roundAt .nearestTiesToAway quantum parity value - value| ≤ (2 : Rat) ^ quantum / 2 := by
  rw [roundAt_error]
  have h := mul_le_mul_of_nonneg_right
    (roundedInteger_nearestTiesToAway_error (value.num < 0) parity _
      (scaledMagnitude_nonneg value quantum))
    (le_of_lt (zpow_pos (by norm_num : (0 : Rat) < 2) quantum))
  linarith

/-- Nearest-even rounding has error at most half the chosen quantum, including precision one. -/
theorem roundAt_nearestTiesToEven_error (quantum : Int) (parity : Nat → Bool) (value : Rat) :
    |roundAt .nearestTiesToEven quantum parity value - value| ≤ (2 : Rat) ^ quantum / 2 := by
  rw [roundAt_error]
  have h := mul_le_mul_of_nonneg_right
    (roundedInteger_nearestTiesToEven_error (value.num < 0) parity _
      (scaledMagnitude_nonneg value quantum))
    (le_of_lt (zpow_pos (by norm_num : (0 : Rat) < 2) quantum))
  linarith

/-- Truncation reduces magnitude by less than one quantum. -/
theorem roundAt_towardZero (quantum : Int) (parity : Nat → Bool) (value : Rat) :
    |roundAt .towardZero quantum parity value| ≤ |value| ∧
      |value| < |roundAt .towardZero quantum parity value| + (2 : Rat) ^ quantum := by
  have hs := scaledMagnitude_nonneg value quantum
  have hu : (0 : Rat) < 2 ^ quantum := zpow_pos (by norm_num) _
  have hlo := mul_le_mul_of_nonneg_right (Nat.floor_le hs) hu.le
  have hhi := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (scaledMagnitude value quantum)) hu
  rw [scaledMagnitude_mul_quantum] at hlo hhi
  simp only [roundAt, roundedInteger_towardZero, abs_signed,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hu.le)]
  constructor <;> nlinarith

/-- Directed rounding toward positive infinity brackets the input from above. -/
theorem roundAt_towardPositive (quantum : Int) (parity : Nat → Bool) (value : Rat) :
    value ≤ roundAt .towardPositive quantum parity value ∧
      roundAt .towardPositive quantum parity value < value + (2 : Rat) ^ quantum := by
  have hs := scaledMagnitude_nonneg value quantum
  have hu : (0 : Rat) < 2 ^ quantum := zpow_pos (by norm_num) _
  have hlo := mul_le_mul_of_nonneg_right (Nat.floor_le hs) hu.le
  have hhi := mul_lt_mul_of_pos_right
    (Nat.lt_floor_add_one (scaledMagnitude value quantum)) hu
  have hup := roundedInteger_up parity (scaledMagnitude value quantum) hs
  have hupLo := mul_le_mul_of_nonneg_right hup.1 hu.le
  have hupHi := mul_lt_mul_of_pos_right hup.2 hu
  have hx := signed_abs value
  rw [← scaledMagnitude_mul_quantum value quantum] at hx
  cases hn : decide (value.num < 0)
  · simp only [hn, signed, Bool.false_eq_true, ite_false] at hx
    simp only [roundAt, hn, signed, Bool.false_eq_true, ite_false]
    constructor <;> nlinarith
  · have hdown :
        roundedInteger .towardPositive true parity (scaledMagnitude value quantum) =
          ⌊scaledMagnitude value quantum⌋₊ := by
      simp [roundedInteger, roundAway]
    simp only [hn, signed, ite_true] at hx
    simp only [roundAt, hn, hdown, signed, ite_true]
    constructor <;> nlinarith

/-- Directed rounding toward negative infinity brackets the input from below. -/
theorem roundAt_towardNegative (quantum : Int) (parity : Nat → Bool) (value : Rat) :
    roundAt .towardNegative quantum parity value ≤ value ∧
      value < roundAt .towardNegative quantum parity value + (2 : Rat) ^ quantum := by
  have hs := scaledMagnitude_nonneg value quantum
  have hu : (0 : Rat) < 2 ^ quantum := zpow_pos (by norm_num) _
  have hlo := mul_le_mul_of_nonneg_right (Nat.floor_le hs) hu.le
  have hhi := mul_lt_mul_of_pos_right
    (Nat.lt_floor_add_one (scaledMagnitude value quantum)) hu
  have hup := roundedInteger_up parity (scaledMagnitude value quantum) hs
  have hupLo := mul_le_mul_of_nonneg_right hup.1 hu.le
  have hupHi := mul_lt_mul_of_pos_right hup.2 hu
  have hx := signed_abs value
  rw [← scaledMagnitude_mul_quantum value quantum] at hx
  cases hn : decide (value.num < 0)
  · have hdown :
        roundedInteger .towardNegative false parity (scaledMagnitude value quantum) =
          ⌊scaledMagnitude value quantum⌋₊ := by
      simp [roundedInteger, roundAway]
    simp only [hn, signed, Bool.false_eq_true, ite_false] at hx
    simp only [roundAt, hn, hdown, signed, Bool.false_eq_true, ite_false]
    constructor <;> nlinarith
  · have hup' :
        roundedInteger .towardNegative true parity (scaledMagnitude value quantum) =
          roundedInteger .towardPositive false parity (scaledMagnitude value quantum) := rfl
    simp only [hn, signed, ite_true] at hx
    simp only [roundAt, hn, hup', signed, ite_true]
    constructor <;> nlinarith

/-- The halfway value is resolved by code parity, with the original sign restored. -/
theorem roundAt_nearestTiesToEven_tie (quantum : Int) (parity : Nat → Bool) (value : Rat)
    (htie : scaledMagnitude value quantum - ⌊scaledMagnitude value quantum⌋₊ = 1 / 2) :
    roundAt .nearestTiesToEven quantum parity value =
      signed (value.num < 0)
        (((if parity ⌊scaledMagnitude value quantum⌋₊
            then ⌊scaledMagnitude value quantum⌋₊
            else ⌊scaledMagnitude value quantum⌋₊ + 1 : Nat) : Rat) * (2 : Rat) ^ quantum) := by
  unfold roundAt
  rw [roundedInteger_nearestTiesToEven_tie _ _ _ htie]

/-- The report's precision-one parity uses the zero code or the biased exponent. -/
theorem codeEven_one (bias : Nat) (quantum : Int) (lower : Nat) :
    codeEven 1 bias quantum lower = decide (lower = 0 ∨ (quantum + (bias : Int)) % 2 = 0) := by
  simp [codeEven]

/-- At greater precision, report parity is ordinary integer significand parity. -/
theorem codeEven_of_one_lt (precision bias : Nat) (quantum : Int) (lower : Nat)
    (hprecision : 1 < precision) :
    codeEven precision bias quantum lower = decide (lower % 2 = 0) := by
  simp [codeEven, hprecision]

end RationalRounding

namespace Format

/-- All rational modes, including each stochastic word, stay within one precision quantum. -/
theorem roundFiniteRatToPrecision_error_lt_quantum (format : Format) (mode : RoundingMode)
    (value : Rat) :
    |(format.roundFiniteRatToPrecision mode value).toRat - value| <
      (2 : Rat) ^ RationalRounding.quantum format.precision format.exponentBias value := by
  rw [roundFiniteRatToPrecision_toRat]
  exact RationalRounding.roundAt_error_lt_quantum _ _ _ _

/-- Rational rounding toward positive infinity lies above the exact input. -/
theorem roundFiniteRatToPrecision_towardPositive (format : Format) (value : Rat) :
    value ≤ (format.roundFiniteRatToPrecision .towardPositive value).toRat ∧
      (format.roundFiniteRatToPrecision .towardPositive value).toRat <
        value +
          (2 : Rat) ^ RationalRounding.quantum format.precision format.exponentBias value := by
  rw [roundFiniteRatToPrecision_toRat]
  exact RationalRounding.roundAt_towardPositive _ _ _

/-- Rational rounding toward negative infinity lies below the exact input. -/
theorem roundFiniteRatToPrecision_towardNegative (format : Format) (value : Rat) :
    (format.roundFiniteRatToPrecision .towardNegative value).toRat ≤ value ∧
      value < (format.roundFiniteRatToPrecision .towardNegative value).toRat +
        (2 : Rat) ^ RationalRounding.quantum format.precision format.exponentBias value := by
  rw [roundFiniteRatToPrecision_toRat]
  exact RationalRounding.roundAt_towardNegative _ _ _

/-- Rational nearest-away precision rounding satisfies the half-quantum bound. -/
theorem roundFiniteRatToPrecision_nearestTiesToAway_error (format : Format) (value : Rat) :
    |(format.roundFiniteRatToPrecision .nearestTiesToAway value).toRat - value| ≤
      (2 : Rat) ^ RationalRounding.quantum format.precision format.exponentBias value / 2 := by
  rw [roundFiniteRatToPrecision_toRat]
  exact RationalRounding.roundAt_nearestTiesToAway_error _ _ _

/-- Rational nearest-even precision rounding satisfies the half-quantum bound. -/
theorem roundFiniteRatToPrecision_nearestTiesToEven_error (format : Format) (value : Rat) :
    |(format.roundFiniteRatToPrecision .nearestTiesToEven value).toRat - value| ≤
      (2 : Rat) ^ RationalRounding.quantum format.precision format.exponentBias value / 2 := by
  rw [roundFiniteRatToPrecision_toRat]
  exact RationalRounding.roundAt_nearestTiesToEven_error _ _ _

/-- Rational halfway selection uses the report's code parity, including precision one. -/
theorem roundFiniteRatToPrecision_nearestTiesToEven_tie (format : Format) (value : Rat)
    (htie :
      let q := RationalRounding.quantum format.precision format.exponentBias value
      RationalRounding.scaledMagnitude value q -
        ⌊RationalRounding.scaledMagnitude value q⌋₊ = 1 / 2) :
    let q := RationalRounding.quantum format.precision format.exponentBias value
    let lower := ⌊RationalRounding.scaledMagnitude value q⌋₊
    (format.roundFiniteRatToPrecision .nearestTiesToEven value).toRat =
      RationalRounding.signed (value.num < 0)
        (((if RationalRounding.codeEven format.precision format.exponentBias q lower
            then lower else lower + 1 : Nat) : Rat) * (2 : Rat) ^ q) := by
  rw [roundFiniteRatToPrecision_toRat]
  exact RationalRounding.roundAt_nearestTiesToEven_tie _ _ _ htie

end Format
end FloatLib.Floats.Formats.P3109
