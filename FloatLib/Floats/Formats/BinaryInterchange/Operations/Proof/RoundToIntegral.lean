/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.Order.Floor.Defs
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Signed
public import FloatLib.Floats.Formats.BinaryInterchange.Model.RealSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Status.Proof
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Core
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Nearest
import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Properties
import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof

/-!
# Integral-rounding contracts

The unbounded dyadic-to-integer kernel is related to the usual nearest-even, nearest-away, floor,
ceiling, truncation, and away-from-zero semantics. The floating-point wrapper then records exactly
when fractional bits were discarded and exposes the exceptional branches.

For IEEE encodings with `fmt.fracWidth ≤ fmt.maxNormalExponent`, the selected integer is exactly
representable. This condition holds for the IEEE interchange formats. On finite inputs,
`roundToIntegral` then denotes the integer selected by the rounding direction and reports no
overflow. Truncation toward zero needs no such range
condition: its result cannot exceed the input magnitude. Nearest-away rounding is
roundToIntegralTiesToAway of IEEE 754-2019, Section 5.9, and it is Flocq's `nearestChoice` with
the tie choice `nearestAwayChoice`.

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

private theorem roundDyadicToInt_down_kernel
    (value : Numerics.Dyadic) :
    roundDyadicToInt .down value =
      roundSignedMantissaAtExponentDown value.negative
        value.significand value.exponent 0 := by
  rcases value with ⟨negative, significand, exponent⟩
  by_cases hsignificand : significand = 0
  · subst significand
    cases negative <;> cases exponent <;>
      simp [roundDyadicToInt,
        roundSignedMantissaAtExponentDown, roundMantissaAtExponentDown,
        roundMantissaAtExponentUp, Numerics.shiftRightCeil]
  · cases exponent with
    | ofNat shift =>
        cases negative <;> cases shift <;>
          simp [roundDyadicToInt, hsignificand,
            roundSignedMantissaAtExponentDown, roundMantissaAtExponentDown,
            roundMantissaAtExponentUp, Numerics.shiftRightCeil]
    | negSucc shift =>
        cases negative <;>
          simp [roundDyadicToInt, hsignificand,
            roundSignedMantissaAtExponentDown, roundMantissaAtExponentDown,
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

/-- Rounding toward negative infinity computes the mathematical floor. -/
theorem roundDyadicToInt_down
    (value : Numerics.Dyadic) :
    roundDyadicToInt .down value = ⌊value.toReal⌋ := by
  rw [roundDyadicToInt_down_kernel]
  have hsemantic :=
    floor_scaledDyadic value.negative value.significand value.exponent 0
  simpa [floorRound, Numerics.Dyadic.toReal,
    Numerics.Dyadic.signedSignificand,
    Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using hsemantic.symm

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
    · have hnonnegative : 0 ≤ value.toReal := by
        rw [Numerics.Dyadic.toReal]
        simp only [Numerics.Dyadic.signedSignificand, hnegative,
          Bool.false_eq_true, ite_false]
        have hcoefficient :
            (0 : ℝ) ≤ ((Int.ofNat value.significand : Int) : ℝ) := by
          norm_cast
          exact Int.natCast_nonneg value.significand
        exact mul_nonneg hcoefficient (bpow_pos value.exponent).le
      simp only [Bool.false_eq_true, ite_false]
      rw [ite_eq_left hnonnegative]
    · have hnegativeReal : value.toReal < 0 := by
        rw [Numerics.Dyadic.toReal]
        simp only [Numerics.Dyadic.signedSignificand, hnegative, ite_true]
        have hcoefficient :
            ((-Int.ofNat value.significand : Int) : ℝ) < 0 := by
          norm_num
          exact Nat.pos_of_ne_zero hsignificand
        exact mul_neg_of_neg_of_pos hcoefficient (bpow_pos value.exponent)
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
        ring
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
    · have hnonnegative : 0 ≤ value.toReal := by
        rw [Numerics.Dyadic.toReal]
        simp only [Numerics.Dyadic.signedSignificand, hnegative,
          Bool.false_eq_true, ite_false]
        have hcoefficient :
            (0 : ℝ) ≤ ((Int.ofNat value.significand : Int) : ℝ) := by
          norm_cast
          exact Int.natCast_nonneg value.significand
        exact mul_nonneg hcoefficient (bpow_pos value.exponent).le
      simp only [Bool.false_eq_true, ite_false]
      rw [ite_eq_left hnonnegative, roundDyadicToInt_up]
    · have hnegativeReal : value.toReal < 0 := by
        rw [Numerics.Dyadic.toReal]
        simp only [Numerics.Dyadic.signedSignificand, hnegative, ite_true]
        have hcoefficient :
            ((-Int.ofNat value.significand : Int) : ℝ) < 0 := by
          norm_num
          exact Nat.pos_of_ne_zero hsignificand
        exact mul_neg_of_neg_of_pos hcoefficient (bpow_pos value.exponent)
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
An exact dyadic is integral exactly when no negative binary exponent leaves a fractional bit.

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

/-- Integral rounding with `status := true` delivers the value of integral rounding. -/
@[simp] theorem value_roundToIntegral {fmt : FloatFormat}
    (value : Model fmt) (mode : IEEERoundingMode) :
    (roundToIntegral value mode (status := true)).value = roundToIntegral value mode :=
  rfl

/--
On finite input, `roundToIntegral` raises `inexact` exactly when a negative binary
exponent leaves at least one fractional bit.
-/
theorem roundToIntegral_inexact_iff
    {fmt : FloatFormat} (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hvalue : exactValue value = .finite exact) :
    (roundToIntegral value mode (status := true)).status.inexact = true ↔
      match exact.exponent with
      | .ofNat _ => False
      | .negSucc shift => ¬2 ^ (shift + 1) ∣ exact.significand := by
  simp only [roundToIntegral, Internal.Status.roundToIntegral, hvalue]
  cases hexponent : exact.exponent with
  | ofNat exponent =>
      have hintegral : dyadicIsIntegral exact = true :=
        (dyadicIsIntegral_iff exact).2 (by simp [hexponent])
      simp [hintegral]
  | negSucc shift =>
      have hintegral := dyadicIsIntegral_iff exact
      simp only [hexponent] at hintegral ⊢
      rw [Bool.not_eq_true']
      constructor
      · intro hfalse hdivides
        have : dyadicIsIntegral exact = true := hintegral.2 hdivides
        simp [this] at hfalse
      · intro hnotDivides
        apply Bool.eq_false_of_not_eq_true
        intro htrue
        exact hnotDivides (hintegral.1 htrue)

/--
`roundToIntegral` returns either infinity unchanged, with clear status.
-/
theorem roundToIntegral_status_of_infinity
    {fmt : FloatFormat} (value : Model fmt) (mode : IEEERoundingMode)
    (negative : Bool) (hvalue : exactValue value = .infinity negative) :
    roundToIntegral value mode (status := true) =
      { value
        status := .clear
        ternary := .eq } := by
  simp [roundToIntegral, Internal.Status.roundToIntegral, hvalue, outcomeWithInvalid]

/--
`roundToIntegral` quiets a NaN and raises `invalid` exactly when it was signaling.
-/
theorem roundToIntegral_status_of_nan
    {fmt : FloatFormat} (value : Model fmt) (mode : IEEERoundingMode)
    (negative signaling : Bool) (payload : Nat)
    (hvalue : exactValue value = .nan negative signaling payload) :
    roundToIntegral value mode (status := true) =
      { value := quietNaN value
        status := { invalid := signaling }
        ternary := .eq } := by
  cases signaling <;>
    simp [roundToIntegral, Internal.Status.roundToIntegral, hvalue, outcomeWithInvalid,
      Numerics.IEEEStatus.clear]

/-! ## Representability of the rounded integer -/

/-- Every rounding direction lands at or above the floor of the exact value. -/
theorem floor_le_roundDyadicToInt (mode : IEEERoundingMode) (value : Numerics.Dyadic) :
    ⌊value.toReal⌋ ≤ roundDyadicToInt mode value := by
  cases mode with
  | nearest =>
      rw [roundDyadicToInt_nearest]
      exact floor_le_valid_round nearestEven value.toReal
  | towardZero =>
      rw [roundDyadicToInt_towardZero]
      split_ifs
      · exact le_rfl
      · exact Int.floor_le_ceil _
  | up =>
      rw [roundDyadicToInt_up]
      exact Int.floor_le_ceil _
  | down =>
      rw [roundDyadicToInt_down]
  | nearestAway =>
      rw [roundDyadicToInt_nearestAway]
      exact (nearestChoice_bounds nearestAwayChoice value.toReal).1
  | away =>
      rw [roundDyadicToInt_away]
      split_ifs
      · exact Int.floor_le_ceil _
      · exact le_rfl

/-- Every rounding direction lands at or below the ceiling of the exact value. -/
theorem roundDyadicToInt_le_ceil (mode : IEEERoundingMode) (value : Numerics.Dyadic) :
    roundDyadicToInt mode value ≤ ⌈value.toReal⌉ := by
  cases mode with
  | nearest =>
      rw [roundDyadicToInt_nearest]
      exact valid_round_le_ceil nearestEven value.toReal
  | towardZero =>
      rw [roundDyadicToInt_towardZero]
      split_ifs
      · exact Int.floor_le_ceil _
      · exact le_rfl
  | up =>
      rw [roundDyadicToInt_up]
  | down =>
      rw [roundDyadicToInt_down]
      exact Int.floor_le_ceil _
  | nearestAway =>
      rw [roundDyadicToInt_nearestAway]
      rcases nearestChoice_eq_floor_or_ceil nearestAwayChoice value.toReal with hfloor | hceil
      · rw [hfloor]
        exact Int.floor_le_ceil _
      · rw [hceil]
  | away =>
      rw [roundDyadicToInt_away]
      split_ifs
      · exact le_rfl
      · exact Int.floor_le_ceil _

/-- A dyadic with a negative exponent and an in-precision significand is below `2^fracWidth`. -/
private theorem abs_toReal_lt_two_pow_of_exponent_neg
    (value : Numerics.Dyadic) (fracWidth : Nat)
    (hsig : value.significand < 2 ^ (fracWidth + 1)) (hexp : value.exponent < 0) :
    |value.toReal| < (2 : ℝ) ^ fracWidth := by
  rw [Dyadic.abs_toReal]
  have hb : bpow value.exponent ≤ bpow (-1) :=
    (bpow_le_bpow_iff Numerics.binaryRadix _ _).2 (by omega)
  rw [bpow_neg_one] at hb
  have hm : (value.significand : ℝ) < (2 : ℝ) ^ (fracWidth + 1) := by
    exact_mod_cast hsig
  calc
    (value.significand : ℝ) * bpow value.exponent ≤ (value.significand : ℝ) * (2 : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ < (2 : ℝ) ^ (fracWidth + 1) * (2 : ℝ)⁻¹ :=
      mul_lt_mul_of_pos_right hm (by norm_num)
    _ = (2 : ℝ) ^ fracWidth := by
      rw [pow_succ]
      field_simp

/--
If the significand is below `2^(fracWidth + 1)` and the binary exponent is negative, the rounded
integer has magnitude at most `2^fracWidth`.
-/
theorem abs_roundDyadicToInt_le_two_pow_of_exponent_neg
    (mode : IEEERoundingMode) (value : Numerics.Dyadic) (fracWidth : Nat)
    (hsig : value.significand < 2 ^ (fracWidth + 1)) (hexp : value.exponent < 0) :
    |roundDyadicToInt mode value| ≤ 2 ^ fracWidth := by
  have hreal := abs_toReal_lt_two_pow_of_exponent_neg value fracWidth hsig hexp
  have hupper : value.toReal ≤ ((2 ^ fracWidth : Int) : ℝ) := by
    push_cast
    exact (abs_lt.mp hreal).2.le
  have hlower : ((-(2 ^ fracWidth) : Int) : ℝ) ≤ value.toReal := by
    push_cast
    exact (abs_lt.mp hreal).1.le
  have hceil : roundDyadicToInt mode value ≤ 2 ^ fracWidth :=
    (roundDyadicToInt_le_ceil mode value).trans (Int.ceil_le.mpr hupper)
  have hfloor : -(2 ^ fracWidth) ≤ roundDyadicToInt mode value :=
    (Int.le_floor.mpr hlower).trans (floor_le_roundDyadicToInt mode value)
  exact abs_le.mpr ⟨hfloor, hceil⟩

/-- An integer placed at exponent zero denotes itself. -/
theorem Dyadic.toReal_ofScaledInt_zero (c : Int) :
    (Numerics.Dyadic.ofScaledInt c 0).toReal = c := by
  simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.ofScaledInt,
    Numerics.Dyadic.signedSignificand, zpow_zero, mul_one]
  by_cases hc : c < 0
  · simp [hc, Int.ofNat_natAbs_of_nonpos hc.le]
  · simp [hc, Int.natAbs_of_nonneg (not_lt.mp hc)]

/-- `2^fracWidth` is at most the largest finite value once the exponent range reaches it. -/
private theorem two_pow_fracWidth_le_toReal_posMaxFinite
    (fmt : FloatFormat) (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent) :
    (2 : ℝ) ^ fmt.fracWidth ≤ toReal (posMaxFinite fmt) := by
  rw [toReal_posMaxFinite]
  have hone : (1 : ℝ) ≤ bpow (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) := by
    rw [← bpow_zero]
    exact (bpow_le_bpow_iff Numerics.binaryRadix _ _).2 (by
      simp only [Int.ofNat_eq_natCast]
      omega)
  have hmantissa : (2 : ℝ) ^ fmt.fracWidth ≤
      ((pow2 fmt.fracWidth + fmt.maxFiniteFracField : Nat) : ℝ) := by
    rw [pow2_eq_two_pow]
    push_cast
    linarith [(Nat.cast_nonneg fmt.maxFiniteFracField : (0 : ℝ) ≤ fmt.maxFiniteFracField)]
  calc
    (2 : ℝ) ^ fmt.fracWidth = (2 : ℝ) ^ fmt.fracWidth * 1 := (mul_one _).symm
    _ ≤ ((pow2 fmt.fracWidth + fmt.maxFiniteFracField : Nat) : ℝ) *
          bpow (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) :=
      mul_le_mul hmantissa hone zero_le_one (Nat.cast_nonneg _)

-- A nonnegative stored exponent already represents an integer, independently of rounding mode.
private theorem roundDyadicToInt_of_exponent_eq_ofNat
    (mode : IEEERoundingMode) (value : Numerics.Dyadic) (k : Nat)
    (hexp : value.exponent = Int.ofNat k) :
    roundDyadicToInt mode value =
      if value.negative then -Int.ofNat (value.significand * 2 ^ k)
      else Int.ofNat (value.significand * 2 ^ k) := by
  by_cases hzero : value.significand = 0
  · simp [roundDyadicToInt, hzero]
  · simp [roundDyadicToInt, hzero, hexp, Nat.shiftLeft_eq]

-- Integral rounding preserves precision independently of the format's upper exponent bound.
private theorem roundDyadicToInt_significand
    {fmt : FloatFormat}
    (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hd : toDyadic? value = some exact) :
    ∃ m k : Nat,
      (Numerics.Dyadic.ofScaledInt (roundDyadicToInt mode exact) 0).significand = m * 2 ^ k ∧
        m < 2 ^ (fmt.fracWidth + 1) := by
  have hsig := toDyadic?_significand_lt value hd
  cases hexp : exact.exponent with
  | negSucc shift =>
      have hneg : exact.exponent < 0 := by
        rw [hexp]
        omega
      have habs := abs_roundDyadicToInt_le_two_pow_of_exponent_neg mode exact fmt.fracWidth hsig hneg
      refine ⟨(roundDyadicToInt mode exact).natAbs, 0,
        by simp [Numerics.Dyadic.ofScaledInt], ?_⟩
      have hnat : (roundDyadicToInt mode exact).natAbs ≤ 2 ^ fmt.fracWidth := by
        rw [Int.abs_eq_natAbs] at habs
        exact_mod_cast habs
      exact lt_of_le_of_lt hnat (Nat.pow_lt_pow_right (by decide) (by omega))
  | ofNat k =>
      have hvalue := roundDyadicToInt_of_exponent_eq_ofNat mode exact k hexp
      refine ⟨exact.significand, k, ?_, hsig⟩
      show (roundDyadicToInt mode exact).natAbs = exact.significand * 2 ^ k
      rw [hvalue]
      cases exact.negative
      · simp only [Bool.false_eq_true, ite_false]
        rfl
      · simp only [ite_true, Int.natAbs_neg]
        rfl

-- An integer selected from a finite IEEE value is encoded exactly once it lies in the finite range.
private theorem roundToIntegral_encoding_of_abs_le
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hd : toDyadic? value = some exact)
    (hbound : |((roundDyadicToInt mode exact : Int) : ℝ)| ≤ toReal (posMaxFinite fmt)) :
    let coefficient := roundDyadicToInt mode exact
    let rounded :=
      if coefficient == 0 then
        zero fmt exact.negative
      else
        Internal.Directed.roundDyadic fmt mode (Numerics.Dyadic.ofScaledInt coefficient 0)
    isFinite rounded = true ∧ toReal rounded = (coefficient : ℝ) ∧
      (dyadicRoundingStatus fmt mode (Numerics.Dyadic.ofScaledInt coefficient 0)
        rounded).overflow = false := by
  obtain ⟨m, k, hsig, hm⟩ := roundDyadicToInt_significand value mode exact hd
  have hexpMin : fmt.minSubnormalExponent ≤ (0 : Int) := by
    have := fmt.exponentBias_pos
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    omega
  have hc0 := Dyadic.toReal_ofScaledInt_zero (roundDyadicToInt mode exact)
  have hbound' :
      |(Numerics.Dyadic.ofScaledInt (roundDyadicToInt mode exact) 0).toReal| ≤
        toReal (posMaxFinite fmt) := by
    rw [hc0]
    exact hbound
  have hoverflow :=
    dyadicRoundingOverflows_eq_false_of_abs_toReal_le_posMaxFinite fmt mode _ hbound'
  dsimp only
  by_cases hzero : roundDyadicToInt mode exact = 0
  · have hbeq : (roundDyadicToInt mode exact == 0) = true := by
      simp [hzero]
    simp only [hbeq, ite_true]
    have hfin : isFinite (zero fmt exact.negative) = true :=
      isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt exact.negative)
    refine ⟨hfin, ?_, ?_⟩
    · rw [toReal_zero, hzero]
      simp
    · rw [dyadicRoundingStatus_overflow_of_isFinite _ _ _ hfin]
      exact hoverflow
  · have hbeq : (roundDyadicToInt mode exact == 0) = false := by
      simp [hzero]
    simp only [hbeq, Bool.false_eq_true, ite_false]
    obtain ⟨hfin, hval⟩ :=
      Internal.Directed.roundDyadic_of_eq_mul_pow2 fmt hfmt mode _ m k hsig hm
        (by simpa [Numerics.Dyadic.ofScaledInt] using hexpMin) hbound'
    refine ⟨hfin, ?_, ?_⟩
    · rw [hval, hc0]
    · rw [dyadicRoundingStatus_overflow_of_isFinite _ _ _ hfin]
      exact hoverflow

-- Once the exponent range reaches the precision, every selected integer lies in the finite range.
private theorem abs_roundDyadicToInt_le_toReal_posMaxFinite
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hd : toDyadic? value = some exact) :
    |((roundDyadicToInt mode exact : Int) : ℝ)| ≤ toReal (posMaxFinite fmt) := by
  cases hexp : exact.exponent with
  | negSucc shift =>
    have hneg : exact.exponent < 0 := by rw [hexp]; omega
    have hsig := toDyadic?_significand_lt value hd
    have hsmall := abs_roundDyadicToInt_le_two_pow_of_exponent_neg mode exact
      fmt.fracWidth hsig hneg
    have hcast : |((roundDyadicToInt mode exact : Int) : ℝ)| ≤ (2 : ℝ) ^ fmt.fracWidth := by
      exact_mod_cast hsmall
    exact hcast.trans (two_pow_fracWidth_le_toReal_posMaxFinite fmt hrange)
  | ofNat k =>
    have hrounded := roundDyadicToInt_of_exponent_eq_ofNat mode exact k hexp
    have hreal : ((roundDyadicToInt mode exact : Int) : ℝ) = exact.toReal := by
      rw [hrounded, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hexp]
      cases exact.negative <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, Int.ofNat_eq_natCast,
          zpow_natCast] <;> push_cast <;> ring
    rw [hreal, show exact.toReal = toReal value by simp [toReal_eq, hd]]
    exact abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite value hfmt
      (isFinite_eq_true_of_toDyadic?_some hd)

/--
On finite input, `roundToIntegral` rounds the exact dyadic to an unbounded integer,
then encodes that integer in the selected direction. The status records discarded fractional bits
and the encoder's overflow classification, and the ternary value compares the delivered value with
the input.
-/
theorem roundToIntegral_status_of_finite
    {fmt : FloatFormat} (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hvalue : exactValue value = .finite exact) :
    roundToIntegral value mode (status := true) =
      let coefficient := roundDyadicToInt mode exact
      let rounded :=
        if coefficient == 0 then
          zero fmt exact.negative
        else
          Internal.Directed.roundDyadic fmt mode (Numerics.Dyadic.ofScaledInt coefficient 0)
      let encodingStatus := dyadicRoundingStatus fmt mode
        (Numerics.Dyadic.ofScaledInt coefficient 0) rounded
      { value := rounded
        status := {
          overflow := encodingStatus.overflow, inexact := !dyadicIsIntegral exact }
        ternary := dyadicTernary exact rounded } := by
  by_cases hguard :
      (fmt.isIEEE && decide (fmt.fracWidth + fmt.exponentBias ≤ fmt.maxFiniteExpField)) = true
  · have hd : toDyadic? value = some exact := exactValue_eq_finite_iff.mp hvalue
    obtain ⟨hfmt, hfits⟩ :
        fmt.isIEEE = true ∧ fmt.fracWidth + fmt.exponentBias ≤ fmt.maxFiniteExpField := by
      simpa using hguard
    have hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent := by
      simp only [FloatFormat.maxNormalExponent, Int.ofNat_eq_natCast]
      omega
    have hencoding := roundToIntegral_encoding_of_abs_le hfmt value mode exact hd
      (abs_roundDyadicToInt_le_toReal_posMaxFinite hfmt hrange value mode exact hd)
    simp only [roundToIntegral, Internal.Status.roundToIntegral, hvalue, hguard, ite_true]
    rw [hencoding.2.2]
  · simp only [roundToIntegral, Internal.Status.roundToIntegral, hvalue, hguard,
    Bool.false_eq_true, ite_false, dyadicRoundingStatus_overflow]

-- Precision and range are separate: truncation supplies its range bound from the input magnitude.
private theorem roundToIntegral_finite_exact_of_abs_le
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hvalue : exactValue value = .finite exact)
    (hbound : |((roundDyadicToInt mode exact : Int) : ℝ)| ≤ toReal (posMaxFinite fmt)) :
    isFinite (roundToIntegral value mode) = true ∧
      toReal (roundToIntegral value mode) = ((roundDyadicToInt mode exact : Int) : ℝ) ∧
      (roundToIntegral value mode (status := true)).status.overflow = false := by
  rw [← value_roundToIntegral, roundToIntegral_status_of_finite value mode exact hvalue]
  exact roundToIntegral_encoding_of_abs_le hfmt value mode exact
    (exactValue_eq_finite_iff.mp hvalue) hbound

/--
On a finite input of an IEEE format whose exponent range reaches the precision, the selected
integer is represented exactly and reports no overflow. Fractional input can still set `inexact`.
The range condition holds for IEEE 754's standard binary interchange formats.
-/
theorem roundToIntegral_finite_exact
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hvalue : exactValue value = .finite exact) :
    isFinite (roundToIntegral value mode) = true ∧
      toReal (roundToIntegral value mode) = ((roundDyadicToInt mode exact : Int) : ℝ) ∧
      (roundToIntegral value mode (status := true)).status.overflow = false := by
  exact roundToIntegral_finite_exact_of_abs_le hfmt value mode exact hvalue
    (abs_roundDyadicToInt_le_toReal_posMaxFinite hfmt hrange value mode exact
      (exactValue_eq_finite_iff.mp hvalue))

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

private theorem roundToIntegral_towardZero_finite_exact
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) :
    isFinite (roundToIntegral value .towardZero) = true ∧
      toReal (roundToIntegral value .towardZero) =
        (if 0 ≤ toReal value then (⌊toReal value⌋ : ℝ) else (⌈toReal value⌉ : ℝ)) ∧
      (roundToIntegral value .towardZero (status := true)).status.overflow = false := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hx : toReal value = exact.toReal := by simp [toReal_eq, hd]
  have hbound : |((roundDyadicToInt .towardZero exact : Int) : ℝ)| ≤
      toReal (posMaxFinite fmt) := by
    apply (abs_roundDyadicToInt_towardZero_le exact).trans
    rw [← hx]
    exact abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite value hfmt hfinite
  have h := roundToIntegral_finite_exact_of_abs_le hfmt value .towardZero exact
    (exactValue_eq_finite_of_toDyadic?_eq_some hd) hbound
  refine ⟨h.1, ?_, h.2.2⟩
  rw [h.2.1, roundDyadicToInt_towardZero, ← hx]
  split_ifs <;> rfl

/-- Truncating a finite IEEE value toward zero is finite, for any exponent range. -/
theorem isFinite_roundToIntegral_towardZero
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) :
    isFinite (roundToIntegral value .towardZero) = true :=
  (roundToIntegral_towardZero_finite_exact hfmt value hfinite).1

/-- Truncation toward zero computes floor or ceiling without an exponent-range restriction. -/
theorem toReal_roundToIntegral_towardZero_of_isFinite
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .towardZero) =
      if 0 ≤ toReal value then (⌊toReal value⌋ : ℝ) else (⌈toReal value⌉ : ℝ) :=
  (roundToIntegral_towardZero_finite_exact hfmt value hfinite).2.1

/-- Truncation toward zero of a finite IEEE value never signals overflow. -/
theorem roundToIntegral_towardZero_overflow_eq_false
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) :
    (roundToIntegral value .towardZero (status := true)).status.overflow = false :=
  (roundToIntegral_towardZero_finite_exact hfmt value hfinite).2.2

/--
Integral rounding of a finite IEEE value never overflows when
`fmt.fracWidth ≤ fmt.maxNormalExponent`.
-/
theorem roundToIntegral_overflow_eq_false
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode) (hfinite : isFinite value = true) :
    (roundToIntegral value mode (status := true)).status.overflow = false := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  exact (roundToIntegral_finite_exact hfmt hrange value mode exact
    (exactValue_eq_finite_of_toDyadic?_eq_some hd)).2.2

/--
Integral rounding of a finite IEEE value is finite when the exponent range reaches the precision.
-/
theorem isFinite_roundToIntegral
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode) (hfinite : isFinite value = true) :
    isFinite (roundToIntegral value mode) = true := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  exact (roundToIntegral_finite_exact hfmt hrange value mode exact
    (exactValue_eq_finite_of_toDyadic?_eq_some hd)).1

/-- The real value of a finite integral rounding is the integer selected by `roundDyadicToInt`. -/
theorem toReal_roundToIntegral
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hd : toDyadic? value = some exact) :
    toReal (roundToIntegral value mode) = ((roundDyadicToInt mode exact : Int) : ℝ) :=
  (roundToIntegral_finite_exact hfmt hrange value mode exact
    (exactValue_eq_finite_of_toDyadic?_eq_some hd)).2.1

/-- The result of integral rounding is an integer. -/
theorem exists_int_toReal_roundToIntegral
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode) (hfinite : isFinite value = true) :
    ∃ n : Int, toReal (roundToIntegral value mode) = n := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  exact ⟨_, toReal_roundToIntegral hfmt hrange value mode exact hd⟩

/-- Rounding toward negative infinity computes the floor of the real value. -/
theorem toReal_roundToIntegral_down
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .down) = ⌊toReal value⌋ := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hx : toReal value = exact.toReal := by
    simp [toReal_eq, hd]
  rw [toReal_roundToIntegral hfmt hrange value _ exact hd,
    roundDyadicToInt_down, hx]

/-- Rounding toward positive infinity computes the ceiling of the real value. -/
theorem toReal_roundToIntegral_up
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .up) = ⌈toReal value⌉ := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hx : toReal value = exact.toReal := by
    simp [toReal_eq, hd]
  rw [toReal_roundToIntegral hfmt hrange value _ exact hd,
    roundDyadicToInt_up, hx]

/-- Rounding toward zero truncates the real value: floor when nonnegative, ceiling otherwise. -/
theorem toReal_roundToIntegral_towardZero
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .towardZero) =
      if 0 ≤ toReal value then (⌊toReal value⌋ : ℝ) else (⌈toReal value⌉ : ℝ) := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hx : toReal value = exact.toReal := by
    simp [toReal_eq, hd]
  rw [toReal_roundToIntegral hfmt hrange value _ exact hd, roundDyadicToInt_towardZero, hx]
  split_ifs <;> rfl

/--
Rounding to nearest with ties away from zero computes the nearest integer and resolves a tie toward
the integer of larger magnitude, roundToIntegralTiesToAway of IEEE 754-2019. This is Flocq's
`nearestChoice nearestAwayChoice`.
-/
theorem toReal_roundToIntegral_nearestAway
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .nearestAway) =
      nearestChoice nearestAwayChoice (toReal value) := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hx : toReal value = exact.toReal := by
    simp [toReal_eq, hd]
  rw [toReal_roundToIntegral hfmt hrange value _ exact hd, roundDyadicToInt_nearestAway, hx]

/--
Rounding away from zero computes the ceiling of a nonnegative value and the floor of a negative
one, as MPFR's `mpfr_rint` does under `MPFR_RNDA`.
-/
theorem toReal_roundToIntegral_away
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .away) =
      if 0 ≤ toReal value then (⌈toReal value⌉ : ℝ) else (⌊toReal value⌋ : ℝ) := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hx : toReal value = exact.toReal := by
    simp [toReal_eq, hd]
  rw [toReal_roundToIntegral hfmt hrange value _ exact hd, roundDyadicToInt_away, hx]
  split_ifs <;> rfl

/--
Rounding to nearest computes the nearest integer with ties to even, `nearestEven` from the Flocq
theory. Mathlib's `round` resolves ties toward positive infinity.
-/
theorem toReal_roundToIntegral_nearest
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .nearest) = nearestEven (toReal value) := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hx : toReal value = exact.toReal := by
    simp [toReal_eq, hd]
  rw [toReal_roundToIntegral hfmt hrange value _ exact hd, roundDyadicToInt_nearest, hx]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
