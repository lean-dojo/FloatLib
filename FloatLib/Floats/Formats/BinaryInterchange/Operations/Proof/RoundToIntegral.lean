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
import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Properties
import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof

/-!
# Integral-rounding contracts

The unbounded dyadic-to-integer kernel is related to the usual nearest-even, floor, ceiling, and
truncation semantics. The floating-point wrapper then records exactly when fractional bits were
discarded and exposes the exceptional branches.

For IEEE encodings with `fmt.fracWidth ≤ fmt.maxNormalExponent`, the selected integer is exactly
representable. This condition holds for the IEEE interchange formats. On finite inputs,
`roundToIntegral` then denotes the floor, ceiling, truncation, or nearest-even integer selected by
the rounding direction, and `roundToIntegralExactWithStatus` reports no overflow.
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

private theorem roundDyadicToInt_nearestEven_kernel
    (value : Numerics.Dyadic) :
    roundDyadicToInt .nearestEven value =
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

private theorem roundDyadicToInt_towardPositiveInfinity_kernel
    (value : Numerics.Dyadic) :
    roundDyadicToInt .towardPositiveInfinity value =
      roundSignedMantissaAtExponentUp value.negative
        value.significand value.exponent 0 := by
  rcases value with ⟨negative, significand, exponent⟩
  by_cases hsignificand : significand = 0
  · subst significand
    cases negative <;> cases exponent <;>
      simp [roundDyadicToInt,
        roundSignedMantissaAtExponentUp, roundMantissaAtExponentDown,
        roundMantissaAtExponentUp, shiftRightCeilPow2]
  · cases exponent with
    | ofNat shift =>
        cases negative <;> cases shift <;>
          simp [roundDyadicToInt, hsignificand,
            roundSignedMantissaAtExponentUp, roundMantissaAtExponentDown,
            roundMantissaAtExponentUp, shiftRightCeilPow2]
    | negSucc shift =>
        cases negative <;>
          simp [roundDyadicToInt, hsignificand,
            roundSignedMantissaAtExponentUp, roundMantissaAtExponentDown,
            roundMantissaAtExponentUp, shiftRightCeilPow2,
            shiftRightRemainder]

private theorem roundDyadicToInt_towardNegativeInfinity_kernel
    (value : Numerics.Dyadic) :
    roundDyadicToInt .towardNegativeInfinity value =
      roundSignedMantissaAtExponentDown value.negative
        value.significand value.exponent 0 := by
  rcases value with ⟨negative, significand, exponent⟩
  by_cases hsignificand : significand = 0
  · subst significand
    cases negative <;> cases exponent <;>
      simp [roundDyadicToInt,
        roundSignedMantissaAtExponentDown, roundMantissaAtExponentDown,
        roundMantissaAtExponentUp, shiftRightCeilPow2]
  · cases exponent with
    | ofNat shift =>
        cases negative <;> cases shift <;>
          simp [roundDyadicToInt, hsignificand,
            roundSignedMantissaAtExponentDown, roundMantissaAtExponentDown,
            roundMantissaAtExponentUp, shiftRightCeilPow2]
    | negSucc shift =>
        cases negative <;>
          simp [roundDyadicToInt, hsignificand,
            roundSignedMantissaAtExponentDown, roundMantissaAtExponentDown,
            roundMantissaAtExponentUp, shiftRightCeilPow2,
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
theorem roundDyadicToInt_nearestEven (value : Numerics.Dyadic) :
    roundDyadicToInt .nearestEven value = nearestEven value.toReal := by
  rw [roundDyadicToInt_nearestEven_kernel]
  have hsemantic :=
    nearestEven_scaledDyadic value.negative value.significand
      value.exponent 0
  simpa [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
    Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
    hsemantic.symm

/-- Rounding toward positive infinity computes the mathematical ceiling. -/
theorem roundDyadicToInt_towardPositiveInfinity
    (value : Numerics.Dyadic) :
    roundDyadicToInt .towardPositiveInfinity value = ⌈value.toReal⌉ := by
  rw [roundDyadicToInt_towardPositiveInfinity_kernel]
  have hsemantic :=
    ceil_scaledDyadic value.negative value.significand value.exponent 0
  simpa [ceilRound, Numerics.Dyadic.toReal,
    Numerics.Dyadic.signedSignificand,
    Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using hsemantic.symm

/-- Rounding toward negative infinity computes the mathematical floor. -/
theorem roundDyadicToInt_towardNegativeInfinity
    (value : Numerics.Dyadic) :
    roundDyadicToInt .towardNegativeInfinity value = ⌊value.toReal⌋ := by
  rw [roundDyadicToInt_towardNegativeInfinity_kernel]
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
An exact dyadic is integral precisely when no negative binary exponent leaves a fractional bit.

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

/-- `roundToIntegral` is exactly the value component of its status-bearing operation. -/
@[simp] theorem roundToIntegral_eq_value {fmt : FloatFormat}
    (value : Model fmt) (mode : IEEERoundingMode) :
    roundToIntegral value mode = (roundToIntegralExactWithStatus value mode).value :=
  rfl

/--
On finite input, `roundToIntegralExactWithStatus` rounds the exact dyadic to an unbounded integer,
then encodes that integer in the selected direction. The status records discarded fractional bits
and the encoder's overflow classification.
-/
theorem roundToIntegralExactWithStatus_of_finite
    {fmt : FloatFormat} (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hvalue : exactValue value = .finite exact) :
    roundToIntegralExactWithStatus value mode =
      let coefficient := roundDyadicToInt mode exact
      let rounded :=
        if coefficient == 0 then
          zero fmt exact.negative
        else
          roundDyadicWithRounding fmt mode (Numerics.Dyadic.ofScaledInt coefficient 0)
      let encodingStatus := dyadicRoundingStatus fmt mode
        (Numerics.Dyadic.ofScaledInt coefficient 0) rounded
      { value := rounded
        status := {
          overflow := encodingStatus.overflow, inexact := !dyadicIsIntegral exact } } := by
  simp [roundToIntegralExactWithStatus, hvalue]

/--
On finite input, `roundToIntegralExactWithStatus` raises `inexact` exactly when a negative binary
exponent leaves at least one fractional bit.
-/
theorem roundToIntegralExactWithStatus_inexact_iff
    {fmt : FloatFormat} (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hvalue : exactValue value = .finite exact) :
    (roundToIntegralExactWithStatus value mode).status.inexact = true ↔
      match exact.exponent with
      | .ofNat _ => False
      | .negSucc shift => ¬2 ^ (shift + 1) ∣ exact.significand := by
  simp only [roundToIntegralExactWithStatus, hvalue]
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

/-- `roundToIntegralExactWithStatus` preserves either infinity and returns clear status. -/
theorem roundToIntegralExactWithStatus_of_infinity
    {fmt : FloatFormat} (value : Model fmt) (mode : IEEERoundingMode)
    (negative : Bool) (hvalue : exactValue value = .infinity negative) :
    roundToIntegralExactWithStatus value mode =
      { value
        status := .clear } := by
  simp [roundToIntegralExactWithStatus, hvalue, outcomeWithInvalid]

/--
`roundToIntegralExactWithStatus` quiets a NaN and raises `invalid` exactly when it was signaling.
-/
theorem roundToIntegralExactWithStatus_of_nan
    {fmt : FloatFormat} (value : Model fmt) (mode : IEEERoundingMode)
    (negative signaling : Bool) (payload : Nat)
    (hvalue : exactValue value = .nan negative signaling payload) :
    roundToIntegralExactWithStatus value mode =
      { value := quietNaN value
        status := { invalid := signaling } } := by
  cases signaling <;>
    simp [roundToIntegralExactWithStatus, hvalue, outcomeWithInvalid, IEEEStatus.clear]

/-! ## Representability of the rounded integer -/

/-- Every rounding direction lands at or above the floor of the exact value. -/
theorem floor_le_roundDyadicToInt (mode : IEEERoundingMode) (value : Numerics.Dyadic) :
    ⌊value.toReal⌋ ≤ roundDyadicToInt mode value := by
  cases mode with
  | nearestEven =>
      rw [roundDyadicToInt_nearestEven]
      exact floor_le_valid_round nearestEven value.toReal
  | towardZero =>
      rw [roundDyadicToInt_towardZero]
      split_ifs
      · exact le_rfl
      · exact Int.floor_le_ceil _
  | towardPositiveInfinity =>
      rw [roundDyadicToInt_towardPositiveInfinity]
      exact Int.floor_le_ceil _
  | towardNegativeInfinity =>
      rw [roundDyadicToInt_towardNegativeInfinity]

/-- Every rounding direction lands at or below the ceiling of the exact value. -/
theorem roundDyadicToInt_le_ceil (mode : IEEERoundingMode) (value : Numerics.Dyadic) :
    roundDyadicToInt mode value ≤ ⌈value.toReal⌉ := by
  cases mode with
  | nearestEven =>
      rw [roundDyadicToInt_nearestEven]
      exact valid_round_le_ceil nearestEven value.toReal
  | towardZero =>
      rw [roundDyadicToInt_towardZero]
      split_ifs
      · exact Int.floor_le_ceil _
      · exact le_rfl
  | towardPositiveInfinity =>
      rw [roundDyadicToInt_towardPositiveInfinity]
  | towardNegativeInfinity =>
      rw [roundDyadicToInt_towardNegativeInfinity]
      exact Int.floor_le_ceil _

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

/--
When the exponent range reaches `fracWidth`, rounding a finite IEEE value to an integer stays
within range. A nonnegative stored exponent already represents an integer; a negative exponent
gives a rounded magnitude at most `2^fracWidth`. In both cases that magnitude is `m * 2^k` with
`m` fitting the significand precision.
-/
private theorem roundDyadicToInt_representable
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hd : toDyadic? value = some exact) :
    ∃ m k : Nat,
      (Numerics.Dyadic.ofScaledInt (roundDyadicToInt mode exact) 0).significand = m * 2 ^ k ∧
        m < 2 ^ (fmt.fracWidth + 1) ∧
        |((roundDyadicToInt mode exact : Int) : ℝ)| ≤ toReal (posMaxFinite fmt) := by
  have hsig := toDyadic?_significand_lt value hd
  have hfin : isFinite value = true := isFinite_eq_true_of_toDyadic?_some hd
  have hx : toReal value = exact.toReal := by
    simp [toReal_eq, hd]
  have hxbound : |exact.toReal| ≤ toReal (posMaxFinite fmt) := by
    rw [← hx]
    exact abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite value hfmt hfin
  cases hexp : exact.exponent with
  | negSucc shift =>
      have hneg : exact.exponent < 0 := by
        rw [hexp]
        omega
      have habs := abs_roundDyadicToInt_le_two_pow_of_exponent_neg mode exact fmt.fracWidth hsig hneg
      refine ⟨(roundDyadicToInt mode exact).natAbs, 0, by simp [Numerics.Dyadic.ofScaledInt], ?_, ?_⟩
      · have hnat : (roundDyadicToInt mode exact).natAbs ≤ 2 ^ fmt.fracWidth := by
          have := habs
          rw [Int.abs_eq_natAbs] at this
          exact_mod_cast this
        exact lt_of_le_of_lt hnat (Nat.pow_lt_pow_right (by decide) (by omega))
      · have hcast : |((roundDyadicToInt mode exact : Int) : ℝ)| ≤ (2 : ℝ) ^ fmt.fracWidth := by
          have := habs
          exact_mod_cast this
        exact hcast.trans (two_pow_fracWidth_le_toReal_posMaxFinite fmt hrange)
  | ofNat k =>
      have hvalue :
          roundDyadicToInt mode exact =
            if exact.negative then -Int.ofNat (exact.significand * 2 ^ k)
            else Int.ofNat (exact.significand * 2 ^ k) := by
        by_cases hzero : exact.significand = 0
        · simp [roundDyadicToInt, hzero]
        · simp [roundDyadicToInt, hzero, hexp, Nat.shiftLeft_eq]
      have hreal : ((roundDyadicToInt mode exact : Int) : ℝ) = exact.toReal := by
        rw [hvalue, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hexp]
        cases exact.negative <;>
          simp only [Bool.false_eq_true, ite_false, ite_true, Int.ofNat_eq_natCast,
            zpow_natCast] <;>
          push_cast <;> ring
      refine ⟨exact.significand, k, ?_, hsig, by rw [hreal]; exact hxbound⟩
      show (roundDyadicToInt mode exact).natAbs = exact.significand * 2 ^ k
      rw [hvalue]
      cases exact.negative
      · simp only [Bool.false_eq_true, ite_false]
        rfl
      · simp only [ite_true, Int.natAbs_neg]
        rfl

/--
On a finite input of an IEEE format whose exponent range reaches the precision, the result
represents the selected integer exactly and reports no overflow. Fractional input can still set
`inexact`.

Every IEEE interchange format satisfies `fmt.fracWidth ≤ fmt.maxNormalExponent`.
-/
theorem roundToIntegralExactWithStatus_finite_exact
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hvalue : exactValue value = .finite exact) :
    isFinite (roundToIntegral value mode) = true ∧
      toReal (roundToIntegral value mode) = ((roundDyadicToInt mode exact : Int) : ℝ) ∧
      (roundToIntegralExactWithStatus value mode).status.overflow = false := by
  have hd : toDyadic? value = some exact := exactValue_eq_finite_iff.mp hvalue
  obtain ⟨m, k, hsig, hm, hbound⟩ := roundDyadicToInt_representable hfmt hrange value mode exact hd
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
  rw [roundToIntegral_eq_value, roundToIntegralExactWithStatus_of_finite value mode exact hvalue]
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
      roundDyadicWithRounding_of_eq_mul_pow2 fmt hfmt mode _ m k hsig hm
        (by simpa [Numerics.Dyadic.ofScaledInt] using hexpMin) hbound'
    refine ⟨hfin, ?_, ?_⟩
    · rw [hval, hc0]
    · rw [dyadicRoundingStatus_overflow_of_isFinite _ _ _ hfin]
      exact hoverflow

/-- For IEEE formats whose exponent range reaches the precision, integral rounding never overflows. -/
theorem roundToIntegralExactWithStatus_overflow_eq_false
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode) (hfinite : isFinite value = true) :
    (roundToIntegralExactWithStatus value mode).status.overflow = false := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  exact (roundToIntegralExactWithStatus_finite_exact hfmt hrange value mode exact
    (exactValue_eq_finite_of_toDyadic?_eq_some hd)).2.2

/-- Integral rounding of a finite IEEE value is finite when the exponent range reaches the precision. -/
theorem isFinite_roundToIntegral
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode) (hfinite : isFinite value = true) :
    isFinite (roundToIntegral value mode) = true := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  exact (roundToIntegralExactWithStatus_finite_exact hfmt hrange value mode exact
    (exactValue_eq_finite_of_toDyadic?_eq_some hd)).1

/-- The real value of a finite integral rounding is the integer selected by `roundDyadicToInt`. -/
theorem toReal_roundToIntegral
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hd : toDyadic? value = some exact) :
    toReal (roundToIntegral value mode) = ((roundDyadicToInt mode exact : Int) : ℝ) :=
  (roundToIntegralExactWithStatus_finite_exact hfmt hrange value mode exact
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
theorem toReal_roundToIntegral_towardNegativeInfinity
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .towardNegativeInfinity) = ⌊toReal value⌋ := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hx : toReal value = exact.toReal := by
    simp [toReal_eq, hd]
  rw [toReal_roundToIntegral hfmt hrange value _ exact hd,
    roundDyadicToInt_towardNegativeInfinity, hx]

/-- Rounding toward positive infinity computes the ceiling of the real value. -/
theorem toReal_roundToIntegral_towardPositiveInfinity
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .towardPositiveInfinity) = ⌈toReal value⌉ := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hx : toReal value = exact.toReal := by
    simp [toReal_eq, hd]
  rw [toReal_roundToIntegral hfmt hrange value _ exact hd,
    roundDyadicToInt_towardPositiveInfinity, hx]

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
Rounding to nearest computes the nearest integer with ties to even, `nearestEven` from the Flocq
theory. Mathlib's `round` resolves ties toward positive infinity.
-/
theorem toReal_roundToIntegral_nearestEven
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .nearestEven) = nearestEven (toReal value) := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hx : toReal value = exact.toReal := by
    simp [toReal_eq, hd]
  rw [toReal_roundToIntegral hfmt hrange value _ exact hd, roundDyadicToInt_nearestEven, hx]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
