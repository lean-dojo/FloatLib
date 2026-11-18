/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.RoundToIntegral.Integer

import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
import FloatLib.Floats.Formats.BinaryInterchange.Status.Proof

/-!
# Encoding integral rounding with status

The floating-point wrapper records inexactness and handles infinities and NaNs. For IEEE formats
with fraction width no greater than the maximum normal exponent, every rounded finite integer is
representable and cannot overflow. Truncation toward zero needs no such range condition because
its magnitude cannot increase.

## References

* IEEE 754-2019, Sections 4.3.2 and 5.9 (directed and integral rounding).
  https://doi.org/10.1109/IEEESTD.2019.8766229
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics
open FloatLib.Floats.Formats.Flocq

/-- Integral rounding with `status := true` delivers the value of integral rounding. -/
@[simp] theorem value_roundToIntegral {fmt : FloatFormat}
    (value : Model fmt) (mode : IEEERoundingMode) :
    (roundToIntegral value mode (status := true)).value = roundToIntegral value mode :=
  rfl

/--
On finite input, `roundToIntegral` raises `inexact` just when a negative binary
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
`roundToIntegral` quiets a NaN, and raises `invalid` if and only if that NaN was signaling.
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
theorem two_pow_fracWidth_le_toReal_posMaxFinite
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
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
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
      have habs := abs_roundDyadicToInt_le_two_pow_of_exponent_neg mode exact fmt.fracWidth hsig
        hneg
      refine ⟨(roundDyadicToInt mode exact).natAbs, 0,
        by simp [Numerics.Dyadic.ofScaledInt], ?_⟩
      have hnat : (roundDyadicToInt mode exact).natAbs ≤ 2 ^ fmt.fracWidth := by
        rw [Int.abs_eq_natAbs] at habs
        exact_mod_cast habs
      exact lt_of_le_of_lt hnat (Nat.pow_lt_pow_right (by decide) (by omega))
  | ofNat k =>
      have hvalue := roundDyadicToInt_of_exponent_eq_ofNat mode exact k hexp
      refine ⟨exact.significand, k, ?_, hsig⟩
      change (roundDyadicToInt mode exact).natAbs = exact.significand * 2 ^ k
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
    {fmt : FloatFormat}
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
    rw [hreal]
    exact abs_toReal_le_posMaxFinite_of_toDyadic?_some value hd

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
      (abs_roundDyadicToInt_le_toReal_posMaxFinite hrange value mode exact hd)
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
integer is represented without rounding and no overflow is reported. A fractional input can set
`inexact` all the same. The binary interchange formats instantiated by this library meet the range
condition.
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
    (abs_roundDyadicToInt_le_toReal_posMaxFinite hrange value mode exact
      (exactValue_eq_finite_iff.mp hvalue))

/-- Truncation preserves finiteness, selects the integer toward zero, and never overflows. -/
theorem roundToIntegral_towardZero_finite_exact
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
    exact abs_toReal_le_posMaxFinite_of_isFinite value hfinite
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

/--
Truncation toward zero never signals overflow under a conventional IEEE descriptor, for any
exponent range. Infinities and NaNs are returned with no overflow flag.
-/
theorem roundToIntegral_towardZero_overflow_eq_false
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (value : Model fmt) :
    (roundToIntegral value .towardZero (status := true)).status.overflow = false := by
  cases hv : exactValue value with
  | finite exact =>
      exact (roundToIntegral_towardZero_finite_exact hfmt value
        (isFinite_eq_true_of_toDyadic?_some (exactValue_eq_finite_iff.mp hv))).2.2
  | infinity negative =>
      rw [roundToIntegral_status_of_infinity value _ negative hv]
      rfl
  | nan negative signaling payload =>
      rw [roundToIntegral_status_of_nan value _ negative signaling payload hv]

/--
Integral rounding under a conventional IEEE descriptor never overflows when
`fmt.fracWidth ≤ fmt.maxNormalExponent`. Infinities and NaNs are returned with no overflow flag.
-/
theorem roundToIntegral_overflow_eq_false
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode) :
    (roundToIntegral value mode (status := true)).status.overflow = false := by
  cases hv : exactValue value with
  | finite exact => exact (roundToIntegral_finite_exact hfmt hrange value mode exact hv).2.2
  | infinity negative =>
      rw [roundToIntegral_status_of_infinity value mode negative hv]
      rfl
  | nan negative signaling payload =>
      rw [roundToIntegral_status_of_nan value mode negative signaling payload hv]

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

end Model
end FloatLib.Floats.Formats.BinaryInterchange
