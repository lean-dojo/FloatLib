/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Subtraction
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.NonNaN

import FloatLib.Floats.Formats.Flocq.Calculation.Round
import Mathlib.Algebra.Order.Floor.Ring

/-!
# An operation in a rounding attribute is one rounding of the exact result

`Arithmetic.Semantics` states a finite nearest-even sum, difference, product or fused
multiply-add as the nearest-even rounding of the exact real result. This module states the same
for every rounding attribute: the four directed ones, `towardZero`, `up`, `down` and `away`, and
`nearestAway`.

A directed rounding saturates: a sum above the largest finite value rounds downward to that
value, which is finite and far from the exact sum. So the premise is not that the result is
finite. It is that the exact result is within the largest finite magnitude, and then the result
is finite too.

* `Internal.Directed.roundDyadic_finite_roundAt`: a rounding of an exact dyadic within the
  largest finite magnitude is finite and equals `roundAt` of its real value, in each of the six
  attributes.
* `fract_scaledMantissa_eq_half_iff`: the tie test that `nearestAway` runs on the bits of a
  dyadic (`dyadicIsGridTie`) holds exactly when its scaled mantissa is halfway between two
  integers. Off such a tie `nearestAway` is nearest-even rounding, and at one it is rounding
  away from zero (`roundDyadicNearestAway_finite_roundAt`).
* `add_finite_roundAt`, `sub_finite_roundAt`, `mul_finite_roundAt`, `fma_finite_roundAt`: for
  finite operands whose exact result is within the largest finite magnitude, the operation in
  the attribute `mode` is finite and equals `roundAt fmt` of the exact result in `mode`, for
  every `mode`. A fused multiply-add rounds the exact `x * y + z` once.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section Dyadic

/-- Downward magnitude rounding below overflow is finite and is the real floor of the magnitude on
the format grid, negated for a negative attached sign. -/
private theorem roundDyadicMagnitudeDown_finite_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Bool) (mantissa : Nat)
    (exponent : Int) (hm : mantissa ≠ 0)
    (hmax : (mantissa.log2 : Int) + exponent ≤ fmt.maxNormalExponent) :
    isFinite (roundDyadicMagnitudeDown fmt sign mantissa exponent) = true ∧
      toReal (roundDyadicMagnitudeDown fmt sign mantissa exponent) =
        if sign then -roundAt fmt ((mantissa : ℝ) * bpow exponent) .down
        else roundAt fmt ((mantissa : ℝ) * bpow exponent) .down := by
  have hfinite := isFinite_roundDyadicPosDown fmt mantissa exponent
  have hround := toReal_roundDyadicPosDown_eq_roundAt_of_le_max fmt mantissa exponent hfmt hm hmax
  cases sign
  · exact ⟨by simpa [roundDyadicPosDown] using hfinite,
      by simpa [roundDyadicPosDown] using hround⟩
  · rw [roundDyadicMagnitudeDown_true_eq_neg_false fmt _ _]
    refine ⟨by simpa [roundDyadicPosDown] using hfinite, ?_⟩
    rw [toReal_neg _ (by simpa [roundDyadicPosDown] using hfinite)]
    simpa [roundDyadicPosDown] using congrArg Neg.neg hround

/-- Upward magnitude rounding within the largest finite value is finite and is the real ceiling
of the magnitude on the format grid, negated for a negative attached sign. -/
private theorem roundDyadicMagnitudeUp_finite_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Bool) (mantissa : Nat)
    (exponent : Int) (hm : mantissa ≠ 0)
    (hbound : (mantissa : ℝ) * bpow exponent ≤ toReal (posMaxFinite fmt)) :
    isFinite (roundDyadicMagnitudeUp fmt sign mantissa exponent) = true ∧
      toReal (roundDyadicMagnitudeUp fmt sign mantissa exponent) =
        if sign then -roundAt fmt ((mantissa : ℝ) * bpow exponent) .up
        else roundAt fmt ((mantissa : ℝ) * bpow exponent) .up := by
  obtain ⟨hfinite, hround⟩ :=
    roundDyadicPosUp_finite_roundAt_of_le_posMaxFinite fmt mantissa exponent hfmt hm hbound
  cases sign
  · exact ⟨by simpa [roundDyadicPosUp] using hfinite, by simpa [roundDyadicPosUp] using hround⟩
  · rw [roundDyadicMagnitudeUp_true_eq_neg_false fmt _ _ (by simp [hfmt])]
    refine ⟨by simpa [roundDyadicPosUp] using hfinite, ?_⟩
    rw [toReal_neg _ (by simpa [roundDyadicPosUp] using hfinite)]
    simpa [roundDyadicPosUp] using congrArg Neg.neg hround

/-- A directed rounding of a signed magnitude rounds the magnitude up when the attribute moves
that sign away from zero, and down otherwise. -/
private theorem roundAt_signed_magnitude (fmt : FloatFormat) {mode : IEEERoundingMode}
    (hnearest : mode ≠ .nearest) (hnearestAway : mode ≠ .nearestAway) (sign : Bool) {x : ℝ}
    (hx : 0 ≤ x) :
    roundAt fmt (if sign then -x else x) mode =
      if mode.roundsAwayFromZero sign then
        (if sign then -roundAt fmt x .up else roundAt fmt x .up)
      else (if sign then -roundAt fmt x .down else roundAt fmt x .down) := by
  cases sign
  · simpa using roundAt_of_nonneg fmt hnearest hnearestAway hx
  · have hneg : mode.negate ≠ .nearest := by cases mode <;> simp_all
    have hnegAway : mode.negate ≠ .nearestAway := by cases mode <;> simp_all
    have hrounded := roundAt_of_nonneg fmt hneg hnegAway hx
    rw [IEEERoundingMode.roundsAwayFromZero_negate] at hrounded
    simp only [ite_true, roundAt_neg, hrounded, Bool.not_false]
    split <;> rfl

/-- A directed rounding of a nonzero dyadic rounds its magnitude up when the attribute moves its
sign away from zero, and down otherwise. -/
private theorem Internal.Directed.roundDyadic_eq_magnitude (fmt : FloatFormat)
    {mode : IEEERoundingMode} (hnearest : mode ≠ .nearest) (hnearestAway : mode ≠ .nearestAway)
    (d : Numerics.Dyadic) (hzero : d.significand ≠ 0) :
    Internal.Directed.roundDyadic fmt mode d =
      if mode.roundsAwayFromZero d.negative then
        roundDyadicMagnitudeUp fmt d.negative d.significand d.exponent
      else roundDyadicMagnitudeDown fmt d.negative d.significand d.exponent := by
  cases mode with
  | nearest => exact absurd rfl hnearest
  | nearestAway => exact absurd rfl hnearestAway
  | towardZero =>
      simp [Internal.Directed.roundDyadic, roundDyadicTowardZero, hzero,
        IEEERoundingMode.roundsAwayFromZero]
  | up =>
      cases hsign : d.negative <;>
        simp [Internal.Directed.roundDyadic, roundDyadicUp, hzero, hsign,
          IEEERoundingMode.roundsAwayFromZero]
  | down =>
      cases hsign : d.negative <;>
        simp [Internal.Directed.roundDyadic, roundDyadicDown, hzero, hsign,
          IEEERoundingMode.roundsAwayFromZero]
  | away =>
      simp [Internal.Directed.roundDyadic, roundDyadicAway, hzero,
        IEEERoundingMode.roundsAwayFromZero]

/-- In a conventional IEEE format, a rounding of an exact dyadic within the largest finite
magnitude in the attribute `towardZero`, `up`, `down` or `away` is finite, and it is the rounding
of the dyadic's real value in that attribute on the format grid. -/
private theorem Internal.Directed.roundDyadic_finite_roundAt_of_directed
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode)
    (hnearest : mode ≠ .nearest) (hnearestAway : mode ≠ .nearestAway)
    (d : Numerics.Dyadic) (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    isFinite (Internal.Directed.roundDyadic fmt mode d) = true ∧
      toReal (Internal.Directed.roundDyadic fmt mode d) = roundAt fmt d.toReal mode := by
  by_cases hzero : d.significand = 0
  · have hreal : d.toReal = 0 := (Dyadic.toReal_eq_zero_iff d).mpr hzero
    have hvalue :
        isFinite (zero fmt d.negative) = true ∧
          toReal (zero fmt d.negative) = roundAt fmt d.toReal mode :=
      ⟨isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt d.negative), by
        rw [toReal_zero, hreal, roundAt_zero fmt mode]⟩
    cases mode with
    | nearest => exact absurd rfl hnearest
    | nearestAway => exact absurd rfl hnearestAway
    | towardZero =>
        simpa [Internal.Directed.roundDyadic, roundDyadicTowardZero, hzero] using hvalue
    | up => simpa [Internal.Directed.roundDyadic, roundDyadicUp, hzero] using hvalue
    | down => simpa [Internal.Directed.roundDyadic, roundDyadicDown, hzero] using hvalue
    | away => simpa [Internal.Directed.roundDyadic, roundDyadicAway, hzero] using hvalue
  · have hmagnitude :
        (d.significand : ℝ) * bpow d.exponent ≤ toReal (posMaxFinite fmt) := by
      rwa [Dyadic.abs_toReal] at hbound
    have hnonneg : 0 ≤ (d.significand : ℝ) * bpow d.exponent :=
      mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _)
    have hmax := Dyadic.leadingExponent_le_maxNormalExponent fmt d hzero hbound
    rw [Internal.Directed.roundDyadic_eq_magnitude fmt hnearest hnearestAway d hzero,
      Dyadic.toReal_eq_signed_magnitude,
      roundAt_signed_magnitude fmt hnearest hnearestAway d.negative hnonneg]
    split
    · exact roundDyadicMagnitudeUp_finite_roundAt fmt hfmt _ _ _ hzero hmagnitude
    · exact roundDyadicMagnitudeDown_finite_roundAt fmt hfmt _ _ _ hzero hmax

end Dyadic

section NearestAway

/-- The scaled mantissa of a dyadic is halfway between two integers exactly when the dyadic is
a grid tie: the tie test on its bits is the tie of its real value. -/
theorem fract_scaledMantissa_eq_half_iff (fmt : FloatFormat) (d : Numerics.Dyadic) :
    Int.fract (scaledMantissa Numerics.binaryRadix (fexpOf fmt) d.toReal) = 1 / 2 ↔
      dyadicIsGridTie fmt d = true := by
  by_cases hm : d.significand = 0
  · rw [(Dyadic.toReal_eq_zero_iff d).mpr hm, scaledMantissa, zero_mul, Int.fract_zero]
    refine iff_of_false one_half_pos.ne fun htie => ?_
    rcases d with ⟨sign, mantissa, exponent⟩
    obtain rfl : mantissa = 0 := hm
    rw [dyadicIsGridTie_zero] at htie
    exact Bool.false_ne_true htie
  have hscaled : scaledMantissa Numerics.binaryRadix (fexpOf fmt) d.toReal =
      (d.signedSignificand : ℝ) * (2 : ℝ) ^ (d.exponent -
        max fmt.minSubnormalExponent ((d.significand.log2 : ℤ) + d.exponent - fmt.fracWidth)) := by
    rw [scaledMantissa, cexp_dyadic fmt d hm, max_comm, Numerics.Dyadic.toReal, bpow_binaryRadix,
      mul_assoc, ← zpow_add₀ two_ne_zero]
    rfl
  rw [hscaled]
  unfold dyadicIsGridTie
  generalize d.exponent -
    max fmt.minSubnormalExponent ((d.significand.log2 : ℤ) + d.exponent - fmt.fracWidth) = k
  cases k with
  | ofNat n =>
      -- The scaled mantissa is an integer, and the bit test finds no bit below the grid.
      have hint : (d.signedSignificand : ℝ) * (2 : ℝ) ^ (Int.ofNat n) =
          ((d.signedSignificand * 2 ^ n : ℤ) : ℝ) := by
        rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
        exact congrArg ((d.signedSignificand : ℝ) * ·) (zpow_natCast (2 : ℝ) n)
      rw [hint, Int.fract_intCast]
      exact iff_of_false one_half_pos.ne Bool.false_ne_true
  | negSucc s =>
      -- The magnitude over `2 ^ (s + 1)` is a tie exactly when its low bits are the top one.
      have hpow : (2 : ℝ) ^ (s + 1) = ((2 ^ (s + 1) : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
      have key : Int.fract ((d.significand : ℝ) / (2 : ℝ) ^ (s + 1)) = 1 / 2 ↔
          Numerics.shiftRightIsTie d.significand (s + 1) = true := by
        rw [hpow, Int.fract_div_natCast_eq_div_natCast_mod,
          div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.two_pow_pos _))) two_ne_zero,
          one_mul, Numerics.shiftRightIsTie_eq_true_iff, Nat.add_sub_cancel, Nat.pow_succ]
        constructor
        · intro h
          have hnat : d.significand % (2 ^ s * 2) * 2 = 2 ^ s * 2 := by exact_mod_cast h
          omega
        · rintro ⟨-, h⟩
          rw [h, Nat.cast_mul, Nat.cast_ofNat]
      -- A tie stays a tie under negation.
      have hneg : ∀ {y : ℝ}, Int.fract y = 1 / 2 → Int.fract (-y) = 1 / 2 := fun h => by
        rw [Int.fract_neg (h.trans_ne one_half_pos.ne'), h, sub_half]
      rw [zpow_negSucc, ← div_eq_mul_inv, Numerics.Dyadic.cast_signedSignificand]
      cases d.negative
      · rw [ite_eq_right Bool.false_ne_true, one_mul]
        exact key
      · rw [ite_eq_left rfl, neg_one_mul, neg_div]
        exact ⟨fun h => key.mp (_root_.neg_neg ((d.significand : ℝ) / 2 ^ (s + 1)) ▸ hneg h),
          fun h => hneg (key.mpr h)⟩

/--
In a conventional IEEE format, rounding an exact dyadic within the largest finite magnitude to
nearest with ties away from zero is finite, and it is that rounding of the dyadic's real value on
the format grid. At a grid tie both round away from zero, and off one both round to nearest
even.
-/
theorem roundDyadicNearestAway_finite_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (d : Numerics.Dyadic)
    (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    isFinite (roundDyadicNearestAway fmt d) = true ∧
      toReal (roundDyadicNearestAway fmt d) = roundAt fmt d.toReal .nearestAway := by
  unfold roundDyadicNearestAway
  by_cases htie : dyadicIsGridTie fmt d = true
  · rw [ite_eq_left htie, show roundAt fmt d.toReal .nearestAway = roundAt fmt d.toReal .away from
      round_congr (nearestChoice_tieAway_eq_awayRound_of_fract_eq_half
        ((fract_scaledMantissa_eq_half_iff fmt d).mpr htie))]
    exact Internal.Directed.roundDyadic_finite_roundAt_of_directed fmt hfmt .away (by decide)
      (by decide) d hbound
  · rw [ite_eq_right htie]
    have hfinite := isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite fmt hfmt d hbound
    exact ⟨hfinite, (toReal_roundDyadic_eq_roundAt fmt hfmt d hfinite).trans (round_congr
      ((nearestChoice_eq_of_fract_ne_half nearestAwayChoice nearestEvenChoice fun h =>
        htie ((fract_scaledMantissa_eq_half_iff fmt d).mp h)).trans
          (nearestChoice_even_eq _))).symm⟩

end NearestAway

section Every

/--
In a conventional IEEE format, a rounding of an exact dyadic within the largest finite magnitude
is finite, and it is the rounding of the dyadic's real value on the format grid, in every one of
the six rounding attributes.
-/
theorem Internal.Directed.roundDyadic_finite_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode)
    (d : Numerics.Dyadic) (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    isFinite (Internal.Directed.roundDyadic fmt mode d) = true ∧
      toReal (Internal.Directed.roundDyadic fmt mode d) = roundAt fmt d.toReal mode := by
  cases mode with
  | nearest =>
      have hfinite :=
        isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite fmt hfmt d hbound
      exact ⟨hfinite, toReal_roundDyadic_eq_roundAt fmt hfmt d hfinite⟩
  | nearestAway => exact roundDyadicNearestAway_finite_roundAt fmt hfmt d hbound
  | towardZero =>
      exact Internal.Directed.roundDyadic_finite_roundAt_of_directed fmt hfmt _ (by decide)
        (by decide) d hbound
  | up =>
      exact Internal.Directed.roundDyadic_finite_roundAt_of_directed fmt hfmt _ (by decide)
        (by decide) d hbound
  | down =>
      exact Internal.Directed.roundDyadic_finite_roundAt_of_directed fmt hfmt _ (by decide)
        (by decide) d hbound
  | away =>
      exact Internal.Directed.roundDyadic_finite_roundAt_of_directed fmt hfmt _ (by decide)
        (by decide) d hbound

end Every

section Operations

variable {fmt : FloatFormat} {x y z : Model fmt}

/--
For an IEEE descriptor and every rounding attribute, finite operands whose exact sum is within
the largest finite magnitude have a finite sum, the rounding of the exact sum in that attribute.
-/
theorem add_finite_roundAt (hfmt : fmt.isIEEE = true) {mode : IEEERoundingMode}
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x + toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (add x y (mode := mode)) = true ∧
      toReal (add x y (mode := mode)) = roundAt fmt (toReal x + toReal y) mode := by
  by_cases hnearest : mode = .nearest
  · subst hnearest
    have hfinite := isFinite_add_of_abs_toReal_add_le_posMaxFinite x y hfmt hx hy hbound
    exact ⟨hfinite, toReal_add_eq_roundAt x y hfmt hfinite⟩
  · obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
    obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
    have hsum := toReal_addDyadic_of_toDyadic?_some hdx hdy
    rw [add_eq_of_toDyadic?_some mode hnearest hdx hdy, ← hsum]
    split
    · next hzero =>
      have hreal : (addDyadic dx dy).toReal = 0 := (Dyadic.toReal_eq_zero_iff _).mpr hzero
      refine ⟨?_, by rw [toReal_zeroForExactSum, hreal, roundAt_zero fmt mode]⟩
      exact isFinite_eq_true_of_isZero_eq_true _ (by simp [zeroForExactSum])
    · exact Internal.Directed.roundDyadic_finite_roundAt fmt hfmt mode _ (hsum ▸ hbound)

/--
For an IEEE descriptor and every rounding attribute, finite operands whose exact difference is
within the largest finite magnitude have a finite difference, the rounding of the exact
difference in that attribute.
-/
theorem sub_finite_roundAt (hfmt : fmt.isIEEE = true) {mode : IEEERoundingMode}
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x - toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (sub x y (mode := mode)) = true ∧
      toReal (sub x y (mode := mode)) = roundAt fmt (toReal x - toReal y) mode := by
  by_cases hnearest : mode = .nearest
  · subst hnearest
    have hfinite := isFinite_sub_of_abs_toReal_sub_le_posMaxFinite x y hfmt hx hy hbound
    exact ⟨hfinite, toReal_sub_eq_roundAt x y hfmt hfinite⟩
  · have hneg : isFinite (neg y) = true := by simpa using hy
    have hadd := add_finite_roundAt (x := x) (y := neg y) (mode := mode) hfmt hx hneg
      (by rwa [toReal_neg y hy, ← sub_eq_add_neg])
    rw [toReal_neg y hy, ← sub_eq_add_neg] at hadd
    have hsub : sub x y (mode := mode) = add x (neg y) (mode := mode) := by
      cases mode <;> first | exact absurd rfl hnearest | rfl
    rw [hsub]
    exact hadd

/--
For an IEEE descriptor and every rounding attribute, finite operands whose exact product is
within the largest finite magnitude have a finite product, the rounding of the exact product in
that attribute.
-/
theorem mul_finite_roundAt (hfmt : fmt.isIEEE = true) {mode : IEEERoundingMode}
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x * toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (mul x y (mode := mode)) = true ∧
      toReal (mul x y (mode := mode)) = roundAt fmt (toReal x * toReal y) mode := by
  by_cases hnearest : mode = .nearest
  · subst hnearest
    have hfinite := isFinite_mul_of_abs_mul_le_posMaxFinite x y hfmt hx hy
      (by rwa [← abs_mul])
    exact ⟨hfinite, toReal_mul_eq_roundAt x y hfmt hfinite⟩
  · obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
    obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
    have hproduct := toReal_mulDyadic_of_toDyadic?_some hdx hdy
    rw [mul_eq_of_toDyadic?_some mode hnearest hdx hdy, ← hproduct]
    exact Internal.Directed.roundDyadic_finite_roundAt fmt hfmt mode _ (hproduct ▸ hbound)

/--
For an IEEE descriptor and every rounding attribute, finite operands whose exact `x * y + z` is
within the largest finite magnitude have a finite fused multiply-add, the one rounding of that
exact value in the attribute.
-/
theorem fma_finite_roundAt (hfmt : fmt.isIEEE = true) {mode : IEEERoundingMode}
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hbound : |toReal x * toReal y + toReal z| ≤ toReal (posMaxFinite fmt)) :
    isFinite (fma x y z (mode := mode)) = true ∧
      toReal (fma x y z (mode := mode)) = roundAt fmt (toReal x * toReal y + toReal z) mode := by
  by_cases hnearest : mode = .nearest
  · subst hnearest
    have hfinite := isFinite_fma_of_abs_toReal_fma_le_posMaxFinite x y z hfmt hx hy hz hbound
    exact ⟨hfinite, toReal_fma_eq_roundAt x y z hfmt hfinite⟩
  · obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
    obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
    obtain ⟨dz, hdz⟩ := exists_toDyadic?_of_isFinite hz
    have hchoose : chooseNaN3 x y z = none := by
      simp [chooseNaN3, isNaN_eq_false_of_isFinite_eq_true x hx,
        isNaN_eq_false_of_isFinite_eq_true y hy, isNaN_eq_false_of_isFinite_eq_true z hz,
        isSignaling_eq_false_of_isNaN_eq_false x (isNaN_eq_false_of_isFinite_eq_true x hx),
        isSignaling_eq_false_of_isNaN_eq_false y (isNaN_eq_false_of_isFinite_eq_true y hy),
        isSignaling_eq_false_of_isNaN_eq_false z (isNaN_eq_false_of_isFinite_eq_true z hz)]
    have hxInf := isInfinite_eq_false_of_isFinite_eq_true x hx
    have hyInf := isInfinite_eq_false_of_isFinite_eq_true y hy
    have hzInf := isInfinite_eq_false_of_isFinite_eq_true z hz
    have hexact : (addDyadic
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent } dz).toReal =
          toReal x * toReal y + toReal z := by
      rw [Dyadic.toReal_addDyadic, toReal_mulDyadic_of_toDyadic?_some hdx hdy]
      simp [toReal_eq, hdz]
    have hvalue : fma x y z (mode := mode) =
        if (addDyadic
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent } dz).significand = 0 then
          zeroForExactSum fmt mode (Bool.xor dx.negative dy.negative) dz.negative
        else
          Internal.Directed.roundDyadic fmt mode (addDyadic
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent } dz) := by
      rw [← Internal.Directed.fma_eq]
      cases mode <;> first
        | exact absurd rfl hnearest
        | simp [Internal.Directed.fma, hchoose, withNaNSelection_of_none, hxInf, hyInf, hzInf,
            finiteDyadic_eq_of_toDyadic _ hdx, finiteDyadic_eq_of_toDyadic _ hdy,
            finiteDyadic_eq_of_toDyadic _ hdz]
    rw [hvalue, ← hexact]
    split
    · next hzero =>
      have hreal : (addDyadic
          { negative := Bool.xor dx.negative dy.negative
            significand := dx.significand * dy.significand
            exponent := dx.exponent + dy.exponent } dz).toReal = 0 :=
        (Dyadic.toReal_eq_zero_iff _).mpr hzero
      refine ⟨?_, by rw [toReal_zeroForExactSum, hreal, roundAt_zero fmt mode]⟩
      exact isFinite_eq_true_of_isZero_eq_true _ (by simp [zeroForExactSum])
    · exact Internal.Directed.roundDyadic_finite_roundAt fmt hfmt mode _ (hexact ▸ hbound)

end Operations

end Model
end FloatLib.Floats.Formats.BinaryInterchange
