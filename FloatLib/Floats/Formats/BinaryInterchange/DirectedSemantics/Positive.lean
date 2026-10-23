/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Basic
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Modes
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Quotient

/-!
# Positive directed rounding for arbitrary executable float formats

The shift-based directed rounders used by `Model` are related to the independent Flocq-style
real semantics at the scaled-mantissa boundary, before subnormal and normal values are packed
into interchange fields.

`roundAt fmt x mode` is the real rounding of every `IEEERoundingMode` on the same grid, Flocq's
`round` with `nearestEven`, `ceilRound`, and `floorRound` for nearest-even and the two infinity
directions. Nearest-away rounding is Flocq's `nearestChoice` with the tie choice
`nearestAwayChoice`, and rounding away from zero is `awayRound`.

All definitions are uniform in `FloatFormat`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/-! ## Real rounding in every direction -/

/-- Nearest-away rounding rounds the scaled mantissa with ties away from zero. -/
@[simp] theorem roundAt_nearestAway (fmt : FloatFormat) (x : ℝ) :
    roundAt fmt x .nearestAway =
      round (β := Numerics.binaryRadix) (fexp := fexpOf fmt)
        (nearestChoice nearestAwayChoice) x :=
  rfl

/-- Rounding toward zero truncates the scaled mantissa. -/
@[simp] theorem roundAt_towardZero (fmt : FloatFormat) (x : ℝ) :
    roundAt fmt x .towardZero =
      round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) truncRound x :=
  rfl

/-- Rounding away from zero rounds the scaled mantissa away from zero. -/
@[simp] theorem roundAt_away (fmt : FloatFormat) (x : ℝ) :
    roundAt fmt x .away =
      round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) awayRound x :=
  rfl

/-- Every rounding direction returns a value on the grid of `fmt`. -/
theorem genericFormat_roundAt (fmt : FloatFormat) (x : ℝ) (mode : IEEERoundingMode := .nearest) :
    genericFormat Numerics.binaryRadix (fexpOf fmt) (roundAt fmt x mode) := by
  rw [roundAt_eq_round]
  exact generic_format_round (roundingFunction mode) x

/-- Every rounding direction fixes a value already on the grid of `fmt`. -/
theorem roundAt_of_genericFormat (fmt : FloatFormat) {x : ℝ}
    (hx : genericFormat Numerics.binaryRadix (fexpOf fmt) x)
    (mode : IEEERoundingMode := .nearest) :
    roundAt fmt x mode = x := by
  rw [roundAt_eq_round]
  exact round_preserves_generic (roundingFunction mode) x hx

/--
On a nonnegative real a directed mode is upward rounding when it rounds positive results away
from zero, and downward rounding otherwise. The two nearest modes are not directed.
-/
theorem roundAt_of_nonneg (fmt : FloatFormat) {mode : IEEERoundingMode}
    (hnearest : mode ≠ .nearest) (hnearestAway : mode ≠ .nearestAway) {x : ℝ}
    (hx : 0 ≤ x) :
    roundAt fmt x mode =
      if mode.roundsAwayFromZero false then roundAt fmt x .up else roundAt fmt x .down := by
  have hs : 0 ≤ scaledMantissa Numerics.binaryRadix (fexpOf fmt) x := by
    rw [scaledMantissa_eq_div]
    exact div_nonneg hx (bpow.nonneg _ _)
  cases mode with
  | nearest => exact absurd rfl hnearest
  | nearestAway => exact absurd rfl hnearestAway
  | towardZero =>
      change round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) truncRound x =
        round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) floorRound x
      unfold Flocq.round
      rw [truncRound_eq_floor hs]
  | up => rfl
  | down => rfl
  | away =>
      change round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) awayRound x =
        round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) ceilRound x
      unfold Flocq.round
      rw [awayRound_eq_ceil hs]

/--
Two reals with the same canonical exponent whose scaled mantissas have the same integer bracket
and the same location in it round alike in every direction.
-/
theorem roundAt_eq_of_scaledBracket (fmt : FloatFormat) (mode : IEEERoundingMode)
    {x y : ℝ} {m : ℤ} {location : Location}
    (hcexp : cexp Numerics.binaryRadix (fexpOf fmt) x =
      cexp Numerics.binaryRadix (fexpOf fmt) y)
    (hx : InbetweenInt m (scaledMantissa Numerics.binaryRadix (fexpOf fmt) x) location)
    (hy : InbetweenInt m (scaledMantissa Numerics.binaryRadix (fexpOf fmt) y) location) :
    roundAt fmt x mode = roundAt fmt y mode := by
  cases mode with
  | nearest =>
      change round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) nearestEven x =
        round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) nearestEven y
      rw [round_nearestEven_of_scaledBracket x hx, round_nearestEven_of_scaledBracket y hy,
        hcexp]
  | towardZero =>
      change round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) truncRound x =
        round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) truncRound y
      rw [round_trunc_of_scaledBracket x hx, round_trunc_of_scaledBracket y hy, hcexp]
  | up =>
      change round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) ceilRound x =
        round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) ceilRound y
      rw [round_ceil_of_scaledBracket x hx, round_ceil_of_scaledBracket y hy, hcexp]
  | down =>
      change round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) floorRound x =
        round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) floorRound y
      rw [round_floor_of_scaledBracket x hx, round_floor_of_scaledBracket y hy, hcexp]
  | nearestAway =>
      change round (β := Numerics.binaryRadix) (fexp := fexpOf fmt)
          (nearestChoice nearestAwayChoice) x =
        round (β := Numerics.binaryRadix) (fexp := fexpOf fmt)
          (nearestChoice nearestAwayChoice) y
      rw [round_nearestChoice_of_scaledBracket nearestAwayChoice x hx,
        round_nearestChoice_of_scaledBracket nearestAwayChoice y hy, hcexp]
  | away =>
      change round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) awayRound x =
        round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) awayRound y
      rw [round_away_of_scaledBracket x hx, round_away_of_scaledBracket y hy, hcexp]

/-! ## Executable scaled-mantissa rounding -/

/-- Floor a natural mantissa after expressing it at `targetExponent`. -/
def roundMantissaAtExponentDown
    (mantissa : Nat) (exponent targetExponent : Int) : Nat :=
  if exponent ≤ targetExponent then
    Nat.shiftRight mantissa (targetExponent - exponent).toNat
  else
    Nat.shiftLeft mantissa (exponent - targetExponent).toNat

/-- Ceil a natural mantissa after expressing it at `targetExponent`. -/
def roundMantissaAtExponentUp
    (mantissa : Nat) (exponent targetExponent : Int) : Nat :=
  if exponent ≤ targetExponent then
    Numerics.shiftRightCeil mantissa (targetExponent - exponent).toNat
  else
    Nat.shiftLeft mantissa (exponent - targetExponent).toNat

/-- Ceiling alignment preserves nonzeroness of a positive mantissa. -/
theorem roundMantissaAtExponentUp_ne_zero
    (mantissa : Nat) (exponent targetExponent : Int) (hm : mantissa ≠ 0) :
    roundMantissaAtExponentUp mantissa exponent targetExponent ≠ 0 := by
  by_cases hle : exponent ≤ targetExponent
  · let shift := (targetExponent - exponent).toNat
    have hcover := le_shiftRightCeil_mul_pow2 mantissa shift
    simp only [roundMantissaAtExponentUp, hle, ite_true]
    intro hzero
    rw [hzero] at hcover
    simp at hcover
    exact hm hcover
  · simp [roundMantissaAtExponentUp, hle, Nat.shiftLeft_eq, hm]

/-- Floor alignment never exceeds ceiling alignment at the same exponent. -/
theorem roundMantissaAtExponentDown_le_up
    (mantissa : Nat) (exponent targetExponent : Int) :
    roundMantissaAtExponentDown mantissa exponent targetExponent ≤
      roundMantissaAtExponentUp mantissa exponent targetExponent := by
  by_cases hle : exponent ≤ targetExponent
  · simp only [roundMantissaAtExponentDown, roundMantissaAtExponentUp, hle, ite_true]
    exact Numerics.shiftRight_le_shiftRightCeil _ _
  · simp [roundMantissaAtExponentDown, roundMantissaAtExponentUp, hle]

/-- Ceiling alignment is at most one unit above floor alignment. -/
theorem roundMantissaAtExponentUp_le_down_add_one
    (mantissa : Nat) (exponent targetExponent : Int) :
    roundMantissaAtExponentUp mantissa exponent targetExponent ≤
      roundMantissaAtExponentDown mantissa exponent targetExponent + 1 := by
  by_cases hle : exponent ≤ targetExponent
  · simp only [roundMantissaAtExponentDown, roundMantissaAtExponentUp, hle, ite_true]
    exact Numerics.shiftRightCeil_le_shiftRight_add_one _ _
  · simp [roundMantissaAtExponentDown, roundMantissaAtExponentUp, hle]

private theorem shiftRightCeil_eq_div_add_one
    (numerator shift : Nat) :
    Numerics.shiftRightCeil numerator shift =
      if numerator % pow2 shift = 0 then
        numerator / pow2 shift
      else
        numerator / pow2 shift + 1 := by
  rw [Numerics.shiftRightCeil_eq, pow2_eq_two_pow]
  split_ifs <;> simp

/-- Downward shifting computes the integer floor of a scaled positive dyadic. -/
theorem floor_scaledMagnitude
    (mantissa : Nat) (exponent targetExponent : Int) :
    floorRound
        ((mantissa : ℝ) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (exponent - targetExponent)) =
      Int.ofNat
        (roundMantissaAtExponentDown mantissa exponent targetExponent) := by
  by_cases hle : exponent ≤ targetExponent
  · let shift := (targetExponent - exponent).toNat
    have hshiftInt : (shift : Int) = targetExponent - exponent :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hle)
    have hvalue :
        (mantissa : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (exponent - targetExponent) =
          (mantissa : ℝ) / (pow2 shift : ℝ) := by
      rw [show exponent - targetExponent = -(shift : Int) by omega]
      simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
        Numerics.Radix.toReal,
        pow2_eq_two_pow, div_eq_mul_inv]
    rw [hvalue]
    simpa [floorRound, roundMantissaAtExponentDown, hle, shift,
      Nat.shiftRight_eq_div_pow, pow2_eq_two_pow] using
      floor_real_nat_div mantissa (pow2 shift)
  · let shift := (exponent - targetExponent).toNat
    have hshiftInt : (shift : Int) = exponent - targetExponent :=
      Int.toNat_of_nonneg (sub_nonneg.mpr (le_of_not_ge hle))
    have hvalue :
        (mantissa : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (exponent - targetExponent) =
          (Nat.shiftLeft mantissa shift : Nat) := by
      rw [← hshiftInt]
      simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
        Numerics.Radix.toReal,
        Nat.shiftLeft_eq]
    rw [hvalue]
    simp [floorRound, roundMantissaAtExponentDown, hle, shift]

/-- Upward shifting computes the integer ceiling of a scaled positive dyadic. -/
theorem ceil_scaledMagnitude
    (mantissa : Nat) (exponent targetExponent : Int) :
    ceilRound
        ((mantissa : ℝ) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (exponent - targetExponent)) =
      Int.ofNat
        (roundMantissaAtExponentUp mantissa exponent targetExponent) := by
  by_cases hle : exponent ≤ targetExponent
  · let shift := (targetExponent - exponent).toNat
    have hshiftInt : (shift : Int) = targetExponent - exponent :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hle)
    have hvalue :
        (mantissa : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (exponent - targetExponent) =
          (mantissa : ℝ) / (pow2 shift : ℝ) := by
      rw [show exponent - targetExponent = -(shift : Int) by omega]
      simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
        Numerics.Radix.toReal,
        pow2_eq_two_pow, div_eq_mul_inv]
    rw [hvalue]
    simp only [roundMantissaAtExponentUp, ite_eq_left hle]
    rw [shiftRightCeil_eq_div_add_one]
    have hpow2 : pow2 shift ≠ 0 := Nat.ne_of_gt (pow2_pos shift)
    simpa [ceilRound, shift, Numerics.roundQuotient_up_eq, hpow2] using
      ceil_div_eq_roundQuotient_up mantissa (pow2 shift) hpow2
  · let shift := (exponent - targetExponent).toNat
    have hshiftInt : (shift : Int) = exponent - targetExponent :=
      Int.toNat_of_nonneg (sub_nonneg.mpr (le_of_not_ge hle))
    have hvalue :
        (mantissa : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (exponent - targetExponent) =
          (Nat.shiftLeft mantissa shift : Nat) := by
      rw [← hshiftInt]
      simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
        Numerics.Radix.toReal,
        Nat.shiftLeft_eq]
    rw [hvalue]
    simp [ceilRound, roundMantissaAtExponentUp, hle, shift]

/-- Floor alignment at any target exponent is a lower bound for the exact dyadic magnitude. -/
theorem roundMantissaAtExponentDown_mul_bpow_le
    (mantissa : Nat) (exponent targetExponent : Int) :
    (roundMantissaAtExponentDown mantissa exponent targetExponent : ℝ) *
        bpow targetExponent ≤
      (mantissa : ℝ) * bpow exponent := by
  have hfloor :
      ((floorRound ((mantissa : ℝ) * bpow (exponent - targetExponent)) : Int) : ℝ) ≤
        (mantissa : ℝ) * bpow (exponent - targetExponent) :=
    Int.floor_le _
  rw [floor_scaledMagnitude] at hfloor
  change (roundMantissaAtExponentDown mantissa exponent targetExponent : ℝ) ≤
    (mantissa : ℝ) * bpow (exponent - targetExponent) at hfloor
  have hscale := mul_le_mul_of_nonneg_right hfloor (bpow_nonneg targetExponent)
  simpa only [mul_assoc, ← bpow_add, sub_add_cancel] using hscale

/-- Ceiling alignment at any target exponent is an upper bound for the exact dyadic magnitude. -/
theorem le_roundMantissaAtExponentUp_mul_bpow
    (mantissa : Nat) (exponent targetExponent : Int) :
    (mantissa : ℝ) * bpow exponent ≤
      (roundMantissaAtExponentUp mantissa exponent targetExponent : ℝ) *
        bpow targetExponent := by
  have hceil :
      (mantissa : ℝ) * bpow (exponent - targetExponent) ≤
        ((ceilRound ((mantissa : ℝ) * bpow (exponent - targetExponent)) : Int) : ℝ) :=
    Int.le_ceil _
  rw [ceil_scaledMagnitude] at hceil
  change (mantissa : ℝ) * bpow (exponent - targetExponent) ≤
    (roundMantissaAtExponentUp mantissa exponent targetExponent : ℝ) at hceil
  have hscale := mul_le_mul_of_nonneg_right hceil (bpow_nonneg targetExponent)
  simpa only [mul_assoc, ← bpow_add, sub_add_cancel] using hscale

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
