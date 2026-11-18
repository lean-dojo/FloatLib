/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.RoundToIntegral.Encoding

/-!
# Real-valued contracts for integral rounding

Under the stated IEEE range hypotheses, integral rounding denotes the selected integer. Its real
value is the corresponding floor, ceiling, truncation, away-from-zero or nearest value. Nearest
rounding moves the input by at most one half; every direction moves it by at most one. The
truncation contract retains its weaker format hypotheses.

## References

* IEEE 754-2019, Sections 4.3.2 and 5.9 (directed and integral rounding).
  https://doi.org/10.1109/IEEESTD.2019.8766229
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics
open FloatLib.Floats.Formats.Flocq

/-- The real value of a finite integral rounding is the integer selected by `roundDyadicToInt`. -/
theorem toReal_roundToIntegral
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (hd : toDyadic? value = some exact) :
    toReal (roundToIntegral value mode) = ((roundDyadicToInt mode exact : Int) : ℝ) :=
  (roundToIntegral_finite_exact hfmt hrange value mode exact
    (exactValue_eq_finite_of_toDyadic?_eq_some hd)).2.1

/--
On a finite input, the result of integral rounding denotes an integer whenever the format's
integers are representable, `fracWidth ≤ maxNormalExponent`.
-/
theorem exists_int_toReal_roundToIntegral
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode) (hfinite : isFinite value = true) :
    ∃ n : Int, toReal (roundToIntegral value mode) = n := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  exact ⟨_, toReal_roundToIntegral hfmt hrange value mode exact hd⟩

/-- On a finite input, integral rounding delivers the kernel's integer for the decoded value. -/
private theorem exists_toReal_roundToIntegral_of_isFinite
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode) (hfinite : isFinite value = true) :
    ∃ exact : Numerics.Dyadic, toReal value = exact.toReal ∧
      toReal (roundToIntegral value mode) = ((roundDyadicToInt mode exact : Int) : ℝ) := by
  obtain ⟨exact, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  exact ⟨exact, by simp [toReal_eq, hd], toReal_roundToIntegral hfmt hrange value mode exact hd⟩

/-- On a finite input, rounding toward negative infinity computes the floor of the real value. -/
theorem toReal_roundToIntegral_down
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .down) = ⌊toReal value⌋ := by
  obtain ⟨exact, hx, hround⟩ :=
    exists_toReal_roundToIntegral_of_isFinite hfmt hrange value _ hfinite
  rw [hround, roundDyadicToInt_down, hx]

/-- On a finite input, rounding toward positive infinity computes the ceiling of the real value. -/
theorem toReal_roundToIntegral_up
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .up) = ⌈toReal value⌉ := by
  obtain ⟨exact, hx, hround⟩ :=
    exists_toReal_roundToIntegral_of_isFinite hfmt hrange value _ hfinite
  rw [hround, roundDyadicToInt_up, hx]

/--
On a finite input, rounding toward zero truncates the real value: floor when nonnegative, ceiling
otherwise. Truncation cannot increase the magnitude, so no exponent-range restriction is needed.
-/
theorem toReal_roundToIntegral_towardZero
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .towardZero) =
      if 0 ≤ toReal value then (⌊toReal value⌋ : ℝ) else (⌈toReal value⌉ : ℝ) :=
  (roundToIntegral_towardZero_finite_exact hfmt value hfinite).2.1

/--
On a finite input, rounding to nearest with ties away from zero computes the nearest integer and
resolves a tie toward the integer of larger magnitude, roundToIntegralTiesToAway of IEEE 754-2019.
This is Flocq's `nearestChoice nearestAwayChoice`.
-/
theorem toReal_roundToIntegral_nearestAway
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .nearestAway) =
      nearestChoice nearestAwayChoice (toReal value) := by
  obtain ⟨exact, hx, hround⟩ :=
    exists_toReal_roundToIntegral_of_isFinite hfmt hrange value _ hfinite
  rw [hround, roundDyadicToInt_nearestAway, hx]

/--
On a finite input, rounding away from zero computes the ceiling of a nonnegative value and the floor
of a negative one, as MPFR's `mpfr_rint` does under `MPFR_RNDA`.
-/
theorem toReal_roundToIntegral_away
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .away) =
      if 0 ≤ toReal value then (⌈toReal value⌉ : ℝ) else (⌊toReal value⌋ : ℝ) := by
  obtain ⟨exact, hx, hround⟩ :=
    exists_toReal_roundToIntegral_of_isFinite hfmt hrange value _ hfinite
  rw [hround, roundDyadicToInt_away, hx]
  split_ifs <;> rfl

/--
On a finite input, rounding to nearest computes the nearest integer with ties to even, `nearestEven`
from the Flocq theory. Mathlib's `round` resolves ties toward positive infinity.
-/
theorem toReal_roundToIntegral_nearest
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    toReal (roundToIntegral value .nearest) = nearestEven (toReal value) := by
  obtain ⟨exact, hx, hround⟩ :=
    exists_toReal_roundToIntegral_of_isFinite hfmt hrange value _ hfinite
  rw [hround, roundDyadicToInt_nearest, hx]

/-- On a finite input, rounding to an integral value to nearest with ties to even moves the real
value by at most one half. -/
theorem abs_toReal_roundToIntegral_nearest_sub_le
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    |toReal (roundToIntegral value .nearest) - toReal value| ≤ 1 / 2 := by
  rw [toReal_roundToIntegral_nearest hfmt hrange value hfinite]
  have := ValidRndToNearest.abs_sub_le_half (rnd := nearestEven) (toReal value)
  norm_num at this ⊢
  exact this

/-- On a finite input, rounding to an integral value to nearest with ties away from zero moves the
real value by at most one half. -/
theorem abs_toReal_roundToIntegral_nearestAway_sub_le
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    |toReal (roundToIntegral value .nearestAway) - toReal value| ≤ 1 / 2 := by
  rw [toReal_roundToIntegral_nearestAway hfmt hrange value hfinite]
  exact nearestChoice_abs_sub_le_half nearestAwayChoice _

/-- On a finite input, rounding to an integral value toward zero moves the real value by at most
one. Truncation needs no exponent-range restriction. -/
theorem abs_toReal_roundToIntegral_towardZero_sub_le
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) :
    |toReal (roundToIntegral value .towardZero) - toReal value| ≤ 1 := by
  rw [toReal_roundToIntegral_towardZero hfmt value hfinite]
  have floor := Int.floor_le (toReal value)
  have floor' := Int.lt_floor_add_one (toReal value)
  have ceil := Int.le_ceil (toReal value)
  have ceil' := Int.ceil_lt_add_one (toReal value)
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- On a finite input, rounding to an integral value in any direction moves the real value by at
most one. -/
theorem abs_toReal_roundToIntegral_sub_le
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (mode : IEEERoundingMode) (hfinite : isFinite value = true) :
    |toReal (roundToIntegral value mode) - toReal value| ≤ 1 := by
  have floor := Int.floor_le (toReal value)
  have floor' := Int.lt_floor_add_one (toReal value)
  have ceil := Int.le_ceil (toReal value)
  have ceil' := Int.ceil_lt_add_one (toReal value)
  cases mode with
  | nearest =>
      exact (abs_toReal_roundToIntegral_nearest_sub_le hfmt hrange value hfinite).trans
        (by norm_num)
  | nearestAway =>
      exact (abs_toReal_roundToIntegral_nearestAway_sub_le hfmt hrange value hfinite).trans
        (by norm_num)
  | towardZero => exact abs_toReal_roundToIntegral_towardZero_sub_le hfmt value hfinite
  | up =>
      rw [toReal_roundToIntegral_up hfmt hrange value hfinite, abs_le]
      constructor <;> linarith
  | down =>
      rw [toReal_roundToIntegral_down hfmt hrange value hfinite, abs_le]
      constructor <;> linarith
  | away =>
      rw [toReal_roundToIntegral_away hfmt hrange value hfinite]
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- On a finite input, rounding to an integral value upward moves the real value by at most
one. -/
theorem abs_toReal_roundToIntegral_up_sub_le
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    |toReal (roundToIntegral value .up) - toReal value| ≤ 1 :=
  abs_toReal_roundToIntegral_sub_le hfmt hrange value _ hfinite

/-- On a finite input, rounding to an integral value downward moves the real value by at most
one. -/
theorem abs_toReal_roundToIntegral_down_sub_le
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    |toReal (roundToIntegral value .down) - toReal value| ≤ 1 :=
  abs_toReal_roundToIntegral_sub_le hfmt hrange value _ hfinite

/-- On a finite input, rounding to an integral value away from zero moves the real value by at
most one. -/
theorem abs_toReal_roundToIntegral_away_sub_le
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent)
    (value : Model fmt) (hfinite : isFinite value = true) :
    |toReal (roundToIntegral value .away) - toReal value| ≤ 1 :=
  abs_toReal_roundToIntegral_sub_le hfmt hrange value _ hfinite
end Model
end FloatLib.Floats.Formats.BinaryInterchange
