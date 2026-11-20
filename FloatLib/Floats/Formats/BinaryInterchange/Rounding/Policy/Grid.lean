/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Overflow
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Rational

import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SqrtSemantics
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact

/-!
# Every descriptor delivers the values of its grid exactly

`roundRatScaled fmt sign mantissa 1 exponent` rounds the dyadic number
`±mantissa * 2 ^ exponent` to nearest-even. When that number is already a value of the grid of
`fmt` and its magnitude is at most the largest finite one, the result is finite and denotes it
(`roundRatScaled_of_grid`), and it carries the sign bit `sign` (`signBit_roundRatScaled_of_grid`).
This holds for every descriptor: the conventional IEEE ones, the formats without an infinity
such as OCP E4M3, the formats with one zero, and the formats in which every encoding is finite.
The rounding of a located real number in a chosen direction delivers its result through this
function, so its contract reaches every descriptor from here.

`roundDyadic_spec` is the contract of `roundDyadic`, the nearest-even rounding of any dyadic
number, for every descriptor: the grid rounding when that is in range, and the overflow word
of the descriptor beyond it.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats.Formats.Flocq FloatLib.Numerics

/-- A scaled dyadic number is a rational number with exponent zero, which the reference
rounder rounds to the same encoding. -/
theorem exists_roundRatScaledGeneral_exponent_zero (fmt : FloatFormat) (sign : Bool)
    {mantissa : Nat} (hmantissa : mantissa ≠ 0) (exponent : Int) :
    ∃ num den : Nat, den ≠ 0 ∧
      roundRatScaledGeneral fmt sign mantissa 1 exponent =
          roundRatScaledGeneral fmt sign num den 0 ∧
        signedScaledRatToReal sign num den 0 =
          signedScaledRatToReal sign mantissa 1 exponent := by
  obtain ⟨shift, rfl | rfl⟩ := Int.eq_nat_or_neg exponent
  · refine ⟨mantissa <<< shift, 1, one_ne_zero, ?_, ?_⟩
    · have h := KernelPath.roundRatScaledGeneral_shiftLeft fmt sign mantissa 1 shift 0 shift
        hmantissa one_ne_zero
      simpa using h.symm
    · simp only [signedScaledRatToReal, scaledRatToReal, Model.bpow, Flocq.bpow_binaryRadix,
        Nat.shiftLeft_eq]
      push_cast
      simp [zpow_natCast]
  · refine ⟨mantissa, 1 <<< shift, by simp [Nat.shiftLeft_eq], ?_, ?_⟩
    · have h := KernelPath.roundRatScaledGeneral_shiftLeft fmt sign mantissa 1 0 shift
        (-(shift : Int)) hmantissa one_ne_zero
      simpa using h.symm
    · simp only [signedScaledRatToReal, scaledRatToReal, Model.bpow, Flocq.bpow_binaryRadix,
        Nat.shiftLeft_eq]
      push_cast
      simp [zpow_neg, zpow_natCast, div_eq_mul_inv]

/--
**A value of the grid is delivered exactly, by every descriptor.** For a nonzero mantissa, when
`±mantissa * 2 ^ exponent` is a value of the grid of `fmt` of magnitude at most the largest
finite one, its nearest-even rounding `roundRatScaled` is finite and denotes it.
-/
theorem roundRatScaled_of_grid (fmt : FloatFormat) (sign : Bool) {mantissa : Nat}
    (hmantissa : mantissa ≠ 0) (exponent : Int)
    (hgrid : roundAt fmt (signedScaledRatToReal sign mantissa 1 exponent) =
      signedScaledRatToReal sign mantissa 1 exponent)
    (hrange : |signedScaledRatToReal sign mantissa 1 exponent| ≤ toReal (posMaxFinite fmt)) :
    isFinite (roundRatScaled fmt sign mantissa 1 exponent) = true ∧
      toReal (roundRatScaled fmt sign mantissa 1 exponent) =
        signedScaledRatToReal sign mantissa 1 exponent := by
  by_cases hfmt : fmt.isIEEE = true
  · have hfinite := isFinite_roundRatScaled_of_abs_le_posMaxFinite fmt sign mantissa 1 exponent
      hfmt one_ne_zero hrange
    exact ⟨hfinite,
      (toReal_roundRatScaled_eq_roundAt fmt sign mantissa 1 exponent hfmt hfinite).trans hgrid⟩
  · obtain ⟨num, den, hden, hround, hvalue⟩ :=
      exists_roundRatScaledGeneral_exponent_zero fmt sign hmantissa exponent
    have hgeneral : roundRatScaled fmt sign mantissa 1 exponent =
        Policy.roundRatGeneralOfDenNeZero fmt { rounding := .nearest, overflow := .native } 0
          sign num den hden := by
      rw [roundRatScaled, dite_eq_right hfmt, hround]
      exact (Policy.roundRatGeneralOfDenNeZero_nearest_eq_roundRatScaledGeneral fmt 0 sign num
        den hden).symm
    rw [← hvalue] at hgrid hrange
    have hfinite := (Policy.isFinite_roundRatGeneral_nearest_iff fmt .native 0 sign num den
      hden).mpr (.inr (by rw [hgrid]; exact hrange))
    rw [hgeneral, ← hvalue]
    refine ⟨hfinite, ?_⟩
    rw [Policy.toReal_roundRatGeneral_nearest fmt .native 0 sign num den hden hfinite, hgrid]
    split_ifs
    · exact clampAt_eq_self fmt hrange
    · rfl

/-- A finite value with a positive real value has a clear sign bit. -/
theorem signBit_eq_false_of_toReal_pos {fmt : FloatFormat} {x : Model fmt}
    (hfinite : isFinite x = true) (hpositive : 0 < toReal x) : signBit x = false := by
  rcases isZero_or_signBit_eq_false_of_toReal_nonneg x hfinite hpositive.le with hzero | hclear
  · exact absurd (toReal_eq_zero_of_isZero x hzero) hpositive.ne'
  · exact hclear

/-- A value with a negative real value has its sign bit set. -/
theorem signBit_eq_true_of_toReal_neg {fmt : FloatFormat} {x : Model fmt}
    (hnegative : toReal x < 0) : signBit x = true := by
  cases hbit : signBit x with
  | true => rfl
  | false => exact absurd (toReal_nonneg_of_signBit_eq_false hbit) (not_le.mpr hnegative)

/-- A grid value that is delivered exactly carries the sign bit it was given. -/
theorem signBit_roundRatScaled_of_grid (fmt : FloatFormat) (sign : Bool) {mantissa : Nat}
    (hmantissa : mantissa ≠ 0) (exponent : Int)
    (hgrid : roundAt fmt (signedScaledRatToReal sign mantissa 1 exponent) =
      signedScaledRatToReal sign mantissa 1 exponent)
    (hrange : |signedScaledRatToReal sign mantissa 1 exponent| ≤ toReal (posMaxFinite fmt)) :
    signBit (roundRatScaled fmt sign mantissa 1 exponent) = sign := by
  obtain ⟨hfinite, hvalue⟩ := roundRatScaled_of_grid fmt sign hmantissa exponent hgrid hrange
  have hpositive : 0 < scaledRatToReal mantissa 1 exponent := by
    have hm : (0 : ℝ) < mantissa := by exact_mod_cast Nat.pos_of_ne_zero hmantissa
    have hpow : (0 : ℝ) < Model.bpow exponent := Flocq.bpow.pos _ _
    simp only [scaledRatToReal, Nat.cast_one, div_one]
    exact mul_pos hm hpow
  cases sign with
  | false =>
      simp only [signedScaledRatToReal, Bool.false_eq_true, ↓reduceIte] at hvalue
      exact signBit_eq_false_of_toReal_pos hfinite (hvalue ▸ hpositive)
  | true =>
      simp only [signedScaledRatToReal, ↓reduceIte] at hvalue
      exact signBit_eq_true_of_toReal_neg (hvalue ▸ neg_lt_zero.mpr hpositive)

/--
**Nearest-even rounding of a dyadic number, by every descriptor.** When the grid rounding of
the number is at most the largest finite magnitude, `roundDyadic` is finite and denotes it.
Otherwise it is the overflow word of the descriptor: an infinity, the NaN of a format without
one, or the largest finite value of a format in which every encoding is finite.
-/
theorem roundDyadic_spec (fmt : FloatFormat) (d : Numerics.Dyadic) :
    (|roundAt fmt d.toReal| ≤ toReal (posMaxFinite fmt) →
        isFinite (roundDyadic fmt d) = true ∧ toReal (roundDyadic fmt d) = roundAt fmt d.toReal) ∧
      (toReal (posMaxFinite fmt) < |roundAt fmt d.toReal| →
        roundDyadic fmt d = nativeOverflow fmt d.negative) := by
  rcases d with ⟨sign, mantissa, exponent⟩
  have hden : (RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).2 ≠ 0 :=
    RationalBinary.scaleByPowerOfTwo_snd_ne_zero mantissa 1 exponent (by decide)
  generalize hscaled : RationalBinary.scaleByPowerOfTwo mantissa 1 exponent = scaled at hden
  have hgeneral : roundDyadic fmt ⟨sign, mantissa, exponent⟩ =
      Policy.roundRatGeneralOfDenNeZero fmt { rounding := .nearest, overflow := .native } 0 sign
        scaled.1 scaled.2 hden := by
    rw [← roundDyadicGeneral_eq_roundDyadic]
    subst hscaled
    exact (Policy.roundRatGeneralOfDenNeZero_nearest_dyadic_eq fmt sign 0 mantissa exponent).symm
  have hvalue : signedScaledRatToReal sign scaled.1 scaled.2 0 =
      (Numerics.Dyadic.mk sign mantissa exponent).toReal := by
    have h := scaleByPowerOfTwo_real mantissa 1 exponent
    rw [hscaled] at h
    cases sign <;>
      simp [signedScaledRatToReal, scaledRatToReal, h, Numerics.Dyadic.toReal,
        Numerics.Dyadic.signedSignificand, Model.bpow, Flocq.bpow_binaryRadix]
  rw [hgeneral, ← hvalue]
  have hiff := Policy.isFinite_roundRatGeneral_nearest_iff fmt .native 0 sign scaled.1 scaled.2
    hden
  have hword : Policy.overflowResult fmt .native .nearest sign = nativeOverflow fmt sign := by
    simp [Policy.overflowResult, Policy.overflowRoundsMagnitudeUp, directedOverflow]
  constructor
  · intro hrange
    have hfinite := hiff.mpr (.inr hrange)
    refine ⟨hfinite, ?_⟩
    rw [Policy.toReal_roundRatGeneral_nearest fmt .native 0 sign scaled.1 scaled.2 hden hfinite]
    split_ifs
    · exact clampAt_eq_self fmt hrange
    · rfl
  · intro hover
    rcases Policy.isFinite_roundRatGeneral_nearest_or_eq_overflow fmt .native 0 sign scaled.1
      scaled.2 hden with hfinite | hoverflow
    · have hsaturates : isFinite (Policy.overflowResult fmt .native .nearest sign) = true := by
        rcases hiff.mp hfinite with h | h
        · exact h
        · exact absurd hover (not_lt.mpr h)
      have hreal := Policy.toReal_roundRatGeneral_nearest fmt .native 0 sign scaled.1 scaled.2
        hden hfinite
      rw [ite_eq_left hsaturates] at hreal
      have hmax := toReal_posMaxFinite_pos fmt
      have hclamp : clampAt fmt (roundAt fmt (signedScaledRatToReal sign scaled.1 scaled.2 0)) =
          (if sign then (-1 : ℝ) else 1) * toReal (posMaxFinite fmt) := by
        rw [Policy.roundAt_rat_eq fmt sign scaled.1 scaled.2 hden, mul_assoc] at hover ⊢
        have hnonneg : (0 : ℝ) ≤ _ := mul_nonneg (Nat.cast_nonneg
          (roundQuotientEven (RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
            (-fexpOf fmt (RationalBinary.floorLog2 scaled.1 scaled.2 + 1))).1
            (RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
              (-fexpOf fmt (RationalBinary.floorLog2 scaled.1 scaled.2 + 1))).2))
          (Flocq.bpow.pos binaryRadix
            (fexpOf fmt (RationalBinary.floorLog2 scaled.1 scaled.2 + 1))).le
        rw [clampAt_signedMagnitude fmt sign hnonneg, min_eq_right]
        cases sign <;> simpa [abs_of_nonneg hnonneg] using hover.le
      rw [← hword]
      apply eq_of_toReal_eq_of_nonzero
      · rw [hreal, hclamp, Policy.toReal_overflowResult_nearest fmt .native sign hsaturates]
      · rw [hreal, hclamp]
        cases sign <;> simp [hmax.ne']
    · rw [hoverflow, hword]

end FloatLib.Floats.Formats.BinaryInterchange.Model
