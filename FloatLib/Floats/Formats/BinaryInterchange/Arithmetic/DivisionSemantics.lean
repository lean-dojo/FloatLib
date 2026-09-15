/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof

/-!
# Correctness of IEEE binary division

The exact scaled-rational rounding theorem gives the real-number correctness contract for the
public `Model.div` operation. The refinement sits above the dyadic arithmetic and rational
packing layers to keep those dependencies acyclic.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Finite division by a nonzero finite operand cannot overflow when the exact real quotient is within
the destination's largest finite magnitude.
-/
theorem isFinite_div_of_abs_div_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt) (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false)
    (hbound : |toReal x / toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (div x y) = true := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  have hdyMant : dy.significand ≠ 0 := by
    intro hmant
    have hzero :=
      isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hdy hmant
    simp [hy0] at hzero
  by_cases hdxMant : dx.significand = 0
  · have hdiv :
      div x y =
          if Bool.xor dx.negative dy.negative then negZero fmt else posZero fmt := by
      simp [Proof.div_eq_spec, Spec.div, hdx, hdy, hdyMant, hdxMant]
      rw [zero_eq_signedZero_of_isIEEE fmt hfmt]
      cases dx.negative <;> cases dy.negative <;> rfl
    rw [hdiv]
    split
    · exact isFinite_negZero fmt (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt)
    · exact isFinite_posZero fmt
  · let sign := Bool.xor dx.negative dy.negative
    have hdiv :
        div x y =
          roundRatScaled fmt sign dx.significand dy.significand (dx.exponent - dy.exponent) := by
      simp [Proof.div_eq_spec, Spec.div, hdx, hdy, hdyMant, hdxMant, sign]
    rw [hdiv]
    apply isFinite_roundRatScaled_of_abs_le_posMaxFinite fmt sign
      dx.significand dy.significand (dx.exponent - dy.exponent) hfmt
    · exact hdyMant
    · rw [signedScaledRatToReal_eq_div_toReal dx dy]
      simpa [toReal_eq, hdx, hdy] using hbound

/--
Finite division by a nonzero finite operand is exact real division followed by one nearest-even
format rounding.

The hypothesis `hfin` excludes overflow by asking that the executable quotient be finite;
`toReal_div_eq_roundAt_of_abs_div_le_posMaxFinite` supplies it from a bound on the operands.
-/
theorem toReal_div_eq_roundAt {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false) (hfin : isFinite (div x y) = true) :
    toReal (div x y) = roundAt fmt (toReal x / toReal y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  have hdyMant : dy.significand ≠ 0 := by
    intro hmant
    have hzero :=
      isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hdy hmant
    simp [hy0] at hzero
  by_cases hdxMant : dx.significand = 0
  · have hxReal : toReal x = 0 := by
      simp [toReal_eq, hdx, Numerics.Dyadic.toReal, hdxMant]
    have hdiv :
      div x y =
          if Bool.xor dx.negative dy.negative then negZero fmt else posZero fmt := by
      simp [Proof.div_eq_spec, Spec.div, hdx, hdy, hdyMant, hdxMant]
      rw [zero_eq_signedZero_of_isIEEE fmt hfmt]
      cases dx.negative <;> cases dy.negative <;> rfl
    rw [hdiv, toReal_signedZero fmt hfmt, hxReal, zero_div, roundAt_zero]
  · let sign := Bool.xor dx.negative dy.negative
    have hdiv :
        div x y =
          roundRatScaled fmt sign dx.significand dy.significand (dx.exponent - dy.exponent) := by
      simp [Proof.div_eq_spec, Spec.div, hdx, hdy, hdyMant, hdxMant, sign]
    have hroundFinite :
        isFinite
            (roundRatScaled fmt sign dx.significand dy.significand
              (dx.exponent - dy.exponent)) = true := by
      simpa [hdiv] using hfin
    calc
      toReal (div x y) =
          toReal
            (roundRatScaled fmt sign dx.significand dy.significand
              (dx.exponent - dy.exponent)) := by
        rw [hdiv]
      _ = roundAt fmt
          (signedScaledRatToReal sign dx.significand dy.significand
            (dx.exponent - dy.exponent)) :=
        toReal_roundRatScaled_eq_roundAt
          fmt sign dx.significand dy.significand (dx.exponent - dy.exponent)
            hfmt hdxMant hdyMant hroundFinite
      _ = roundAt fmt (dx.toReal / dy.toReal) := by
        rw [signedScaledRatToReal_eq_div_toReal dx dy]
      _ = roundAt fmt (toReal x / toReal y) := by
        simp [toReal_eq, hdx, hdy]

/--
Finite division under a symbolic exact-quotient bound is exact real division followed by one
nearest-even format rounding.
-/
theorem toReal_div_eq_roundAt_of_abs_div_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt) (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false)
    (hbound : |toReal x / toReal y| ≤ toReal (posMaxFinite fmt)) :
    toReal (div x y) = roundAt fmt (toReal x / toReal y) :=
  toReal_div_eq_roundAt x y hfmt hx hy hy0
    (isFinite_div_of_abs_div_le_posMaxFinite x y hfmt hx hy hy0 hbound)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
