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
Nearest-even division of finite IEEE values by a nonzero divisor, through the decoded operands:
a zero dividend gives the zero of the quotient sign, and any other dividend one `roundRatScaled`
of the exact quotient.
-/
private theorem div_eq_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt) (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hy0 : isZero y = false) :
    ∃ dx dy : Numerics.Dyadic, toDyadic? x = some dx ∧ toDyadic? y = some dy ∧
      dy.significand ≠ 0 ∧
      (dx.significand = 0 →
        div x y = if Bool.xor dx.negative dy.negative then negZero fmt else posZero fmt) ∧
      (dx.significand ≠ 0 →
        div x y =
          roundRatScaled fmt (Bool.xor dx.negative dy.negative) dx.significand dy.significand
            (dx.exponent - dy.exponent)) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  have hdyMant : dy.significand ≠ 0 :=
    significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdy hy0
  refine ⟨dx, dy, hdx, hdy, hdyMant, fun hdxMant => ?_, fun hdxMant => ?_⟩
  · simp [Proof.div_eq_spec, Spec.div, hdx, hdy, hdyMant, hdxMant]
    rw [zero_eq_signedZero_of_isIEEE fmt hfmt]
    cases dx.negative <;> cases dy.negative <;> rfl
  · simp [Proof.div_eq_spec, Spec.div, hdx, hdy, hdyMant, hdxMant]

/--
Under a conventional IEEE descriptor a finite special-operand quotient comes from a finite dividend
and an infinite divisor: a NaN operand gives a NaN, an infinite dividend an infinity or the
invalid-operation NaN, and two non-NaN, non-infinite operands the invalid-operation NaN.
-/
private theorem isFinite_left_and_isInf_right_of_isFinite_divSpecial {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) {x y : Model fmt} (h : isFinite (Spec.divSpecial x y) = true) :
    isFinite x = true ∧ isInf y = true := by
  have hinvalid := isFinite_invalidResult hfmt
  unfold Spec.divSpecial at h
  split at h
  · next nan hnan =>
    simp [isFinite_eq_false_of_isNaN (isNaN_of_chooseNaN2_eq_some hnan)] at h
  · next hnan =>
    rw [chooseNaN2_eq_none_iff] at hnan
    split_ifs at h with hx hy hy'
    · simp [hinvalid] at h
    · simp [isFinite_nativeOverflow hfmt] at h
    · exact ⟨isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnan.1
        (Bool.eq_false_iff.mpr hx), hy'⟩
    · simp [hinvalid] at h

/--
Under a conventional IEEE descriptor a finite quotient has a finite dividend: a NaN operand gives a
NaN, and an infinite dividend gives an infinity or the invalid-operation NaN.
-/
theorem isFinite_left_of_isFinite_div {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {x y : Model fmt} (h : isFinite (div x y) = true) :
    isFinite x = true := by
  rw [Proof.div_eq_spec, Spec.div] at h
  split at h
  · next dx dy hdx hdy => exact isFinite_eq_true_of_toDyadic?_some hdx
  · exact (isFinite_left_and_isInf_right_of_isFinite_divSpecial hfmt h).1

/--
Under a conventional IEEE descriptor a finite quotient has a nonzero divisor: dividing by zero
gives an infinity or the invalid-operation NaN. NaN and infinite divisors are not zeros, so the
divisor need not be finite.
-/
theorem isZero_eq_false_of_isFinite_div {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {x y : Model fmt} (h : isFinite (div x y) = true) :
    isZero y = false := by
  have hinvalid := isFinite_invalidResult hfmt
  by_contra hzero
  have hy := isFinite_eq_true_of_isZero_eq_true y (Bool.eq_true_of_not_eq_false hzero)
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  have hdyZero : dy.significand = 0 := by
    have := isZero_eq_beq_zero_of_toDyadic?_some hdy
    simp_all
  rw [Proof.div_eq_spec, Spec.div, hdy] at h
  cases hdx : toDyadic? x with
  | some dx =>
      rw [hdx] at h
      by_cases hdxZero : dx.significand = 0 <;>
        simp [hdyZero, hdxZero, hinvalid, isFinite_nativeOverflow hfmt] at h
  | none =>
      rw [hdx] at h
      split at h
      · next heq _ => simp at heq
      have hyInf := (isFinite_left_and_isInf_right_of_isFinite_divSpecial hfmt h).2
      rw [isInf_eq_false_of_isFinite_eq_true y hy] at hyInf
      contradiction

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
  obtain ⟨dx, dy, hdx, hdy, hdyMant, hzeroDiv, hdivNonzero⟩ :=
    div_eq_of_isFinite x y hfmt hx hy hy0
  by_cases hdxMant : dx.significand = 0
  · have hdiv := hzeroDiv hdxMant
    rw [hdiv]
    split
    · exact isFinite_negZero fmt (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt)
    · exact isFinite_posZero fmt
  · let sign := Bool.xor dx.negative dy.negative
    have hdiv := hdivNonzero hdxMant
    rw [hdiv]
    apply isFinite_roundRatScaled_of_abs_le_posMaxFinite fmt sign
      dx.significand dy.significand (dx.exponent - dy.exponent) hfmt
    · exact hdyMant
    · rw [signedScaledRatToReal_eq_div_toReal dx dy]
      simpa [toReal_eq, hdx, hdy] using hbound

/--
Division by a finite operand is exact real division followed by one nearest-even format rounding.

The hypothesis `hfin` excludes overflow by asking that the executable quotient be finite. It also
forces a finite dividend and a nonzero divisor (`isFinite_left_of_isFinite_div`,
`isZero_eq_false_of_isFinite_div`), but not a finite divisor: a finite dividend over an infinity
is a signed zero. `toReal_div_eq_roundAt_of_abs_div_le_posMaxFinite` supplies `hfin` from a bound
on the operands.
-/
theorem toReal_div_eq_roundAt {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hy : isFinite y = true)
    (hfin : isFinite (div x y) = true) :
    toReal (div x y) = roundAt fmt (toReal x / toReal y) := by
  have hx := isFinite_left_of_isFinite_div hfmt hfin
  have hy0 := isZero_eq_false_of_isFinite_div hfmt hfin
  obtain ⟨dx, dy, hdx, hdy, hdyMant, hzeroDiv, hdivNonzero⟩ :=
    div_eq_of_isFinite x y hfmt hx hy hy0
  by_cases hdxMant : dx.significand = 0
  · have hxReal : toReal x = 0 := by
      simp [toReal_eq, hdx, Numerics.Dyadic.toReal, hdxMant]
    have hdiv := hzeroDiv hdxMant
    rw [hdiv, toReal_signedZero fmt (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt),
      hxReal, zero_div, roundAt_zero]
  · let sign := Bool.xor dx.negative dy.negative
    have hdiv := hdivNonzero hdxMant
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
            hfmt hroundFinite
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
  toReal_div_eq_roundAt x y hfmt hy
    (isFinite_div_of_abs_div_le_posMaxFinite x y hfmt hx hy hy0 hbound)

/-- Dividing a finite value by a value of magnitude one is exact. -/
theorem toReal_div_of_abs_toReal_eq_one_right {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hx : isFinite x = true) (hy : isFinite y = true)
    (h1 : |toReal y| = 1) :
    toReal (div x y) = toReal x / toReal y := by
  have hy0 : isZero y = false := by
    cases hzero : isZero y with
    | false => rfl
    | true =>
        rw [toReal_eq_zero_of_isZero y hzero, abs_zero] at h1
        exact absurd h1 zero_ne_one
  rw [toReal_div_eq_roundAt_of_abs_div_le_posMaxFinite x y hfmt hx hy hy0 (by
    rw [abs_div, h1, div_one]
    exact abs_toReal_le_posMaxFinite_of_isFinite x hx)]
  rcases (abs_eq zero_le_one).1 h1 with h | h <;> rw [h]
  · rw [div_one, roundAt_toReal_eq x hx]
  · rw [div_neg, div_one, roundAt_neg, IEEERoundingMode.negate, roundAt_toReal_eq x hx]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
