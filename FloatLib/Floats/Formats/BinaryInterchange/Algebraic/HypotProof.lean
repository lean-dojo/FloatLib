/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SqrtSemantics

/-!
# Correct rounding of the binary Euclidean norm

Exact dyadic multiplication and addition form the sum of squares. The arbitrary-mantissa
square-root theorem then rounds its square root once. Neither the squares nor their sum must
fit the output format, so intermediate overflow and underflow cannot change the result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats.Formats.Flocq

namespace Algebraic

/-- The existing finite square-root kernel accepts any exact nonnegative dyadic radicand. -/
theorem toReal_sqrtPositiveDyadic (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mantissa : Nat) (exponent : Int)
    (hfinite : isFinite (FiniteSqrt.sqrtPositiveDyadic fmt mantissa exponent) = true) :
    toReal (FiniteSqrt.sqrtPositiveDyadic fmt mantissa exponent) =
      roundAt fmt (Real.sqrt ((mantissa : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent)) := by
  by_cases hm : mantissa = 0
  · simp [hm, FiniteSqrt.sqrtPositiveDyadic, toReal_posZero]
  · simp only [FiniteSqrt.sqrtPositiveDyadic, hm, dite_false, hfmt, ite_true,
      NativeModelSqrt.sqrt_eq] at hfinite ⊢
    exact toReal_ofModel_sqrt_finite_eq_roundAt fmt hfmt mantissa exponent hm hfinite

/-- The exact-dyadic norm rounds the square root of the real sum of squares once. -/
theorem toReal_hypotDyadic (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (left right : Numerics.Dyadic)
    (hfinite : isFinite (hypotDyadic fmt left right) = true) :
    toReal (hypotDyadic fmt left right) =
      roundAt fmt (Real.sqrt (left.toReal ^ 2 + right.toReal ^ 2)) := by
  rw [hypotDyadic, Numerics.Dyadic.sumSquares_eq] at hfinite ⊢
  let sum := (left.mul left).add (right.mul right)
  have hsum : sum.toReal = left.toReal ^ 2 + right.toReal ^ 2 := by
    have hrat := Numerics.Dyadic.add_toRat (left.mul left) (right.mul right)
    have hreal := congrArg (fun q : Rat => (q : ℝ)) hrat
    simpa [sum, Numerics.Dyadic.mul_toRat, pow_two] using hreal
  have hmagnitude : (sum.significand : ℝ) *
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix sum.exponent =
      left.toReal ^ 2 + right.toReal ^ 2 := by
    rw [← Dyadic.abs_toReal, hsum, abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  rw [toReal_sqrtPositiveDyadic fmt hfmt _ _ hfinite, hmagnitude]

end Algebraic

/-- Finite operands take the exact-dyadic norm path. -/
theorem hypot_eq_hypotDyadic {fmt : FloatFormat} (left right : Model fmt)
    {a b : Numerics.Dyadic}
    (hleft : toDyadic? left = some a) (hright : toDyadic? right = some b) :
    hypot left right = Algebraic.hypotDyadic fmt a b := by
  have hnan : chooseNaN2 left right = none :=
    chooseNaN2_none_of_isFinite left right
      (isFinite_eq_true_of_toDyadic?_some hleft) (isFinite_eq_true_of_toDyadic?_some hright)
  simp [hypot, isSNaN_eq_false_of_toDyadic?_some hleft,
    isSNaN_eq_false_of_toDyadic?_some hright,
    isInf_eq_false_of_toDyadic?_some hleft, isInf_eq_false_of_toDyadic?_some hright,
    hnan, hleft, hright]

/--
Under a conventional IEEE descriptor a finite norm has finite operands. A signaling NaN gives a
quiet NaN, an infinity gives positive infinity even beside a quiet NaN, and a remaining quiet NaN
propagates.
-/
theorem isFinite_of_isFinite_hypot {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {left right : Model fmt} (h : isFinite (hypot left right) = true) :
    isFinite left = true ∧ isFinite right = true := by
  have hquiet {z : Model fmt} (hz : isNaN z = true) : isFinite (quietNaN z) = false :=
    isFinite_eq_false_of_isNaN ((isNaN_quietNaN z).trans hz)
  by_cases hsl : isSNaN left = true
  · simp [hypot, chooseNaN2, hsl, hquiet (isNaN_of_isSNaN hsl)] at h
  by_cases hsr : isSNaN right = true
  · simp [hypot, chooseNaN2, hsl, hsr, hquiet (isNaN_of_isSNaN hsr)] at h
  by_cases hinf : (isInf left || isInf right) = true
  · simp [hypot, hsl, hsr, hinf, isFinite_nativeOverflow hfmt] at h
  by_cases hnl : isNaN left = true
  · simp [hypot, chooseNaN2, hsl, hsr, hinf, hnl, hquiet hnl] at h
  by_cases hnr : isNaN right = true
  · simp [hypot, chooseNaN2, hsl, hsr, hinf, hnl, hnr, hquiet hnr] at h
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hinf hnl hnr
  exact ⟨isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false left hnl hinf.1,
    isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false right hnr hinf.2⟩

/--
The finite IEEE Euclidean norm is one nearest-even rounding of `sqrt (x² + y²)`.

The exact sum may exceed the representable range. Only finiteness of the final result is
required, and it forces finite operands (`isFinite_of_isFinite_hypot`). The theorem includes
subnormal inputs, signed zeros and underflow boundaries.
-/
theorem toReal_hypot_eq_roundAt {fmt : FloatFormat} (left right : Model fmt)
    (hfmt : fmt.isIEEE = true) (hfinite : isFinite (hypot left right) = true) :
    toReal (hypot left right) =
      roundAt fmt (Real.sqrt (toReal left ^ 2 + toReal right ^ 2)) := by
  obtain ⟨hleft, hright⟩ := isFinite_of_isFinite_hypot hfmt hfinite
  obtain ⟨a, ha⟩ := exists_toDyadic?_of_isFinite hleft
  obtain ⟨b, hb⟩ := exists_toDyadic?_of_isFinite hright
  rw [hypot_eq_hypotDyadic left right ha hb] at hfinite ⊢
  rw [Algebraic.toReal_hypotDyadic fmt hfmt a b hfinite]
  simp [toReal_eq, ha, hb]

end FloatLib.Floats.Formats.BinaryInterchange.Model
