/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Bounds

/-!
# Non-NaN results for conventional IEEE directed arithmetic

Rounding gives a finite value or an infinity and never a NaN. That holds in every rounding
direction, nearest-even and nearest-away included, both for dyadic rounding
(`Internal.Directed.isNaN_roundDyadic_eq_false`) and for scaled rational rounding with a nonzero
denominator (`Internal.Directed.isNaN_roundRatScaled_eq_false`). So addition, subtraction,
multiplication and fused multiply-add of finite operands are numbers in every direction, and so
is division of finite operands by a nonzero divisor.

`Status.Proof` uses the addition, multiplication and fused multiply-add theorems, and the
rational-rounding lemma for division, to state the invalid flag from operand classes alone. The
downward and upward specializations at the end are there for the IEEE interval soundness proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-! ## Every rounding direction -/

/-- A conventional IEEE format packs every field pair below the all-ones exponent as a number. -/
private theorem isNaN_ofFields_of_lt_expAllOnesNat {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (sign : Bool) {exponent : Nat} (fraction : Nat) (hexponent : exponent < fmt.expAllOnesNat) :
    isNaN (ofFields fmt sign exponent fraction) = false :=
  isNaN_eq_false_of_isFinite_eq_true _
    (isFinite_ofFields_ieee fmt hfmt sign exponent fraction hexponent)

private theorem isNaN_nativeOverflow_eq_false {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (sign : Bool) : isNaN (nativeOverflow fmt sign) = false := by
  cases sign <;> simp [nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt]

private theorem isNaN_packRoundedSubnormal_eq_false {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) (sign : Bool) {zeroResult : Model fmt}
    (hzero : isNaN zeroResult = false) (fraction : Nat) :
    isNaN (packRoundedSubnormal fmt sign zeroResult fraction) = false := by
  have hone := FloatFormat.one_lt_expAllOnesNat fmt
  unfold packRoundedSubnormal
  split_ifs
  · exact hzero
  · exact isNaN_ofFields_of_lt_expAllOnesNat hfmt sign 0 hone
  · exact isNaN_ofFields_of_lt_expAllOnesNat hfmt sign fraction (by omega)

private theorem isNaN_packRoundedNormal_eq_false {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) (sign : Bool) {overflow : Model fmt}
    (hoverflow : isNaN overflow = false) (totalExponent : Int) (roundedMantissa : Nat) :
    isNaN (packRoundedNormal fmt sign overflow totalExponent roundedMantissa) = false := by
  have hencoding := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  have hmax : fmt.maxFiniteExpField < fmt.expAllOnesNat := by
    have hfour : 4 ≤ 2 ^ fmt.expWidth := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) fmt.expWidth_ge_two
    simp only [FloatFormat.maxFiniteExpField, hencoding, FloatFormat.Encoding.maxFiniteExponent,
      FloatFormat.expAllOnesNat]
    omega
  unfold packRoundedNormal
  dsimp only
  split_ifs <;> first
    | exact hoverflow
    | rename_i hguard
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hguard
      exact isNaN_ofFields_of_lt_expAllOnesNat hfmt sign _ (by omega)

/-- Nearest-even dyadic rounding never produces a NaN in a conventional IEEE format. -/
theorem isNaN_roundDyadic_eq_false
    (fmt : FloatFormat) (d : Numerics.Dyadic) (hfmt : fmt.isIEEE = true) :
    isNaN (roundDyadic fmt d) = false := by
  rw [← roundDyadicGeneral_eq_roundDyadic]
  unfold roundDyadicGeneral
  dsimp only
  split_ifs
  · exact isNaN_zero fmt _
  · exact isNaN_nativeOverflow_eq_false hfmt _
  · exact isNaN_packRoundedSubnormal_eq_false hfmt _ (isNaN_zero fmt _) _
  all_goals
    exact isNaN_packRoundedNormal_eq_false hfmt _ (isNaN_nativeOverflow_eq_false hfmt _) _ _

/-- Toward-zero dyadic rounding is downward for a positive and upward for a negative value. -/
private theorem roundDyadicTowardZero_eq (fmt : FloatFormat) (d : Numerics.Dyadic) :
    roundDyadicTowardZero fmt d =
      if d.negative then roundDyadicUp fmt d else roundDyadicDown fmt d := by
  cases hsign : d.negative <;>
    simp [roundDyadicTowardZero, roundDyadicUp, roundDyadicDown, hsign]

/-- Away-from-zero dyadic rounding is upward for a positive and downward for a negative value. -/
private theorem roundDyadicAway_eq (fmt : FloatFormat) (d : Numerics.Dyadic) :
    roundDyadicAway fmt d =
      if d.negative then roundDyadicDown fmt d else roundDyadicUp fmt d := by
  cases hsign : d.negative <;>
    simp [roundDyadicAway, roundDyadicUp, roundDyadicDown, hsign]

/-- Dyadic rounding in any direction never produces a NaN in a conventional IEEE format. -/
theorem Internal.Directed.isNaN_roundDyadic_eq_false
    (fmt : FloatFormat) (mode : IEEERoundingMode) (d : Numerics.Dyadic)
    (hfmt : fmt.isIEEE = true) :
    isNaN (Internal.Directed.roundDyadic fmt mode d) = false := by
  have hdown := isNaN_roundDyadicDown_eq_false fmt d hfmt
  have hup := isNaN_roundDyadicUp_eq_false fmt d hfmt
  have haway : isNaN (roundDyadicAway fmt d) = false := by
    rw [roundDyadicAway_eq]
    split <;> assumption
  cases mode with
  | nearest => exact Model.isNaN_roundDyadic_eq_false fmt d hfmt
  | nearestAway =>
      simp only [Internal.Directed.roundDyadic, roundDyadicNearestAway]
      split
      · exact haway
      · exact Model.isNaN_roundDyadic_eq_false fmt d hfmt
  | towardZero =>
      simp only [Internal.Directed.roundDyadic, roundDyadicTowardZero_eq]
      split <;> assumption
  | up => exact hup
  | down => exact hdown
  | away => exact haway

/--
Nearest-even scaled rational rounding with a nonzero denominator never produces a NaN in a
conventional IEEE format.
-/
theorem isNaN_roundRatScaled_eq_false
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true) (hdenominator : denominator ≠ 0) :
    isNaN (roundRatScaled fmt sign numerator denominator exponent) = false := by
  have hbias := FloatFormat.expAllOnesNat_eq_two_mul_bias_add_one fmt
  have hone := FloatFormat.one_lt_expAllOnesNat fmt
  have hmax : fmt.ieeeMaxNormalExponent = fmt.bias := rfl
  have hsigned := FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt
  rw [roundRatScaled, dite_eq_left_of_eq_true (eq_true hfmt)]
  unfold ieeeRoundRatScaled
  dsimp only
  simp only [beq_iff_eq, hdenominator, ite_false]
  split_ifs
  all_goals first
    | (simp [isNaN_negZero fmt hsigned]; done)
    | (split <;> exact isNaN_ofFields_of_lt_expAllOnesNat hfmt sign _ (by omega))
    | exact isNaN_ofFields_of_lt_expAllOnesNat hfmt sign _
        (by simp only [Int.ofNat_eq_natCast] at *; omega)

/--
Scaled rational rounding in any direction with a nonzero denominator never produces a NaN in a
conventional IEEE format.
-/
theorem Internal.Directed.isNaN_roundRatScaled_eq_false
    (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hfmt : fmt.isIEEE = true) (hdenominator : denominator ≠ 0) :
    isNaN (Internal.Directed.roundRatScaled fmt mode sign numerator denominator exponent) =
      false := by
  have hmagnitude (roundMagnitudeUp : Bool) :=
    isNaN_roundRatMagnitudeDirectedScaled_eq_false fmt roundMagnitudeUp sign numerator denominator
      exponent hfmt hdenominator
  cases mode with
  | nearest =>
      exact Model.isNaN_roundRatScaled_eq_false fmt sign numerator denominator exponent hfmt
        hdenominator
  | nearestAway =>
      simp only [Internal.Directed.roundRatScaled, roundRatNearestAwayScaled]
      split
      · exact hmagnitude true
      · exact Model.isNaN_roundRatScaled_eq_false fmt sign numerator denominator exponent hfmt
          hdenominator
  | towardZero => exact hmagnitude false
  | up => exact hmagnitude (!sign)
  | down => exact hmagnitude sign
  | away => exact hmagnitude true

/--
In a conventional IEEE format, addition of finite operands never produces a NaN, in every rounding
direction: the exact sum rounds to a number, possibly an infinity.
-/
theorem isNaN_add_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (add x y (mode := mode)) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  by_cases hmode : mode = .nearest
  · subst hmode
    rw [show add x y (mode := .nearest) = roundDyadic fmt (addDyadic dx dy) by
      simp [Proof.add_eq_spec, Spec.add, hdx, hdy]]
    exact isNaN_roundDyadic_eq_false fmt _ hfmt
  · rw [add_eq_of_toDyadic?_some mode hmode hdx hdy]
    split_ifs
    · exact isNaN_zeroForExactSum_eq_false fmt _ _ _
    · exact Internal.Directed.isNaN_roundDyadic_eq_false fmt mode _ hfmt

/--
In a conventional IEEE format, multiplication of finite operands never produces a NaN, in every
rounding direction.
-/
theorem isNaN_mul_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (mul x y (mode := mode)) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  by_cases hmode : mode = .nearest
  · subst hmode
    rw [Proof.mul_eq_spec]
    simp only [Spec.mul, hdx, hdy]
    split
    · exact isNaN_zero fmt _
    · exact isNaN_roundDyadic_eq_false fmt _ hfmt
  · rw [mul_eq_of_toDyadic?_some mode hmode hdx hdy]
    exact Internal.Directed.isNaN_roundDyadic_eq_false fmt mode _ hfmt

/--
In a conventional IEEE format, fused multiply-add of finite operands never produces a NaN, in every
rounding direction: the exact `x * y + z` is rounded once to a number.
-/
theorem isNaN_fma_eq_false_of_isFinite
    {fmt : FloatFormat} (x y z : Model fmt) (mode : IEEERoundingMode)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true) :
    isNaN (fma x y z (mode := mode)) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  obtain ⟨dz, hdz⟩ := exists_toDyadic?_of_isFinite hz
  have hchoose : chooseNaN3 x y z = none := by
    simp [chooseNaN3, isNaN_eq_false_of_isFinite_eq_true x hx,
      isNaN_eq_false_of_isFinite_eq_true y hy, isNaN_eq_false_of_isFinite_eq_true z hz,
      isSNaN_eq_false_of_isNaN_eq_false x (isNaN_eq_false_of_isFinite_eq_true x hx),
      isSNaN_eq_false_of_isNaN_eq_false y (isNaN_eq_false_of_isFinite_eq_true y hy),
      isSNaN_eq_false_of_isNaN_eq_false z (isNaN_eq_false_of_isFinite_eq_true z hz)]
  have hxInf := isInf_eq_false_of_isFinite_eq_true x hx
  have hyInf := isInf_eq_false_of_isFinite_eq_true y hy
  have hzInf := isInf_eq_false_of_isFinite_eq_true z hz
  by_cases hmode : mode = .nearest
  · subst hmode
    change isNaN (fma x y z) = false
    rw [Proof.fma_eq_spec]
    simp only [Spec.fma, hchoose, hxInf, hyInf, hzInf, hdx, hdy, hdz, Bool.or_false,
      Bool.false_eq_true, ite_false]
    exact isNaN_roundDyadic_eq_false fmt _ hfmt
  · rw [← Internal.Directed.fma_eq]
    cases mode <;> first
      | exact absurd rfl hmode
      | simp only [Internal.Directed.fma, hchoose, withNaNSelection_of_none, hxInf, hyInf, hzInf,
          Bool.or_false, Bool.false_eq_true, dite_false, finiteDyadic_eq_of_toDyadic _ hdx,
          finiteDyadic_eq_of_toDyadic _ hdy, finiteDyadic_eq_of_toDyadic _ hdz]
        split_ifs
        · exact isNaN_zeroForExactSum_eq_false fmt _ _ _
        · exact Internal.Directed.isNaN_roundDyadic_eq_false fmt _ _ hfmt

/--
In a conventional IEEE format, subtraction of finite operands never produces a NaN, in every
rounding direction: it is addition of the negated right operand.
-/
theorem isNaN_sub_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (sub x y (mode := mode)) = false := by
  rw [← Internal.Directed.sub_eq]
  change isNaN (Internal.Directed.add mode x (neg y)) = false
  rw [Internal.Directed.add_eq]
  exact isNaN_add_eq_false_of_isFinite x (neg y) mode hfmt hx (by simpa using hy)

/--
In a conventional IEEE format, division of a finite dividend by a finite nonzero divisor never
produces a NaN, in every rounding direction: the exact quotient is zero or rounds to a number.
-/
theorem isNaN_div_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hy0 : isZero y = false) :
    isNaN (div x y (mode := mode)) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  have hdyMant := significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdy hy0
  by_cases hmode : mode = .nearest
  · subst hmode
    rw [Proof.div_eq_spec]
    simp only [Spec.div, hdx, hdy, beq_iff_eq, hdyMant, ite_false]
    split
    · exact isNaN_zero fmt _
    · exact isNaN_roundRatScaled_eq_false fmt _ _ _ _ hfmt hdyMant
  · rw [div_eq_of_toDyadic?_some mode hmode hdx hdy hy0]
    exact Internal.Directed.isNaN_roundRatScaled_eq_false fmt mode _ _ _ _ hfmt hdyMant

/-! ## Downward and upward specializations -/

/-- In a conventional IEEE format, directed-down addition is non-NaN on finite operands. -/
theorem isNaN_add_down_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (add x y (mode := .down)) = false :=
  isNaN_add_eq_false_of_isFinite x y .down hfmt hx hy

/-- In a conventional IEEE format, directed-up addition is non-NaN on finite operands. -/
theorem isNaN_add_up_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (add x y (mode := .up)) = false :=
  isNaN_add_eq_false_of_isFinite x y .up hfmt hx hy

/-- In a conventional IEEE format, directed-down multiplication is non-NaN on finite operands. -/
theorem isNaN_mul_down_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (mul x y (mode := .down)) = false :=
  isNaN_mul_eq_false_of_isFinite x y .down hfmt hx hy

/-- In a conventional IEEE format, directed-up multiplication is non-NaN on finite operands. -/
theorem isNaN_mul_up_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (mul x y (mode := .up)) = false :=
  isNaN_mul_eq_false_of_isFinite x y .up hfmt hx hy

/--
In a conventional IEEE format, directed-down division is non-NaN on finite operands with a nonzero
divisor.
-/
theorem isNaN_div_down_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false) :
    isNaN (div x y (mode := .down)) = false :=
  isNaN_div_eq_false_of_isFinite x y .down hfmt hx hy hy0

/--
In a conventional IEEE format, directed-up division is non-NaN on finite operands with a nonzero
divisor.
-/
theorem isNaN_div_up_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false) :
    isNaN (div x y (mode := .up)) = false :=
  isNaN_div_eq_false_of_isFinite x y .up hfmt hx hy hy0

/-- In a conventional IEEE format, directed-down subtraction is non-NaN on finite operands. -/
theorem isNaN_sub_down_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (sub x y (mode := .down)) = false :=
  isNaN_sub_eq_false_of_isFinite x y .down hfmt hx hy

/-- In a conventional IEEE format, directed-up subtraction is non-NaN on finite operands. -/
theorem isNaN_sub_up_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (sub x y (mode := .up)) = false :=
  isNaN_sub_eq_false_of_isFinite x y .up hfmt hx hy

end Model
end FloatLib.Floats.Formats.BinaryInterchange
