/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Bounded.Semantics.Core
public import FloatLib.Numerics.Representations.FixedInt.Semantics.Arithmetic
public import FloatLib.Numerics.Operation.Proof.Finite

/-!
# Correctness of bounded fixed-point semantics

The bounded fixed-point kernels satisfy the rational contracts defined in `Semantics.Core`. The
operation contracts distinguish three policies:

* wrapping operations denote centered reduction of the exact coefficient;
* checked operations denote exact rational arithmetic when the destination coefficient fits;
* saturating operations denote exact coefficient arithmetic followed by signed-range clamping.

The wrapping addition, subtraction, and multiplication kernels use direct `BitVec` operations.
-/

@[expose] public section

open FloatLib.Numerics
open FloatLib.Numerics.Representations

namespace FloatLib.Floats.Formats.FixedPoint.Bounded

/-- The storage scale is always positive. -/
theorem scale_pos (radix : Radix) (fractionalDigits : Nat) :
    0 < scale radix fractionalDigits := by
  unfold scale
  apply Nat.pow_pos
  exact lt_of_lt_of_le (by norm_num) radix.base_valid

/-- The storage scale is nonzero. -/
theorem scale_ne_zero (radix : Radix) (fractionalDigits : Nat) :
    scale radix fractionalDigits ≠ 0 :=
  Nat.ne_of_gt (scale_pos radix fractionalDigits)

/-- Bounded decoding is `valueOfCoefficient` applied to the stored signed coefficient. -/
@[simp] theorem toRat_eq_valueOfCoefficient
    {radix : Radix} {fractionalDigits width : Nat}
    (code : Code radix fractionalDigits width) :
    toRat radix fractionalDigits code =
      valueOfCoefficient radix fractionalDigits (coefficient code) :=
  rfl

/-- Coefficient recovery is exact on every bounded fixed-point code. -/
theorem coefficientOf_toRat
    {radix : Radix} {fractionalDigits width : Nat}
    (code : Code radix fractionalDigits width) :
    coefficientOf radix fractionalDigits (toRat radix fractionalDigits code) =
      coefficient code := by
  unfold coefficientOf toRat
  rw [show
    (coefficient code : ℚ) / (scale radix fractionalDigits : Nat) *
        (scale radix fractionalDigits : Nat) = coefficient code by
      field_simp [scale_ne_zero radix fractionalDigits]]
  exact roundRatEven_intCast _

/-- Forgetting the coefficient bound preserves the exact rational value. -/
@[simp] theorem toUnbounded_toRat
    {radix : Radix} {fractionalDigits width : Nat}
    (code : Code radix fractionalDigits width) :
    FixedPoint.Code.toRat (toUnbounded code) =
      toRat radix fractionalDigits code :=
  rfl

/-- Representation in the bounded system is equality of decoded rational values. -/
@[simp] theorem numericalSystem_represents_iff
    {radix : Radix} {fractionalDigits width : Nat}
    (code : Code radix fractionalDigits width) (value : ℚ) :
    (numericalSystem radix fractionalDigits width).Represents code value ↔
      toRat radix fractionalDigits code = value := by
  simp [NumericalSystem.Represents, numericalSystem]

/-- Decoding wrapping addition exposes centered coefficient reduction modulo `2 ^ width`. -/
theorem toRat_wrapAdd
    {radix : Radix} {fractionalDigits width : Nat}
    (left right : Code radix fractionalDigits width) :
    toRat radix fractionalDigits (wrapAdd left right) =
      valueOfCoefficient radix fractionalDigits
        ((coefficient left + coefficient right).bmod (2 ^ width)) := by
  unfold Code at left right
  simp [toRat, valueOfCoefficient, coefficient, wrapAdd, FixedInt.toInt_wrapAdd]

/-- Decoding wrapping subtraction exposes centered coefficient reduction modulo `2 ^ width`. -/
theorem toRat_wrapSub
    {radix : Radix} {fractionalDigits width : Nat}
    (left right : Code radix fractionalDigits width) :
    toRat radix fractionalDigits (wrapSub left right) =
      valueOfCoefficient radix fractionalDigits
        ((coefficient left - coefficient right).bmod (2 ^ width)) := by
  unfold Code at left right
  simp [toRat, valueOfCoefficient, coefficient, wrapSub, FixedInt.toInt_wrapSub]

/-- Wrapping multiplication stores the exact coefficient product modulo `2 ^ outWidth`. -/
theorem coefficient_wrapMul
    {leftWidth rightWidth outWidth : Nat}
    (left : FixedInt leftWidth) (right : FixedInt rightWidth) :
    coefficient (wrapMul outWidth left right) =
      (coefficient left * coefficient right).bmod (2 ^ outWidth) := by
  change (wrapMul outWidth left right).toInt =
    (left.bits.toInt * right.bits.toInt).bmod (2 ^ outWidth)
  rw [wrapMul, FixedInt.toInt, BitVec.toInt_mul]
  by_cases hleft : leftWidth ≤ outWidth
  · rw [BitVec.toInt_signExtend_of_le hleft]
    by_cases hright : rightWidth ≤ outWidth
    · rw [BitVec.toInt_signExtend_of_le hright]
    · rw [BitVec.toInt_signExtend_eq_toInt_bmod_of_le _ (Nat.le_of_not_ge hright)]
      simp
  · rw [BitVec.toInt_signExtend_eq_toInt_bmod_of_le _ (Nat.le_of_not_ge hleft)]
    by_cases hright : rightWidth ≤ outWidth
    · rw [BitVec.toInt_signExtend_of_le hright]
      simp
    · rw [BitVec.toInt_signExtend_eq_toInt_bmod_of_le _ (Nat.le_of_not_ge hright)]
      simp

/-- Decoding wrapping multiplication exposes the reduced product at the composed scale. -/
theorem toRat_wrapMul
    {radix : Radix} {p q leftWidth rightWidth outWidth : Nat}
    (left : Code radix p leftWidth) (right : Code radix q rightWidth) :
    toRat radix (p + q) (wrapMul outWidth left right) =
      valueOfCoefficient radix (p + q)
        ((coefficient left * coefficient right).bmod (2 ^ outWidth)) := by
  unfold Code at left right
  unfold toRat valueOfCoefficient
  rw [coefficient_wrapMul]

/-- Checked multiplication returns the exact product when it fits the destination width. -/
theorem checkedMul_eq_some
    {leftWidth rightWidth outWidth : Nat}
    (left : FixedInt leftWidth) (right : FixedInt rightWidth)
    (hresult : FixedInt.InRange outWidth (coefficient left * coefficient right)) :
    checkedMul outWidth left right =
      some (FixedInt.ofInt (coefficient left * coefficient right)) := by
  change FixedInt.InRange outWidth (left.toInt * right.toInt) at hresult
  simp [checkedMul, hresult, coefficient]

/-- Decoding saturating addition exposes exact coefficient addition followed by clamping. -/
theorem toRat_saturatingAdd
    {radix : Radix} {fractionalDigits width : Nat} (hwidth : 0 < width)
    (left right : Code radix fractionalDigits width) :
    toRat radix fractionalDigits (saturatingAdd left right) =
      valueOfCoefficient radix fractionalDigits
        (FixedInt.clamp width (coefficient left + coefficient right)) := by
  unfold Code at left right
  simp [toRat, valueOfCoefficient, coefficient, saturatingAdd,
    FixedInt.toInt_saturatingAdd hwidth]

/-- Decoding saturating subtraction exposes exact coefficient subtraction followed by clamping. -/
theorem toRat_saturatingSub
    {radix : Radix} {fractionalDigits width : Nat} (hwidth : 0 < width)
    (left right : Code radix fractionalDigits width) :
    toRat radix fractionalDigits (saturatingSub left right) =
      valueOfCoefficient radix fractionalDigits
        (FixedInt.clamp width (coefficient left - coefficient right)) := by
  unfold Code at left right
  simp [toRat, valueOfCoefficient, coefficient, saturatingSub,
    FixedInt.toInt_saturatingSub hwidth]

/-- Decoding saturating multiplication exposes the clamped product at the composed scale. -/
theorem toRat_saturatingMul
    {radix : Radix} {p q leftWidth rightWidth outWidth : Nat}
    (houtWidth : 0 < outWidth)
    (left : Code radix p leftWidth) (right : Code radix q rightWidth) :
    toRat radix (p + q) (saturatingMul outWidth left right) =
      valueOfCoefficient radix (p + q)
        (FixedInt.clamp outWidth (coefficient left * coefficient right)) := by
  unfold Code at left right
  simp [toRat, valueOfCoefficient, coefficient, saturatingMul,
    FixedInt.toInt_ofIntSaturating houtWidth]

/--
Decoding a wrapped sum whose exact coefficient fits the width gives the exact rational sum.
-/
theorem toRat_wrapAdd_of_inRange
    {radix : Radix} {fractionalDigits width : Nat} (hwidth : 0 < width)
    (left right : Code radix fractionalDigits width)
    (hresult : FixedInt.InRange width (coefficient left + coefficient right)) :
    toRat radix fractionalDigits (wrapAdd left right) =
      toRat radix fractionalDigits left + toRat radix fractionalDigits right := by
  unfold Code at left right
  simp only [toRat]
  rw [show coefficient (wrapAdd left right) = coefficient left + coefficient right from
    FixedInt.toInt_wrapAdd_of_inRange hwidth left right hresult, Int.cast_add, add_div]

/--
Decoding a wrapped difference whose exact coefficient fits the width gives the exact rational
difference.
-/
theorem toRat_wrapSub_of_inRange
    {radix : Radix} {fractionalDigits width : Nat} (hwidth : 0 < width)
    (left right : Code radix fractionalDigits width)
    (hresult : FixedInt.InRange width (coefficient left - coefficient right)) :
    toRat radix fractionalDigits (wrapSub left right) =
      toRat radix fractionalDigits left - toRat radix fractionalDigits right := by
  unfold Code at left right
  simp only [toRat]
  rw [show coefficient (wrapSub left right) = coefficient left - coefficient right from
    FixedInt.toInt_wrapSub_of_inRange hwidth left right hresult, Int.cast_sub, sub_div]

/--
Encoding an exact coefficient product that fits the destination width decodes to the rational
product at the composed scale.
-/
theorem toRat_ofInt_mul_of_inRange
    {radix : Radix} {p q leftWidth rightWidth outWidth : Nat}
    (houtWidth : 0 < outWidth)
    (left : Code radix p leftWidth) (right : Code radix q rightWidth)
    (hresult : FixedInt.InRange outWidth (coefficient left * coefficient right)) :
    toRat radix (p + q)
        (FixedInt.ofInt (width := outWidth) (coefficient left * coefficient right) :
          Code radix (p + q) outWidth) =
      toRat radix p left * toRat radix q right := by
  unfold Code at left right
  simp only [toRat]
  rw [show
    coefficient
        (FixedInt.ofInt (width := outWidth) (coefficient left * coefficient right) :
          Code radix (p + q) outWidth) =
      coefficient left * coefficient right from FixedInt.toInt_ofInt_eq_self houtWidth hresult]
  simp only [scale, FixedPoint.scale, pow_add, Int.cast_mul, Nat.cast_mul, Nat.cast_pow]
  exact (div_mul_div_comm _ _ _ _).symm

/--
A checked binary kernel satisfies a rational specification under a precondition once, on
operands meeting the precondition, it returns a code decoding to the specified value.
-/
theorem checked2On_of_toRat_eq
    {radix : Radix} {p q r leftWidth rightWidth outWidth : Nat}
    {run : Code radix p leftWidth → Code radix q rightWidth → Option (Code radix r outWidth)}
    {spec : ℚ → ℚ → ℚ} {pre : ℚ → ℚ → Prop}
    (h : ∀ left right, pre (toRat radix p left) (toRat radix q right) →
      ∃ result, run left right = some result ∧
        toRat radix r result = spec (toRat radix p left) (toRat radix q right)) :
    Operation.Checked2On (numericalSystem radix p leftWidth) (numericalSystem radix q rightWidth)
      (numericalSystem radix r outWidth) run (fun left right => .finite (spec left right)) pre := by
  intro left right leftValue rightValue hpre hleft hright
  obtain rfl := (numericalSystem_represents_iff left leftValue).1 hleft
  obtain rfl := (numericalSystem_represents_iff right rightValue).1 hright
  obtain ⟨result, hrun, hvalue⟩ := h left right hpre
  change Option.map (fun code => NumericalValue.finite (toRat radix r code)) (run left right) = _
  rw [hrun, Option.map_some, hvalue]
  rfl

/-- Wrapping addition refines centered coefficient reduction. -/
theorem wrapAdd_refines (radix : Radix) (fractionalDigits width : Nat) :
    Operation.Finite2 (numericalSystem radix fractionalDigits width)
      (numericalSystem radix fractionalDigits width)
      (numericalSystem radix fractionalDigits width)
      wrapAdd (wrapAddValue radix fractionalDigits width) :=
  Operation.Finite2.ofFinite fun left right => by
    rw [toRat_wrapAdd, wrapAddValue, coefficientOf_toRat, coefficientOf_toRat]

/-- Wrapping subtraction refines centered coefficient reduction. -/
theorem wrapSub_refines (radix : Radix) (fractionalDigits width : Nat) :
    Operation.Finite2 (numericalSystem radix fractionalDigits width)
      (numericalSystem radix fractionalDigits width)
      (numericalSystem radix fractionalDigits width)
      wrapSub (wrapSubValue radix fractionalDigits width) :=
  Operation.Finite2.ofFinite fun left right => by
    rw [toRat_wrapSub, wrapSubValue, coefficientOf_toRat, coefficientOf_toRat]

/-- Cross-width wrapping multiplication refines centered coefficient reduction. -/
theorem wrapMul_refines
    (radix : Radix) (p q leftWidth rightWidth outWidth : Nat) :
    Operation.Finite2 (numericalSystem radix p leftWidth)
      (numericalSystem radix q rightWidth)
      (numericalSystem radix (p + q) outWidth)
      (wrapMul outWidth) (wrapMulValue radix p q outWidth) :=
  Operation.Finite2.ofFinite fun left right => by
    rw [toRat_wrapMul, wrapMulValue, coefficientOf_toRat, coefficientOf_toRat]

/-- Checked addition returns the exact rational sum whenever its coefficient fits. -/
theorem checkedAdd_refines
    {radix : Radix} {fractionalDigits width : Nat} (hwidth : 0 < width) :
    Operation.Checked2On (numericalSystem radix fractionalDigits width)
      (numericalSystem radix fractionalDigits width)
      (numericalSystem radix fractionalDigits width)
      checkedAdd (fun left right : ℚ => .finite (left + right))
      (fun left right =>
        FixedInt.InRange width
          (coefficientOf radix fractionalDigits left +
            coefficientOf radix fractionalDigits right)) :=
  checked2On_of_toRat_eq fun left right hresult => by
    rw [coefficientOf_toRat, coefficientOf_toRat] at hresult
    exact ⟨wrapAdd left right, FixedInt.checkedAdd_eq_some hwidth left right hresult,
      toRat_wrapAdd_of_inRange hwidth left right hresult⟩

/-- Checked subtraction returns the exact rational difference whenever its coefficient fits. -/
theorem checkedSub_refines
    {radix : Radix} {fractionalDigits width : Nat} (hwidth : 0 < width) :
    Operation.Checked2On (numericalSystem radix fractionalDigits width)
      (numericalSystem radix fractionalDigits width)
      (numericalSystem radix fractionalDigits width)
      checkedSub (fun left right : ℚ => .finite (left - right))
      (fun left right =>
        FixedInt.InRange width
          (coefficientOf radix fractionalDigits left -
            coefficientOf radix fractionalDigits right)) :=
  checked2On_of_toRat_eq fun left right hresult => by
    rw [coefficientOf_toRat, coefficientOf_toRat] at hresult
    exact ⟨wrapSub left right, FixedInt.checkedSub_eq_some hwidth left right hresult,
      toRat_wrapSub_of_inRange hwidth left right hresult⟩

/-- Checked multiplication returns the exact rational product whenever its coefficient fits. -/
theorem checkedMul_refines
    {radix : Radix} {p q leftWidth rightWidth outWidth : Nat}
    (houtWidth : 0 < outWidth) :
    Operation.Checked2On (numericalSystem radix p leftWidth)
      (numericalSystem radix q rightWidth)
      (numericalSystem radix (p + q) outWidth)
      (checkedMul outWidth) (fun left right : ℚ => .finite (left * right))
      (fun left right =>
        FixedInt.InRange outWidth
          (coefficientOf radix p left * coefficientOf radix q right)) :=
  checked2On_of_toRat_eq fun left right hresult => by
    rw [coefficientOf_toRat, coefficientOf_toRat] at hresult
    exact ⟨_, checkedMul_eq_some left right hresult,
      toRat_ofInt_mul_of_inRange houtWidth left right hresult⟩

/-- Saturating addition refines exact coefficient addition followed by clamping. -/
theorem saturatingAdd_refines
    {radix : Radix} {fractionalDigits width : Nat} (hwidth : 0 < width) :
    Operation.Finite2 (numericalSystem radix fractionalDigits width)
      (numericalSystem radix fractionalDigits width)
      (numericalSystem radix fractionalDigits width)
      saturatingAdd (saturatingAddValue radix fractionalDigits width) :=
  Operation.Finite2.ofFinite fun left right => by
    rw [toRat_saturatingAdd hwidth, saturatingAddValue, coefficientOf_toRat, coefficientOf_toRat]

/-- Saturating subtraction refines exact coefficient subtraction followed by clamping. -/
theorem saturatingSub_refines
    {radix : Radix} {fractionalDigits width : Nat} (hwidth : 0 < width) :
    Operation.Finite2 (numericalSystem radix fractionalDigits width)
      (numericalSystem radix fractionalDigits width)
      (numericalSystem radix fractionalDigits width)
      saturatingSub (saturatingSubValue radix fractionalDigits width) :=
  Operation.Finite2.ofFinite fun left right => by
    rw [toRat_saturatingSub hwidth, saturatingSubValue, coefficientOf_toRat, coefficientOf_toRat]

/-- Saturating multiplication refines exact coefficient multiplication followed by clamping. -/
theorem saturatingMul_refines
    {radix : Radix} {p q leftWidth rightWidth outWidth : Nat}
    (houtWidth : 0 < outWidth) :
    Operation.Finite2 (numericalSystem radix p leftWidth)
      (numericalSystem radix q rightWidth)
      (numericalSystem radix (p + q) outWidth)
      (saturatingMul outWidth) (saturatingMulValue radix p q outWidth) :=
  Operation.Finite2.ofFinite fun left right => by
    rw [toRat_saturatingMul houtWidth, saturatingMulValue, coefficientOf_toRat,
      coefficientOf_toRat]

end FloatLib.Floats.Formats.FixedPoint.Bounded
