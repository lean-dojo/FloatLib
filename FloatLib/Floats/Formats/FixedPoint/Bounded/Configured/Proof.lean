/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Runtime
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Semantics.Proof

/-!
# Correctness of configured bounded fixed-point operations

Complete word conversions recover the stored code, and encoding preserves in-range words.
Arithmetic with `(overflow := .wrap)` decodes to centered modular arithmetic on signed
coefficients. The default `.reject` addition and subtraction are exact whenever they succeed, and
so is multiplication at a positive destination width. At positive widths,
`(overflow := .saturate)` decodes to the exact coefficient clamped to the signed range.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.BoundedFixedPoint

open FloatLib.Numerics
open FloatLib.Numerics.Representations

variable {radix : Radix} {fractionalDigits p q : Nat}
variable {width leftWidth rightWidth outWidth : Nat}

/-- Unwrapping a freshly wrapped bounded fixed-point code returns the original code. -/
@[simp, grind =] theorem toCode_ofCode
    (code : Formats.FixedPoint.Bounded.Code radix fractionalDigits width) :
    toCode (ofCode code) = code :=
  rfl

/-- Rewrapping the code of a bounded fixed-point value returns the original value. -/
@[simp, grind =] theorem ofCode_toCode
    (value : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    ofCode value.toCode = value :=
  ExecFloat.ofRaw_raw value

/-- Reconstructing a value from its complete word preserves the value. -/
@[simp, grind =] theorem ofNatBits_toNatBits
    (value : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    ofNatBits (toNatBits value) = value := by
  rw [ofNatBits, toNatBits,
    FloatLib.Numerics.Representations.FixedInt.ofNatBits_toNatBits]
  exact ofCode_toCode value

/-- An in-range word is unchanged by bounded fixed-point encoding and decoding. -/
@[simp, grind =] theorem toNatBits_ofNatBits_of_lt
    (bits : Nat) (bits_lt : bits < 2 ^ width) :
    toNatBits
        (ofNatBits (radix := radix) (fractionalDigits := fractionalDigits)
          (width := width) bits) =
      bits := by
  simpa [ofNatBits, toNatBits] using
    FloatLib.Numerics.Representations.FixedInt.toNatBits_ofNatBits_of_lt
      (width := width) bits bits_lt

/-- Constructing from an integer stores its two's-complement residue at the selected width. -/
@[simp, grind =] theorem coefficient_ofCoefficient (stored : Int) :
    coefficient
      (ofCoefficient stored :
        ExecFloat.BoundedFixedPoint radix fractionalDigits width) =
      (FloatLib.Numerics.Representations.FixedInt.ofInt
        (width := width) stored).toInt :=
  rfl

/-- Addition with `.wrap` decodes to the coefficient sum, centered modulo `2 ^ width`. -/
@[simp, grind =] theorem toRat_add_wrap
    (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    toRat (add left right .wrap) =
      Formats.FixedPoint.Bounded.valueOfCoefficient radix fractionalDigits
        ((left.coefficient + right.coefficient).bmod (2 ^ width)) :=
  Formats.FixedPoint.Bounded.toRat_wrapAdd left.toCode right.toCode

/-- Subtraction with `.wrap` decodes to the coefficient difference, centered modulo `2 ^ width`. -/
@[simp, grind =] theorem toRat_sub_wrap
    (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    toRat (sub left right .wrap) =
      Formats.FixedPoint.Bounded.valueOfCoefficient radix fractionalDigits
        ((left.coefficient - right.coefficient).bmod (2 ^ width)) :=
  Formats.FixedPoint.Bounded.toRat_wrapSub left.toCode right.toCode

/-- Multiplication with `.wrap` decodes to the coefficient product, centered mod `2 ^ outWidth`. -/
@[simp, grind =] theorem toRat_mul_wrap
    (left : ExecFloat.BoundedFixedPoint radix p leftWidth)
    (right : ExecFloat.BoundedFixedPoint radix q rightWidth) :
    toRat (mul outWidth left right .wrap) =
      Formats.FixedPoint.Bounded.valueOfCoefficient radix (p + q)
        ((left.coefficient * right.coefficient).bmod (2 ^ outWidth)) :=
  Formats.FixedPoint.Bounded.toRat_wrapMul left.toCode right.toCode

/-- Addition succeeds with the wrapped sum when the exact coefficient sum fits. -/
theorem add_eq_some (hwidth : 0 < width)
    (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width)
    (hresult : FixedInt.InRange width (left.coefficient + right.coefficient)) :
    add left right = some (add left right .wrap) :=
  congrArg (Option.map ofCode)
    (FixedInt.checkedAdd_eq_some hwidth left.toCode right.toCode hresult)

/-- Subtraction succeeds with the wrapped difference when the exact coefficient fits. -/
theorem sub_eq_some (hwidth : 0 < width)
    (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width)
    (hresult : FixedInt.InRange width (left.coefficient - right.coefficient)) :
    sub left right = some (sub left right .wrap) :=
  congrArg (Option.map ofCode)
    (FixedInt.checkedSub_eq_some hwidth left.toCode right.toCode hresult)

/-- Multiplication succeeds with the encoded product when the exact coefficient fits. -/
theorem mul_eq_some
    (left : ExecFloat.BoundedFixedPoint radix p leftWidth)
    (right : ExecFloat.BoundedFixedPoint radix q rightWidth)
    (hresult : FixedInt.InRange outWidth (left.coefficient * right.coefficient)) :
    mul outWidth left right =
      some (ofCoefficient (left.coefficient * right.coefficient)) :=
  congrArg (Option.map ofCode)
    (Formats.FixedPoint.Bounded.checkedMul_eq_some left.toCode right.toCode hresult)

/--
Rejecting addition is exact: whenever it returns a value, that value decodes to the rational sum of
the operands. No width hypothesis is needed because success already certifies the absence of
signed overflow.
-/
theorem toRat_of_add_eq_some
    {left right result : ExecFloat.BoundedFixedPoint radix fractionalDigits width}
    (hsome : add left right = some result) :
    toRat result = toRat left + toRat right := by
  dsimp only [add, Formats.FixedPoint.Bounded.checkedAdd, FixedInt.checkedAdd] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · rename_i hoverflow
    simp only [Option.map_some, Option.some.injEq] at hsome
    subst hsome
    unfold toRat Formats.FixedPoint.Bounded.toRat Formats.FixedPoint.Bounded.coefficient
    change ((FixedInt.wrapAdd left.toCode right.toCode).toInt : ℚ) / _ = _
    rw [FixedInt.wrapAdd, FixedInt.toInt,
      BitVec.toInt_add_of_not_saddOverflow (by simpa using hoverflow), Int.cast_add]
    exact add_div _ _ _

/--
Rejecting subtraction is exact: whenever it returns a value, that value decodes to the rational
difference of the operands.
-/
theorem toRat_of_sub_eq_some
    {left right result : ExecFloat.BoundedFixedPoint radix fractionalDigits width}
    (hsome : sub left right = some result) :
    toRat result = toRat left - toRat right := by
  dsimp only [sub, Formats.FixedPoint.Bounded.checkedSub, FixedInt.checkedSub] at hsome
  split at hsome
  · exact absurd hsome (by simp)
  · rename_i hoverflow
    simp only [Option.map_some, Option.some.injEq] at hsome
    subst hsome
    unfold toRat Formats.FixedPoint.Bounded.toRat Formats.FixedPoint.Bounded.coefficient
    change ((FixedInt.wrapSub left.toCode right.toCode).toInt : ℚ) / _ = _
    rw [FixedInt.wrapSub, FixedInt.toInt,
      BitVec.toInt_sub_of_not_ssubOverflow (by simpa using hoverflow), Int.cast_sub]
    exact sub_div _ _ _

/--
Rejecting multiplication is exact: whenever it returns a value at a positive destination width,
that value decodes to the rational product of the operands at the composed scale.
-/
theorem toRat_of_mul_eq_some (houtWidth : 0 < outWidth)
    {left : ExecFloat.BoundedFixedPoint radix p leftWidth}
    {right : ExecFloat.BoundedFixedPoint radix q rightWidth}
    {result : ExecFloat.BoundedFixedPoint radix (p + q) outWidth}
    (hsome : mul outWidth left right = some result) :
    toRat result = toRat left * toRat right := by
  have hrange : FixedInt.InRange outWidth (left.coefficient * right.coefficient) := by
    by_contra hrange
    unfold mul Formats.FixedPoint.Bounded.checkedMul at hsome
    simp at hsome
    exact hrange hsome.1
  rw [mul_eq_some left right hrange, Option.some.injEq] at hsome
  subst hsome
  exact Formats.FixedPoint.Bounded.toRat_ofInt_mul_of_inRange houtWidth
    left.toCode right.toCode hrange

/-- Addition with `.saturate` decodes to exact coefficient addition followed by clamping. -/
@[simp, grind =] theorem toRat_add_saturate (hwidth : 0 < width)
    (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    toRat (add left right .saturate) =
      Formats.FixedPoint.Bounded.valueOfCoefficient radix fractionalDigits
        (FixedInt.clamp width (left.coefficient + right.coefficient)) :=
  Formats.FixedPoint.Bounded.toRat_saturatingAdd hwidth left.toCode right.toCode

/-- Subtraction with `.saturate` decodes to exact coefficient subtraction and clamping. -/
@[simp, grind =] theorem toRat_sub_saturate (hwidth : 0 < width)
    (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    toRat (sub left right .saturate) =
      Formats.FixedPoint.Bounded.valueOfCoefficient radix fractionalDigits
        (FixedInt.clamp width (left.coefficient - right.coefficient)) :=
  Formats.FixedPoint.Bounded.toRat_saturatingSub hwidth left.toCode right.toCode

/-- Multiplication with `.saturate` decodes to the clamped exact product at the composed scale. -/
@[simp, grind =] theorem toRat_mul_saturate (houtWidth : 0 < outWidth)
    (left : ExecFloat.BoundedFixedPoint radix p leftWidth)
    (right : ExecFloat.BoundedFixedPoint radix q rightWidth) :
    toRat (mul outWidth left right .saturate) =
      Formats.FixedPoint.Bounded.valueOfCoefficient radix (p + q)
        (FixedInt.clamp outWidth (left.coefficient * right.coefficient)) :=
  Formats.FixedPoint.Bounded.toRat_saturatingMul houtWidth left.toCode right.toCode

end FloatLib.Floats.ExecFloat.BoundedFixedPoint
