/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Reference
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Decode
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact

/-!
# The formatOf operations in one format

The arithmetic of IEEE 754-2019 §5.4.1 is formatOf arithmetic: operands of any formats and one
rounding into the destination. When the operands and the destination have one format, the
operation is the homogeneous operation of that format. This module proves it for finite
operands, in every rounding direction and for every format descriptor:

* `formatOfAddition_value_eq_add`, `formatOfSubtraction_value_eq_sub`,
  `formatOfMultiplication_value_eq_mul`, `formatOfDivision_value_eq_div` and
  `formatOfFusedMultiplyAdd_value_eq_fma`: the value that the formatOf operation delivers is
  `Model.add`, `sub`, `mul`, `div` and `fma` in the same direction, with the same signed zeros,
  and for division by zero the same infinity or NaN.

So every theorem of the homogeneous operations in a direction (the directed enclosures of
`DirectedSemantics`, the kernel path) applies to the formatOf operations in one format. Operands
that are not finite, the flags and the ternary value are compared with the homogeneous
operations on every pair of a six-bit format by `tests/oracles/ieee2019.sh formatOf`, in six
directions, and are not proved here.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Reduction.Internal (Factor)

variable {fmt : FloatFormat}

/--
In one format and for finite operands, `formatOfAddition` delivers `Model.add`, in every
rounding direction.
-/
theorem formatOfAddition_value_eq_add (x y : Model fmt) (mode : IEEERoundingMode)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    (formatOfAddition fmt x y mode).value = add x y (mode := mode) := by
  obtain ⟨dx, hdx, hsx, -⟩ := KernelPath.toDyadic?_of_isFinite x hx
  obtain ⟨dy, hdy, hsy, -⟩ := KernelPath.toDyadic?_of_isFinite y hy
  rw [formatOfAddition_of_toDyadic?_eq_some hdx hdy mode, Factor.deliver_finite_value,
    KernelPath.add_of_finite mode x y dx dy hdx hdy]
  unfold KernelPath.roundedSum zeroForExactSum
  rw [hsx, hsy]
  simp

/--
In one format and for finite operands, `formatOfSubtraction` delivers `Model.sub`, in every
rounding direction.
-/
theorem formatOfSubtraction_value_eq_sub (x y : Model fmt) (mode : IEEERoundingMode)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    (formatOfSubtraction fmt x y mode).value = sub x y (mode := mode) := by
  rw [KernelPath.sub_eq_add_neg]
  exact formatOfAddition_value_eq_add x (neg y) mode hx (by rwa [isFinite_neg])

/--
In one format and for finite operands, `formatOfMultiplication` delivers `Model.mul`, in every
rounding direction, a zero product with the product of the signs.
-/
theorem formatOfMultiplication_value_eq_mul (x y : Model fmt) (mode : IEEERoundingMode)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    (formatOfMultiplication fmt x y mode).value = mul x y (mode := mode) := by
  obtain ⟨dx, hdx, hsx, -⟩ := KernelPath.toDyadic?_of_isFinite x hx
  obtain ⟨dy, hdy, hsy, -⟩ := KernelPath.toDyadic?_of_isFinite y hy
  rw [formatOfMultiplication_of_toDyadic?_eq_some hdx hdy mode, Factor.deliver_finite_value,
    KernelPath.mul_of_finite mode x y dx dy hdx hdy]
  split
  · rename_i hzero
    simp only at hzero
    rw [hzero, Internal.Directed.roundDyadic_zero, hsx, hsy]
  · rfl

/--
In one format and for finite operands, `formatOfFusedMultiplyAdd` delivers `Model.fma`, in
every rounding direction.
-/
theorem formatOfFusedMultiplyAdd_value_eq_fma (x y z : Model fmt) (mode : IEEERoundingMode)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true) :
    (formatOfFusedMultiplyAdd fmt x y z mode).value = fma x y z (mode := mode) := by
  obtain ⟨dx, hdx, hsx, -⟩ := KernelPath.toDyadic?_of_isFinite x hx
  obtain ⟨dy, hdy, hsy, -⟩ := KernelPath.toDyadic?_of_isFinite y hy
  obtain ⟨dz, hdz, hsz, -⟩ := KernelPath.toDyadic?_of_isFinite z hz
  rw [formatOfFusedMultiplyAdd_of_toDyadic?_eq_some hdx hdy hdz mode, Factor.deliver_finite_value,
    KernelPath.fma_of_finite mode x y z dx dy dz hdx hdy hdz]
  unfold KernelPath.roundedSum zeroForExactSum
  rw [hsx, hsy, hsz]
  simp

/--
In one format and for finite operands, `formatOfDivision` delivers `Model.div`, in every
rounding direction: the rounded quotient, the signed zero of a zero dividend, the infinity of a
division by zero and the default NaN of zero divided by zero.
-/
theorem formatOfDivision_value_eq_div (x y : Model fmt) (mode : IEEERoundingMode)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    (formatOfDivision fmt x y mode).value = div x y (mode := mode) := by
  obtain ⟨dx, hdx, hsx, -⟩ := KernelPath.toDyadic?_of_isFinite x hx
  obtain ⟨dy, hdy, hsy, -⟩ := KernelPath.toDyadic?_of_isFinite y hy
  rw [KernelPath.div_of_finite mode x y dx dy hdx hdy]
  by_cases hy0 : dy.significand = 0
  · by_cases hx0 : dx.significand = 0 <;>
      simp [formatOfDivision, Factor.ofValue_of_toDyadic?_eq_some hdx,
        Factor.ofValue_of_toDyadic?_eq_some hdy, hx0, hy0, hsx, hsy, outcomeWithInvalid]
  · by_cases hx0 : dx.significand = 0
    · simp [formatOfDivision, Factor.ofValue_of_toDyadic?_eq_some hdx,
        Factor.ofValue_of_toDyadic?_eq_some hdy, hx0, hy0, hsx, hsy]
    · rw [formatOfDivision_value_of_toDyadic?_eq_some hdx hdy hx0 hy0 mode, ite_eq_right hy0,
        ite_eq_right hx0, hsx, hsy]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
