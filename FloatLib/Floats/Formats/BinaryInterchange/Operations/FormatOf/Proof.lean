/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.ScaledProduct.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.DivisionSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rounded

/-!
# Semantics of the formatOf operations

IEEE 754-2019 §5.4.1 asks that a formatOf operation compute "as if" with unbounded range and
precision and round once into the destination. For finite operands of any formats this module
proves:

* in every rounding direction the delivered value is the zero of the direction's sign rule
  when the exact result is zero, and otherwise the direction's rounding kernel
  `Internal.Directed.roundDyadic` (for division `roundRatScaled`) applied to the exact result
  (`formatOfAddition_of_toDyadic?_eq_some` and its siblings): the rounding step of the
  operations of one format, applied in the destination;
* to nearest-even, with a conventional IEEE destination and a finite result, the delivered
  value denotes `roundAt destination` of the exact real sum, difference, product, quotient or
  `x * y + z` (`toReal_formatOfAddition`, `toReal_formatOfSubtraction`,
  `toReal_formatOfMultiplication`, `toReal_formatOfDivision`,
  `toReal_formatOfFusedMultiplyAdd`);
* in every rounding direction, with a conventional IEEE destination and an exact sum,
  difference, product or `x * y + z` within the largest finite magnitude of the destination,
  the result is finite and denotes `roundAt destination` of that exact value in the direction
  (`formatOfAddition_finite_roundAt`, `formatOfSubtraction_finite_roundAt`,
  `formatOfMultiplication_finite_roundAt`, `formatOfFusedMultiplyAdd_finite_roundAt`).

The hypotheses on the range exclude overflow. No statement is made here about the quotient in
the directed directions as a real number, nor about the flags. When the three formats coincide
the operations are `add`, `sub`, `mul`, `div` and `fma` with their flags, for every operand:
`Operations.FormatOf.Homogeneous` proves it.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open Reduction.Internal (Factor)

variable {destination left right addend : FloatFormat}

namespace Reduction.Internal

/--
The value delivered for a finite exact result: the zero of sign `zeroNegative` when it is
zero, and one rounding in `mode` otherwise.
-/
theorem Factor.deliver_finite_value (exact : Numerics.Dyadic) (mode : IEEERoundingMode)
    (zeroNegative : Bool) :
    ((Factor.finite exact : Factor destination).deliver mode zeroNegative).value =
      if exact.significand = 0 then zero destination zeroNegative
      else Internal.Directed.roundDyadic destination mode exact := by
  by_cases hzero : exact.significand = 0 <;> simp [Factor.deliver, hzero]

/--
To nearest-even and under a conventional IEEE descriptor, a finite value delivered for a finite
exact result denotes the rounded exact result.
-/
theorem Factor.toReal_deliver_finite (hfmt : destination.isIEEE = true)
    (exact : Numerics.Dyadic) (zeroNegative : Bool)
    (hfin : isFinite
      ((Factor.finite exact : Factor destination).deliver .nearest zeroNegative).value = true) :
    toReal ((Factor.finite exact : Factor destination).deliver .nearest zeroNegative).value =
      roundAt destination exact.toReal := by
  rw [Factor.deliver_finite_value] at hfin ⊢
  by_cases hzero : exact.significand = 0
  · simp [hzero, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]
  · simp only [hzero, ite_false] at hfin ⊢
    exact toReal_roundDyadic_eq_roundAt destination hfmt exact hfin

/--
For a conventional IEEE destination and every rounding direction, a finite exact result within
the largest finite magnitude is delivered as a finite value that denotes its rounding on the
grid of the destination in that direction.
-/
theorem Factor.deliver_finite_roundAt (hfmt : destination.isIEEE = true)
    (mode : IEEERoundingMode) (exact : Numerics.Dyadic) (zeroNegative : Bool)
    (hbound : |exact.toReal| ≤ toReal (posMaxFinite destination)) :
    isFinite ((Factor.finite exact : Factor destination).deliver mode zeroNegative).value =
        true ∧
      toReal ((Factor.finite exact : Factor destination).deliver mode zeroNegative).value =
        roundAt destination exact.toReal mode := by
  rw [Factor.deliver_finite_value]
  by_cases hzero : exact.significand = 0
  · have hreal : exact.toReal = 0 := (Dyadic.toReal_eq_zero_iff exact).mpr hzero
    rw [ite_eq_left hzero, hreal, roundAt_zero destination mode, toReal_zero]
    exact ⟨isFinite_eq_true_of_isZero_eq_true _ (isZero_zero destination zeroNegative), rfl⟩
  · rw [ite_eq_right hzero]
    exact Internal.Directed.roundDyadic_finite_roundAt destination hfmt mode exact hbound

end Reduction.Internal

/-! ## Finite operands in every direction -/

/--
For finite operands of any formats, `formatOfAddition` delivers the exact dyadic sum: the
outcome of `Factor.deliver` on it, with the sign rule of the direction for an exact zero.
-/
theorem formatOfAddition_of_toDyadic?_eq_some {x : Model left} {y : Model right}
    {dx dy : Numerics.Dyadic} (hdx : toDyadic? x = some dx) (hdy : toDyadic? y = some dy)
    (mode : IEEERoundingMode := .nearest) :
    formatOfAddition destination x y mode =
      (Factor.finite (addDyadic dx dy) : Factor destination).deliver mode
        (mode.zeroSumSign (signBit x) (signBit y)) := by
  simp [formatOfAddition, Factor.ofValue_of_toDyadic?_eq_some hdx,
    Factor.ofValue_of_toDyadic?_eq_some hdy, Factor.add]

/--
For finite operands of any formats, `formatOfMultiplication` delivers the exact dyadic product,
a zero product with the product of the signs.
-/
theorem formatOfMultiplication_of_toDyadic?_eq_some {x : Model left} {y : Model right}
    {dx dy : Numerics.Dyadic} (hdx : toDyadic? x = some dx) (hdy : toDyadic? y = some dy)
    (mode : IEEERoundingMode := .nearest) :
    formatOfMultiplication destination x y mode =
      (Factor.finite
          { negative := Bool.xor dx.negative dy.negative
            significand := dx.significand * dy.significand
            exponent := dx.exponent + dy.exponent } : Factor destination).deliver mode
        (Bool.xor (signBit x) (signBit y)) := by
  simp [formatOfMultiplication, Factor.ofValue_of_toDyadic?_eq_some hdx,
    Factor.ofValue_of_toDyadic?_eq_some hdy, Factor.mul]

/--
For finite operands of any formats, `formatOfFusedMultiplyAdd` delivers the exact dyadic
`x * y + z`, with the sign rule of the direction for an exact zero.
-/
theorem formatOfFusedMultiplyAdd_of_toDyadic?_eq_some {x : Model left} {y : Model right}
    {z : Model addend} {dx dy dz : Numerics.Dyadic} (hdx : toDyadic? x = some dx)
    (hdy : toDyadic? y = some dy) (hdz : toDyadic? z = some dz)
    (mode : IEEERoundingMode := .nearest) :
    formatOfFusedMultiplyAdd destination x y z mode =
      (Factor.finite
          (addDyadic
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent } dz) : Factor destination).deliver mode
        (mode.zeroSumSign (Bool.xor (signBit x) (signBit y)) (signBit z)) := by
  simp [formatOfFusedMultiplyAdd, Factor.ofValue_of_toDyadic?_eq_some hdx,
    Factor.ofValue_of_toDyadic?_eq_some hdy, Factor.ofValue_of_toDyadic?_eq_some hdz,
    Factor.mul, Factor.add]

/--
For a finite nonzero dividend and a finite nonzero divisor of any formats, `formatOfDivision`
delivers one rounding of the exact scaled rational quotient in `mode`.
-/
theorem formatOfDivision_value_of_toDyadic?_eq_some {x : Model left} {y : Model right}
    {dx dy : Numerics.Dyadic} (hdx : toDyadic? x = some dx) (hdy : toDyadic? y = some dy)
    (hx : dx.significand ≠ 0) (hy : dy.significand ≠ 0) (mode : IEEERoundingMode := .nearest) :
    (formatOfDivision destination x y mode).value =
      Internal.Directed.roundRatScaled destination mode (Bool.xor (signBit x) (signBit y))
        dx.significand dy.significand (dx.exponent - dy.exponent) := by
  simp [formatOfDivision, Factor.ofValue_of_toDyadic?_eq_some hdx,
    Factor.ofValue_of_toDyadic?_eq_some hdy, hx, hy]

/-! ## One rounding of the exact real result -/

/--
**formatOf addition rounds the exact sum once.** For finite operands of any two formats and a
conventional IEEE destination, a finite result of `formatOfAddition` to nearest-even denotes
`roundAt destination (toReal x + toReal y)`.
-/
theorem toReal_formatOfAddition (hfmt : destination.isIEEE = true) (x : Model left)
    (y : Model right) (hx : isFinite x = true) (hy : isFinite y = true)
    (hfin : isFinite (formatOfAddition destination x y).value = true) :
    toReal (formatOfAddition destination x y).value =
      roundAt destination (toReal x + toReal y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [formatOfAddition_of_toDyadic?_eq_some hdx hdy] at hfin ⊢
  rw [Factor.toReal_deliver_finite hfmt _ _ hfin, Dyadic.toReal_addDyadic]
  simp [toReal_eq, hdx, hdy]

/--
**formatOf subtraction rounds the exact difference once.** For finite operands of any two
formats and a conventional IEEE destination, a finite result of `formatOfSubtraction` to
nearest-even denotes `roundAt destination (toReal x - toReal y)`.
-/
theorem toReal_formatOfSubtraction (hfmt : destination.isIEEE = true) (x : Model left)
    (y : Model right) (hx : isFinite x = true) (hy : isFinite y = true)
    (hfin : isFinite (formatOfSubtraction destination x y).value = true) :
    toReal (formatOfSubtraction destination x y).value =
      roundAt destination (toReal x - toReal y) := by
  have h := toReal_formatOfAddition hfmt x (neg y) hx (by simpa using hy) hfin
  rwa [toReal_neg y hy, ← sub_eq_add_neg] at h

/--
**formatOf multiplication rounds the exact product once.** For finite operands of any two
formats and a conventional IEEE destination, a finite result of `formatOfMultiplication` to
nearest-even denotes `roundAt destination (toReal x * toReal y)`.
-/
theorem toReal_formatOfMultiplication (hfmt : destination.isIEEE = true) (x : Model left)
    (y : Model right) (hx : isFinite x = true) (hy : isFinite y = true)
    (hfin : isFinite (formatOfMultiplication destination x y).value = true) :
    toReal (formatOfMultiplication destination x y).value =
      roundAt destination (toReal x * toReal y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [formatOfMultiplication_of_toDyadic?_eq_some hdx hdy] at hfin ⊢
  rw [Factor.toReal_deliver_finite hfmt _ _ hfin, Dyadic.toReal_mul]
  simp [toReal_eq, hdx, hdy]

/--
**formatOf fused multiply-add rounds the exact `x * y + z` once.** For finite operands of any
three formats and a conventional IEEE destination, a finite result of
`formatOfFusedMultiplyAdd` to nearest-even denotes
`roundAt destination (toReal x * toReal y + toReal z)`.
-/
theorem toReal_formatOfFusedMultiplyAdd (hfmt : destination.isIEEE = true) (x : Model left)
    (y : Model right) (z : Model addend) (hx : isFinite x = true) (hy : isFinite y = true)
    (hz : isFinite z = true)
    (hfin : isFinite (formatOfFusedMultiplyAdd destination x y z).value = true) :
    toReal (formatOfFusedMultiplyAdd destination x y z).value =
      roundAt destination (toReal x * toReal y + toReal z) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  obtain ⟨dz, hdz⟩ := exists_toDyadic?_of_isFinite hz
  rw [formatOfFusedMultiplyAdd_of_toDyadic?_eq_some hdx hdy hdz] at hfin ⊢
  rw [Factor.toReal_deliver_finite hfmt _ _ hfin, Dyadic.toReal_addDyadic, Dyadic.toReal_mul]
  simp [toReal_eq, hdx, hdy, hdz]

/--
**formatOf division rounds the exact quotient once.** For a finite dividend and a finite
nonzero divisor of any two formats and a conventional IEEE destination, a finite result of
`formatOfDivision` to nearest-even denotes `roundAt destination (toReal x / toReal y)`.
-/
theorem toReal_formatOfDivision (hfmt : destination.isIEEE = true) (x : Model left)
    (y : Model right) (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false)
    (hfin : isFinite (formatOfDivision destination x y).value = true) :
    toReal (formatOfDivision destination x y).value =
      roundAt destination (toReal x / toReal y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  have hnx := sign_eq_signBit_of_toDyadic?_some hdx
  have hny := sign_eq_signBit_of_toDyadic?_some hdy
  have hdyMant := significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdy hy0
  by_cases hdxMant : dx.significand = 0
  · have hxReal : toReal x = 0 := by
      simp [toReal_eq, hdx, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hdxMant]
    simp [formatOfDivision, Factor.ofValue_of_toDyadic?_eq_some hdx,
      Factor.ofValue_of_toDyadic?_eq_some hdy, hdxMant, hdyMant, hxReal]
  · rw [formatOfDivision_value_of_toDyadic?_eq_some hdx hdy hdxMant hdyMant] at hfin ⊢
    rw [← hnx, ← hny] at hfin ⊢
    change isFinite (roundRatScaled destination _ _ _ _) = true at hfin
    change toReal (roundRatScaled destination _ _ _ _) = _
    rw [toReal_roundRatScaled_eq_roundAt destination _ _ _ _ hfmt hfin,
      signedScaledRatToReal_eq_div_toReal dx dy]
    simp [toReal_eq, hdx, hdy]

/-! ## One rounding in every direction -/

/--
**formatOf addition is one rounding in every direction.** For finite operands of any two
formats, a conventional IEEE destination and each rounding direction `mode`, an exact sum
within the largest finite magnitude of the destination gives a finite result that denotes
`roundAt destination (toReal x + toReal y) mode`.
-/
theorem formatOfAddition_finite_roundAt (hfmt : destination.isIEEE = true)
    (mode : IEEERoundingMode) (x : Model left) (y : Model right) (hx : isFinite x = true)
    (hy : isFinite y = true)
    (hbound : |toReal x + toReal y| ≤ toReal (posMaxFinite destination)) :
    isFinite (formatOfAddition destination x y mode).value = true ∧
      toReal (formatOfAddition destination x y mode).value =
        roundAt destination (toReal x + toReal y) mode := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  have hexact : (addDyadic dx dy).toReal = toReal x + toReal y := by
    rw [Dyadic.toReal_addDyadic]
    simp [toReal_eq, hdx, hdy]
  rw [formatOfAddition_of_toDyadic?_eq_some hdx hdy mode, ← hexact]
  exact Factor.deliver_finite_roundAt hfmt mode _ _ (hexact ▸ hbound)

/--
**formatOf subtraction is one rounding in every direction.** For finite operands of any two
formats, a conventional IEEE destination and each rounding direction `mode`, an exact
difference within the largest finite magnitude of the destination gives a finite result that
denotes `roundAt destination (toReal x - toReal y) mode`.
-/
theorem formatOfSubtraction_finite_roundAt (hfmt : destination.isIEEE = true)
    (mode : IEEERoundingMode) (x : Model left) (y : Model right) (hx : isFinite x = true)
    (hy : isFinite y = true)
    (hbound : |toReal x - toReal y| ≤ toReal (posMaxFinite destination)) :
    isFinite (formatOfSubtraction destination x y mode).value = true ∧
      toReal (formatOfSubtraction destination x y mode).value =
        roundAt destination (toReal x - toReal y) mode := by
  have h := formatOfAddition_finite_roundAt hfmt mode x (neg y) hx (by simpa using hy)
    (by rwa [toReal_neg y hy, ← sub_eq_add_neg])
  rwa [toReal_neg y hy, ← sub_eq_add_neg] at h

/--
**formatOf multiplication is one rounding in every direction.** For finite operands of any two
formats, a conventional IEEE destination and each rounding direction `mode`, an exact product
within the largest finite magnitude of the destination gives a finite result that denotes
`roundAt destination (toReal x * toReal y) mode`.
-/
theorem formatOfMultiplication_finite_roundAt (hfmt : destination.isIEEE = true)
    (mode : IEEERoundingMode) (x : Model left) (y : Model right) (hx : isFinite x = true)
    (hy : isFinite y = true)
    (hbound : |toReal x * toReal y| ≤ toReal (posMaxFinite destination)) :
    isFinite (formatOfMultiplication destination x y mode).value = true ∧
      toReal (formatOfMultiplication destination x y mode).value =
        roundAt destination (toReal x * toReal y) mode := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  have hexact : (Numerics.Dyadic.mk (Bool.xor dx.negative dy.negative)
      (dx.significand * dy.significand) (dx.exponent + dy.exponent)).toReal =
      toReal x * toReal y := by
    rw [Dyadic.toReal_mul]
    simp [toReal_eq, hdx, hdy]
  rw [formatOfMultiplication_of_toDyadic?_eq_some hdx hdy mode, ← hexact]
  exact Factor.deliver_finite_roundAt hfmt mode _ _ (hexact ▸ hbound)

/--
**formatOf fused multiply-add is one rounding in every direction.** For finite operands of any
three formats, a conventional IEEE destination and each rounding direction `mode`, an exact
`x * y + z` within the largest finite magnitude of the destination gives a finite result that
denotes `roundAt destination (toReal x * toReal y + toReal z) mode`.
-/
theorem formatOfFusedMultiplyAdd_finite_roundAt (hfmt : destination.isIEEE = true)
    (mode : IEEERoundingMode) (x : Model left) (y : Model right) (z : Model addend)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hbound : |toReal x * toReal y + toReal z| ≤ toReal (posMaxFinite destination)) :
    isFinite (formatOfFusedMultiplyAdd destination x y z mode).value = true ∧
      toReal (formatOfFusedMultiplyAdd destination x y z mode).value =
        roundAt destination (toReal x * toReal y + toReal z) mode := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  obtain ⟨dz, hdz⟩ := exists_toDyadic?_of_isFinite hz
  have hexact : (addDyadic (Numerics.Dyadic.mk (Bool.xor dx.negative dy.negative)
      (dx.significand * dy.significand) (dx.exponent + dy.exponent)) dz).toReal =
      toReal x * toReal y + toReal z := by
    rw [Dyadic.toReal_addDyadic, Dyadic.toReal_mul]
    simp [toReal_eq, hdx, hdy, hdz]
  rw [formatOfFusedMultiplyAdd_of_toDyadic?_eq_some hdx hdy hdz mode, ← hexact]
  exact Factor.deliver_finite_roundAt hfmt mode _ _ (hexact ▸ hbound)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
