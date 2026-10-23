/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Bounds

/-!
# Non-NaN results for conventional IEEE directed arithmetic

Directed dyadic rounding may produce a finite value or an infinity, but never a NaN. So directed
addition, subtraction, multiplication, and nonzero-denominator division preserve the
non-NaN classification when both operands are finite. These facts are shared by the IEEE interval
soundness proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Directed-down addition is non-NaN on finite operands. -/
theorem isNaN_add_down_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (add x y (mode := .down)) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [add_eq_of_toDyadic?_some .down nofun hdx hdy]
  split_ifs
  · exact isNaN_zeroForExactSum_eq_false fmt _ _ _
  · exact isNaN_roundDyadicDown_eq_false fmt _ hfmt

/-- Directed-up addition is non-NaN on finite operands. -/
theorem isNaN_add_up_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (add x y (mode := .up)) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [add_eq_of_toDyadic?_some .up nofun hdx hdy]
  split_ifs
  · exact isNaN_zeroForExactSum_eq_false fmt _ _ _
  · exact isNaN_roundDyadicUp_eq_false fmt _ hfmt

/-- Directed-down multiplication is non-NaN on finite operands. -/
theorem isNaN_mul_down_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (mul x y (mode := .down)) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [mul_eq_of_toDyadic?_some .down nofun hdx hdy]
  exact isNaN_roundDyadicDown_eq_false fmt _ hfmt

/-- Directed-up multiplication is non-NaN on finite operands. -/
theorem isNaN_mul_up_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (mul x y (mode := .up)) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [mul_eq_of_toDyadic?_some .up nofun hdx hdy]
  exact isNaN_roundDyadicUp_eq_false fmt _ hfmt

/-- Directed-down division is non-NaN on finite operands with a nonzero divisor. -/
theorem isNaN_div_down_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false) :
    isNaN (div x y (mode := .down)) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [div_eq_of_toDyadic?_some .down nofun hdx hdy hy0]
  exact isNaN_roundRatDownScaled_eq_false fmt _ _ _ _ hfmt
    (significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdy hy0)

/-- Directed-up division is non-NaN on finite operands with a nonzero divisor. -/
theorem isNaN_div_up_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false) :
    isNaN (div x y (mode := .up)) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [div_eq_of_toDyadic?_some .up nofun hdx hdy hy0]
  exact isNaN_roundRatUpScaled_eq_false fmt _ _ _ _ hfmt
    (significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdy hy0)

/-- Directed-down subtraction is non-NaN on finite operands. -/
theorem isNaN_sub_down_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (sub x y (mode := .down)) = false := by
  have hyNeg : isFinite (neg y) = true := by
    simpa using hy
  change isNaN (add x (neg y) (mode := .down)) = false
  exact isNaN_add_down_eq_false_of_isFinite x (neg y) hfmt hx hyNeg

/-- Directed-up subtraction is non-NaN on finite operands. -/
theorem isNaN_sub_up_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (sub x y (mode := .up)) = false := by
  have hyNeg : isFinite (neg y) = true := by
    simpa using hy
  change isNaN (add x (neg y) (mode := .up)) = false
  exact isNaN_add_up_eq_false_of_isFinite x (neg y) hfmt hx hyNeg

end Model
end FloatLib.Floats.Formats.BinaryInterchange
