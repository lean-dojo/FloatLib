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

Directed dyadic rounding may produce a finite value or an infinity, but never a NaN. Consequently,
directed addition, subtraction, multiplication, and nonzero-denominator division preserve the
non-NaN classification when both operands are finite. These facts are shared by the IEEE interval
soundness proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Directed-down addition is non-NaN on finite operands. -/
theorem isNaN_addDown_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (addDown x y) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [addDown, addWithRounding_eq_of_toDyadic?_some .towardNegativeInfinity nofun hdx hdy]
  split_ifs
  · exact isNaN_zeroForExactSum_eq_false fmt _ _ _
  · exact isNaN_roundDyadicDown_eq_false fmt _ hfmt

/-- Directed-up addition is non-NaN on finite operands. -/
theorem isNaN_addUp_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (addUp x y) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [addUp, addWithRounding_eq_of_toDyadic?_some .towardPositiveInfinity nofun hdx hdy]
  split_ifs
  · exact isNaN_zeroForExactSum_eq_false fmt _ _ _
  · exact isNaN_roundDyadicUp_eq_false fmt _ hfmt

/-- Directed-down multiplication is non-NaN on finite operands. -/
theorem isNaN_mulDown_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (mulDown x y) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [mulDown, mulWithRounding_eq_of_toDyadic?_some .towardNegativeInfinity nofun hdx hdy]
  exact isNaN_roundDyadicDown_eq_false fmt _ hfmt

/-- Directed-up multiplication is non-NaN on finite operands. -/
theorem isNaN_mulUp_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (mulUp x y) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [mulUp, mulWithRounding_eq_of_toDyadic?_some .towardPositiveInfinity nofun hdx hdy]
  exact isNaN_roundDyadicUp_eq_false fmt _ hfmt

/-- Directed-down division is non-NaN on finite operands with a nonzero divisor. -/
theorem isNaN_divDown_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false) :
    isNaN (divDown x y) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [divDown, divWithRounding_eq_of_toDyadic?_some .towardNegativeInfinity nofun hdx hdy hy0]
  exact isNaN_roundRatDownScaled_eq_false fmt _ _ _ _ hfmt
    (significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdy hy0)

/-- Directed-up division is non-NaN on finite operands with a nonzero divisor. -/
theorem isNaN_divUp_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false) :
    isNaN (divUp x y) = false := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [divUp, divWithRounding_eq_of_toDyadic?_some .towardPositiveInfinity nofun hdx hdy hy0]
  exact isNaN_roundRatUpScaled_eq_false fmt _ _ _ _ hfmt
    (significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdy hy0)

/-- Directed-down subtraction is non-NaN on finite operands. -/
theorem isNaN_subDown_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (subDown x y) = false := by
  have hyNeg : isFinite (neg y) = true := by
    simpa using hy
  change isNaN (addDown x (neg y)) = false
  exact isNaN_addDown_eq_false_of_isFinite x (neg y) hfmt hx hyNeg

/-- Directed-up subtraction is non-NaN on finite operands. -/
theorem isNaN_subUp_eq_false_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    isNaN (subUp x y) = false := by
  have hyNeg : isFinite (neg y) = true := by
    simpa using hy
  change isNaN (addUp x (neg y)) = false
  exact isNaN_addUp_eq_false_of_isFinite x (neg y) hfmt hx hyNeg

end Model
end FloatLib.Floats.Formats.BinaryInterchange
