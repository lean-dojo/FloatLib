/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Basic
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Ordered-field interval corner bounds

Multiplication and division away from zero are enclosed by their four endpoint calculations.
The proofs apply to any ordered field, independently of endpoint representation or rounding.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

variable {β : Type*} [Field β] [LinearOrder β] [IsStrictOrderedRing β]

/-- Minimum of four ordered values, grouped as `min (min a b) (min c d)`. -/
abbrev minOfFour {α : Type*} [LinearOrder α] (a b c d : α) : α :=
  min (min a b) (min c d)

/-- Maximum of four ordered values, grouped as `max (max a b) (max c d)`. -/
abbrev maxOfFour {α : Type*} [LinearOrder α] (a b c d : α) : α :=
  max (max a b) (max c d)

/-- A product with one factor in a closed interval is bounded below by the endpoint products. -/
private theorem min_mul_le_mul {p c d y : β} (hcy : c ≤ y) (hyd : y ≤ d) :
    min (p * c) (p * d) ≤ p * y := by
  rcases le_total 0 p with hp | hp
  · exact min_le_of_left_le (mul_le_mul_of_nonneg_left hcy hp)
  · exact min_le_of_right_le (mul_le_mul_of_nonpos_left hyd hp)

/-- A product with one factor in a closed interval is bounded above by the endpoint products. -/
private theorem mul_le_max_mul {p c d y : β} (hcy : c ≤ y) (hyd : y ≤ d) :
    p * y ≤ max (p * c) (p * d) := by
  rcases le_total 0 p with hp | hp
  · exact le_max_of_le_right (mul_le_mul_of_nonneg_left hyd hp)
  · exact le_max_of_le_left (mul_le_mul_of_nonpos_left hcy hp)

/--
Corner enclosure for multiplication on intervals.

If $x\in[a,b]$ and $y\in[c,d]$, then
$$
\min(ac,ad,bc,bd)\le xy\le\max(ac,ad,bc,bd),
$$

where the min/max are represented by `minOfFour`/`maxOfFour` with the same grouping used by
the executable interval four-corner rule.
-/
theorem mul_bounds_Icc (a b c d x y : β)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    x * y ∈ Set.Icc (minOfFour (a * c) (a * d) (b * c) (b * d))
      (maxOfFour (a * c) (a * d) (b * c) (b * d)) := by
  have hmin := min_mul_le_mul (p := y) hx.1 hx.2
  have hmax := mul_le_max_mul (p := y) hx.1 hx.2
  rw [mul_comm y a, mul_comm y b, mul_comm y x] at hmin hmax
  exact ⟨(min_le_min (min_mul_le_mul hy.1 hy.2) (min_mul_le_mul hy.1 hy.2)).trans hmin,
    hmax.trans (max_le_max (mul_le_max_mul hy.1 hy.2) (mul_le_max_mul hy.1 hy.2))⟩

private theorem inv_mem_Icc_of_mem_Icc_of_pos (c d y : β)
    (hc : 0 < c) (hy : y ∈ Set.Icc c d) :
    (1 / y) ∈ Set.Icc (1 / d) (1 / c) := by
  rcases hy with ⟨hcy, hyd⟩
  have hypos : 0 < y := lt_of_lt_of_le hc hcy
  exact ⟨one_div_le_one_div_of_le hypos hyd, one_div_le_one_div_of_le hc hcy⟩

private theorem inv_mem_Icc_of_mem_Icc_of_neg (c d y : β)
    (hd : d < 0) (hy : y ∈ Set.Icc c d) :
    (1 / y) ∈ Set.Icc (1 / d) (1 / c) := by
  rcases hy with ⟨hcy, hyd⟩
  have hyneg : y < 0 := lt_of_le_of_lt hyd hd
  exact
    ⟨one_div_le_one_div_of_neg_of_le hd hyd,
      one_div_le_one_div_of_neg_of_le hyneg hcy⟩

/--
Corner enclosure for division when the denominator interval lies strictly on one side of
zero.
-/
theorem div_bounds_Icc (a b c d x y : β)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d)
    (hzero : d < 0 ∨ 0 < c) :
    x / y ∈ Set.Icc (minOfFour (a / c) (a / d) (b / c) (b / d))
      (maxOfFour (a / c) (a / d) (b / c) (b / d)) := by
  have hinvOne : (1 / y) ∈ Set.Icc (1 / d) (1 / c) := by
    cases hzero with
    | inl hd => exact inv_mem_Icc_of_mem_Icc_of_neg c d y hd hy
    | inr hc => exact inv_mem_Icc_of_mem_Icc_of_pos c d y hc hy
  have hinv : y⁻¹ ∈ Set.Icc d⁻¹ c⁻¹ := by
    simpa [one_div] using hinvOne
  have hmul := mul_bounds_Icc a b d⁻¹ c⁻¹ x y⁻¹ hx hinv
  have hmin :
      minOfFour (a * d⁻¹) (a * c⁻¹) (b * d⁻¹) (b * c⁻¹) =
        minOfFour (a / c) (a / d) (b / c) (b / d) := by
    simp [minOfFour, div_eq_mul_inv, min_comm]
  have hmax :
      maxOfFour (a * d⁻¹) (a * c⁻¹) (b * d⁻¹) (b * c⁻¹) =
        maxOfFour (a / c) (a / d) (b / c) (b / d) := by
    simp [maxOfFour, div_eq_mul_inv, max_comm]
  refine ⟨?_, ?_⟩
  · simpa [div_eq_mul_inv, hmin] using hmul.1
  · simpa [div_eq_mul_inv, hmax] using hmul.2

end FloatLib.Numerics.Interval
