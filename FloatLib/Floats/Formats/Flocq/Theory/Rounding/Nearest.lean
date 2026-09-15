/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Core

/-!
# Nearest Rounding with a Tie Choice

`nearestChoice chooseUp` rounds to a nearest integer. At an exact midpoint, `chooseUp f`
decides whether the lower integer `f` or the upper integer `f + 1` is selected. This is the native
Lean counterpart of Flocq's `Znearest choice`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

/-- Round to a nearest integer, resolving a midpoint according to its lower integer. -/
noncomputable def nearestChoice (chooseUp : ℤ → Bool) (x : ℝ) : ℤ :=
  let f := ⌊x⌋
  if Int.fract x < 1 / 2 then f
  else if Int.fract x > 1 / 2 then f + 1
  else if chooseUp f then f + 1 else f

/-- Choice-based nearest rounding always selects floor or ceiling. -/
theorem nearestChoice_eq_floor_or_ceil (chooseUp : ℤ → Bool) (x : ℝ) :
    nearestChoice chooseUp x = ⌊x⌋ ∨ nearestChoice chooseUp x = ⌈x⌉ := by
  by_cases hxInt : x ∈ Set.range ((↑·) : ℤ → ℝ)
  · obtain ⟨n, rfl⟩ := hxInt
    simp [nearestChoice]
  · have hceil : ⌈x⌉ = ⌊x⌋ + 1 := (Int.ceil_eq_floor_add_one_iff_notMem x).2 hxInt
    rw [hceil]
    simp only [nearestChoice]
    split_ifs <;> simp

/-- Choice-based nearest rounding lies between floor and floor plus one. -/
theorem nearestChoice_bounds (chooseUp : ℤ → Bool) (x : ℝ) :
    ⌊x⌋ ≤ nearestChoice chooseUp x ∧ nearestChoice chooseUp x ≤ ⌊x⌋ + 1 := by
  simp only [nearestChoice]
  split_ifs <;> constructor <;> linarith

/-- Choice-based nearest rounding fixes integers. -/
@[simp] theorem nearestChoice_intCast (chooseUp : ℤ → Bool) (n : ℤ) :
    nearestChoice chooseUp (n : ℝ) = n := by
  simp [nearestChoice]

/-- Every tie choice has absolute error at most one half. -/
theorem nearestChoice_abs_sub_le_half (chooseUp : ℤ → Bool) (x : ℝ) :
    abs ((nearestChoice chooseUp x : ℝ) - x) ≤ (1 / 2 : ℝ) := by
  unfold nearestChoice
  dsimp only
  split_ifs with hlt hgt hchoice
  · have hdiff : (⌊x⌋ : ℝ) - x = -Int.fract x := by
      rw [Int.fract]
      ring
    rw [hdiff, abs_neg, abs_of_nonneg (Int.fract_nonneg x)]
    exact hlt.le
  · have hdiff : (⌊x⌋ : ℝ) + 1 - x = 1 - Int.fract x := by
      rw [Int.fract]
      ring
    norm_num only [Int.cast_add, Int.cast_one]
    rw [hdiff, abs_of_nonneg (by linarith [Int.fract_lt_one x])]
    linarith
  · have heq : Int.fract x = 1 / 2 := by linarith
    have hdiff : (⌊x⌋ : ℝ) + 1 - x = 1 - Int.fract x := by
      rw [Int.fract]
      ring
    norm_num only [Int.cast_add, Int.cast_one]
    rw [hdiff, heq]
    norm_num
  · have heq : Int.fract x = 1 / 2 := by linarith
    have hdiff : (⌊x⌋ : ℝ) - x = -Int.fract x := by
      rw [Int.fract]
      ring
    rw [hdiff, heq]
    norm_num

/-- Choice-based nearest rounding is monotone. -/
theorem nearestChoice_mono (chooseUp : ℤ → Bool) {x y : ℝ} (hxy : x ≤ y) :
    nearestChoice chooseUp x ≤ nearestChoice chooseUp y := by
  let rx := nearestChoice chooseUp x
  let ry := nearestChoice chooseUp y
  by_contra hnot
  have hryx : ry < rx := lt_of_not_ge hnot
  have hstep : ry + 1 ≤ rx := Int.add_one_le_iff.mpr hryx
  have hstepR : (ry : ℝ) + 1 ≤ (rx : ℝ) := by exact_mod_cast hstep
  have hxerr := abs_le.mp (nearestChoice_abs_sub_le_half chooseUp x)
  have hyerr := abs_le.mp (nearestChoice_abs_sub_le_half chooseUp y)
  have hxeq : x = y := by linarith
  subst y
  exact (lt_irrefl rx) hryx

/-- Every tie-choice nearest mode is a valid nearest rounding mode. -/
instance nearestChoiceValid (chooseUp : ℤ → Bool) :
    ValidRndToNearest (nearestChoice chooseUp) where
  monotone := fun _ _ h => nearestChoice_mono chooseUp h
  id := nearestChoice_intCast chooseUp
  abs_sub_le_half := by
    intro x
    have hhalf : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
    rw [← hhalf]
    exact nearestChoice_abs_sub_le_half chooseUp x

end FloatLib.Floats.Formats.Flocq
