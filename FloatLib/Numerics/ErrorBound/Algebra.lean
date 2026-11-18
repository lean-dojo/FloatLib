/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Algebraic propagation of absolute errors

Addition, subtraction and multiplication propagate absolute bounds over any linearly ordered
commutative ring. The complex fixed-point enclosure proofs use these same bounds on each
coordinate; the backward-error layer specializes them to real numbers.
-/

@[expose] public section

namespace FloatLib.Numerics

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Numerical interpretation and propagation of input errors are independent proof steps. -/
theorem compose_error {actual intermediate reference localError inputError : K}
    (hlocal : |actual - intermediate| ≤ localError)
    (hinput : |intermediate - reference| ≤ inputError) :
    |actual - reference| ≤ inputError + localError :=
  ((abs_sub_le actual intermediate reference).trans (add_le_add hlocal hinput)).trans_eq
    (add_comm localError inputError)

namespace Backward

variable {x R A y S B : K}

/-- A sum is at most the sum of bounds of its terms. -/
theorem abs_add_le_add {x y A B : K} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x + y| ≤ A + B :=
  (abs_add_le _ _).trans (add_le_add hx hy)

/-- A difference is at most the sum of bounds of its terms. -/
theorem abs_sub_le_add {x y A B : K} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x - y| ≤ A + B :=
  (abs_sub _ _).trans (add_le_add hx hy)

/-- A product is at most the product of bounds of its factors. -/
theorem abs_mul_le_mul {x y A B : K} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x * y| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg y) ((abs_nonneg x).trans hx)

/-- A sum of two values within `A` and `B` of their references is within `A + B` of the sum of
the references. -/
theorem add (hx : |x - R| ≤ A) (hy : |y - S| ≤ B) :
    |x + y - (R + S)| ≤ A + B := by
  rw [add_sub_add_comm]
  exact abs_add_le_add hx hy

/-- A difference of two values within `A` and `B` of their references is within `A + B` of the
difference of the references. -/
theorem sub (hx : |x - R| ≤ A) (hy : |y - S| ≤ B) :
    |x - y - (R - S)| ≤ A + B := by
  rw [sub_sub_sub_comm]
  exact abs_sub_le_add hx hy

/-- One computed factor and one reference suffice for a product perturbation bound. -/
theorem deviation_mul_mixed (hx : |x - R| ≤ A) (hy : |y - S| ≤ B) :
    |x * y - R * S| ≤ |y| * A + |R| * B := by
  have hsplit : x * y - R * S = (x - R) * y + R * (y - S) := by
    rw [sub_mul, mul_sub, sub_add_sub_cancel]
  rw [hsplit]
  exact abs_add_le_add
    (by simpa only [mul_comm] using abs_mul_le_mul hx (le_refl |y|))
    (abs_mul_le_mul (le_refl |R|) hy)

/-- A product of two values within `A` and `B` of their references `R` and `S` is within
`A * (|S| + B) + |R| * B` of `R * S`. The bound reads the references, not the values. -/
theorem deviation_mul (hx : |x - R| ≤ A) (hy : |y - S| ≤ B) :
    |x * y - R * S| ≤ A * (|S| + B) + |R| * B := by
  have hA := (abs_nonneg _).trans hx
  have hyS : |y| ≤ |S| + B := by
    simpa only [sub_zero] using compose_error hy (le_refl |S - 0|)
  calc |x * y - R * S| ≤ |y| * A + |R| * B := deviation_mul_mixed hx hy
    _ ≤ (|S| + B) * A + |R| * B :=
      add_le_add (mul_le_mul_of_nonneg_right hyS hA) le_rfl
    _ = A * (|S| + B) + |R| * B := by rw [mul_comm (|S| + B)]

end Backward

/-- Compose input perturbations with the error of the operation actually executed. -/
theorem add_error {a b x y r ea eb er : K}
    (ha : |a - x| ≤ ea) (hb : |b - y| ≤ eb) (hr : |r - (a + b)| ≤ er) :
    |r - (x + y)| ≤ ea + eb + er :=
  compose_error hr (Backward.add ha hb)

/-- Subtraction retains both input errors even when its exact result is very small. -/
theorem sub_error {a b x y r ea eb er : K}
    (ha : |a - x| ≤ ea) (hb : |b - y| ≤ eb) (hr : |r - (a - b)| ≤ er) :
    |r - (x - y)| ≤ ea + eb + er :=
  compose_error hr (Backward.sub ha hb)

/-- An asymmetric product bound retains the computed second factor and the exact first
reference, including their higher-order input error. -/
theorem mul_error {a b x y r ea eb er : K}
    (ha : |a - x| ≤ ea) (hb : |b - y| ≤ eb) (hr : |r - a * b| ≤ er) :
    |r - x * y| ≤ |b| * ea + |x| * eb + er :=
  compose_error hr (Backward.deviation_mul_mixed ha hb)

end FloatLib.Numerics
