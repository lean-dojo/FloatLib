/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Rational.Runtime
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Soundness of rational interval operations

`Contains` interprets executable rational endpoints as a closed real interval. The arithmetic
lemmas propagate membership without imposing a floating-point format or rounding policy.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalInterval

/-- A real value lies between the rational endpoints. -/
def Contains (interval : RationalInterval) (x : ℝ) : Prop :=
  (interval.lo : ℝ) ≤ x ∧ x ≤ (interval.hi : ℝ)

/-- Every nonempty interval has ordered rational endpoints. -/
theorem lo_le_hi {interval : RationalInterval} {x : ℝ} (hx : interval.Contains x) :
    interval.lo ≤ interval.hi := by
  exact_mod_cast hx.1.trans hx.2

/-- A point interval contains its exact rational value. -/
theorem contains_point (x : ℚ) : (point x).Contains (x : ℝ) :=
  ⟨le_rfl, le_rfl⟩

/-- An absolute-error estimate gives membership in a midpoint-radius interval. -/
theorem contains_around {x : ℝ} {midpoint radius : ℚ}
    (herror : |x - (midpoint : ℝ)| ≤ (radius : ℝ)) :
    (around midpoint radius).Contains x := by
  rcases abs_le.mp herror with ⟨hlower, hupper⟩
  constructor <;> simp only [around, Rat.cast_sub, Rat.cast_add] <;> linarith

/-- Negating an enclosed real value reverses the endpoint inequalities. -/
theorem contains_neg {interval : RationalInterval} {x : ℝ} (hx : interval.Contains x) :
    interval.neg.Contains (-x) := by
  constructor
  · simpa [neg] using neg_le_neg hx.2
  · simpa [neg] using neg_le_neg hx.1

/-- Addition preserves enclosure. -/
theorem contains_add {left right : RationalInterval} {x y : ℝ}
    (hx : left.Contains x) (hy : right.Contains y) :
    (left.add right).Contains (x + y) := by
  constructor
  · simpa [add] using add_le_add hx.1 hy.1
  · simpa [add] using add_le_add hx.2 hy.2

/-- Subtraction preserves enclosure. -/
theorem contains_sub {left right : RationalInterval} {x y : ℝ}
    (hx : left.Contains x) (hy : right.Contains y) :
    (left.sub right).Contains (x - y) := by
  simpa [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

/-- A nonnegative rational scale preserves the endpoint inequalities. -/
theorem contains_scaleNonnegative {interval : RationalInterval} {x : ℝ}
    (hx : interval.Contains x) {factor : ℚ} (hfactor : 0 ≤ factor) :
    (interval.scaleNonnegative factor).Contains ((factor : ℝ) * x) := by
  have hreal : (0 : ℝ) ≤ factor := by exact_mod_cast hfactor
  constructor
  · simpa [scaleNonnegative] using mul_le_mul_of_nonneg_left hx.1 hreal
  · simpa [scaleNonnegative] using mul_le_mul_of_nonneg_left hx.2 hreal

/-- Signed rational scaling preserves enclosure with the appropriate endpoint order. -/
theorem contains_scale {interval : RationalInterval} {x : ℝ}
    (hx : interval.Contains x) (factor : ℚ) :
    (interval.scale factor).Contains ((factor : ℝ) * x) := by
  unfold scale
  split
  · exact contains_scaleNonnegative hx ‹0 ≤ factor›
  · simpa only [Rat.cast_neg, neg_mul, neg_neg] using
      contains_neg (contains_scaleNonnegative hx (factor := -factor) (by linarith))

/-- Squaring a nonnegative enclosed value preserves enclosure. -/
theorem contains_squareNonnegative {interval : RationalInterval} {x : ℝ}
    (hx : interval.Contains x) (hnonnegative : 0 ≤ x) :
    interval.squareNonnegative.Contains (x ^ 2) := by
  have hlower : max 0 (interval.lo : ℝ) ≤ x := max_le hnonnegative hx.1
  constructor
  · simp only [squareNonnegative, Rat.cast_pow, Rat.cast_max, Rat.cast_zero]
    exact pow_le_pow_left₀ (le_max_left _ _) hlower _
  · simp only [squareNonnegative, Rat.cast_pow]
    exact pow_le_pow_left₀ hnonnegative hx.2 _

/-- Repeated squaring encloses the corresponding power of a nonnegative real value. -/
theorem contains_squareRepeat {interval : RationalInterval} {x : ℝ}
    (hx : interval.Contains x) (hnonnegative : 0 ≤ x) (n : Nat) :
    (interval.squareRepeat n).Contains (x ^ (2 ^ n)) := by
  induction n with
  | zero => simpa [squareRepeat] using hx
  | succ n ih =>
      simpa [squareRepeat, pow_succ, pow_mul] using
        contains_squareNonnegative ih (pow_nonneg hnonnegative _)

end FloatLib.Numerics.RationalInterval
