/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring.RingNF

/-!
# Mixed relative and absolute error

`MixedError x x₀ r a` states that `x` approximates `x₀` with relative error `r` and absolute error
`a`: `|x - x₀| ≤ r * |x₀| + a`, where `r` and `a` are nonnegative. The relative part describes
rounding in the normal range. The absolute part covers gradual underflow and the error that
cancellation leaves behind. Unlike a relative bound, the predicate makes sense at `x₀ = 0`. For
nonzero `x₀` the error relative to `|x₀|` is at most `r + a / |x₀|`, so unlike a fixed absolute
tolerance the bound keeps the leading digits of a small exact value whenever `r` is small and `a`
is much smaller than `|x₀|`. A zero coefficient describes the shape of the bound, not a measured
error: `r = 0` is a pure absolute bound and `a = 0` a pure relative one.

An error analysis applies one lemma per operation. `MixedError.of_standardModel` reads the
standard model of a rounding as a mixed error, and `MixedError.trans` composes the error already
present in the operands of a rounded operation with the error of that rounding. The other lemmas
carry a bound through an exact real operation with explicit constants: negation, absolute value,
scaling, sums, products, quotients, square roots, `max` and `min`. Sums of same-sign values keep
a relative bound, either the larger of the two relative errors or their average weighted by the
magnitudes of the terms. A difference with cancellation keeps only an absolute one. A purely
relative error below one keeps the sign of the exact value.

The lemmas use Lean's total operations: `x / 0 = 0`, `0⁻¹ = 0`, and `√x = 0` for `x < 0`. The
quotient and reciprocal bounds therefore also hold when the exact denominator is zero, which forces
a computed denominator with pure relative error to be zero too, and the square-root bounds allow
a negative computed argument. The weighted sum bounds divide by `|x₀ + y₀|`, which is `0 / 0 = 0`
when both exact terms vanish.

## Main definitions

* `FloatLib.Numerics.MixedError`: approximation with relative and absolute error.

## Main results

* `MixedError.trans`: composition of two approximation steps.
* `MixedError.add_of_mul_nonneg`, `MixedError.add_of_mul_nonneg_weighted`, `MixedError.mul`,
  `MixedError.div`: relative bounds for same-sign sums, products and quotients.
* `MixedError.sqrt`: square root keeps the relative error and takes the square root of the
  absolute error.
* `MixedError.sqrt_of_pos`: above zero, square root divides the error by
  `√x₀ + √((1 - r) * x₀ - a)`, about `2 * √x₀`.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
`MixedError x x₀ r a` states that `x` approximates `x₀` with relative error `r` and absolute error
`a`, both nonnegative: `|x - x₀| ≤ r * |x₀| + a`.
-/
structure MixedError (x x₀ r a : ℝ) : Prop where
  /-- The relative error is nonnegative. -/
  r_nonneg : 0 ≤ r
  /-- The absolute error is nonnegative. -/
  a_nonneg : 0 ≤ a
  /-- The error is at most `r` times the magnitude of the exact value, plus `a`. -/
  bound : |x - x₀| ≤ r * |x₀| + a

/-- With both coefficients zero, the approximation is exact. -/
@[simp] theorem mixedError_zero_zero_iff {x x₀ : ℝ} : MixedError x x₀ 0 0 ↔ x = x₀ := by
  refine ⟨fun h => ?_, fun h => ⟨le_rfl, le_rfl, by simp [h]⟩⟩
  simpa [sub_eq_zero] using h.bound

/-- `|√x - √y| * (√x + √y) ≤ |x - y|` for all reals, where `√` is zero below zero. -/
theorem abs_sqrt_sub_sqrt_mul_le (x y : ℝ) : |√x - √y| * (√x + √y) ≤ |x - y| := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · refine le_of_eq ?_
    rw [← abs_of_nonneg (by positivity : 0 ≤ √x + √y), ← abs_mul,
      show (√x - √y) * (√x + √y) = √x * √x - √y * √y by ring, Real.mul_self_sqrt hx,
      Real.mul_self_sqrt hy]
  · rw [Real.sqrt_eq_zero_of_nonpos hy, sub_zero, add_zero, abs_of_nonneg (Real.sqrt_nonneg x),
      Real.mul_self_sqrt hx, abs_of_nonneg (by linarith)]
    linarith
  · rw [Real.sqrt_eq_zero_of_nonpos hx, zero_sub, zero_add, abs_neg,
      abs_of_nonneg (Real.sqrt_nonneg y), Real.mul_self_sqrt hy, abs_of_nonpos (by linarith)]
    linarith
  · rw [Real.sqrt_eq_zero_of_nonpos hx, Real.sqrt_eq_zero_of_nonpos hy]
    simp

/-- `|√x - √y| ≤ |x - y| / (√x + √y)` for all reals; both sides vanish when `√x + √y = 0`. -/
theorem abs_sqrt_sub_sqrt_le_div_add (x y : ℝ) : |√x - √y| ≤ |x - y| / (√x + √y) := by
  rcases (add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)).eq_or_lt with hzero | hpos
  · have hx : √x = 0 := by linarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
    have hy : √y = 0 := by linarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
    simp [hx, hy]
  · rw [le_div_iff₀ hpos]
    exact abs_sqrt_sub_sqrt_mul_le x y

namespace MixedError

variable {x x₀ y y₀ z r a r' a' rx ax ry ay c m : ℝ}

/-! ### Basic properties -/

/-- An exact value has no error. -/
theorem of_eq (h : x = x₀) : MixedError x x₀ 0 0 :=
  mixedError_zero_zero_iff.2 h

/-- Every real number approximates itself without error. -/
protected theorem refl (x : ℝ) : MixedError x x 0 0 :=
  of_eq rfl

/-- Larger error constants give a weaker bound. -/
theorem mono (h : MixedError x x₀ r a) (hr : r ≤ r') (ha : a ≤ a') :
    MixedError x x₀ r' a' := by
  refine ⟨h.r_nonneg.trans hr, h.a_nonneg.trans ha, h.bound.trans ?_⟩
  gcongr

/-- An absolute error bound is a mixed bound without relative part. -/
theorem of_abs_sub_le (h : |x - x₀| ≤ a) : MixedError x x₀ 0 a :=
  ⟨le_rfl, (abs_nonneg _).trans h, by simpa using h⟩

/-- A relative error bound is a mixed bound without absolute part. -/
theorem of_abs_sub_le_mul (hr : 0 ≤ r) (h : |x - x₀| ≤ r * |x₀|) : MixedError x x₀ r 0 :=
  ⟨hr, le_rfl, by simpa using h⟩

/--
The standard model of rounding, `x = x₀ * (1 + δ) + η` with `|δ| ≤ r` and `|η| ≤ a`, is a mixed
error.
-/
theorem of_standardModel (h : ∃ δ η : ℝ, x = x₀ * (1 + δ) + η ∧ |δ| ≤ r ∧ |η| ≤ a) :
    MixedError x x₀ r a := by
  obtain ⟨δ, η, rfl, hδ, hη⟩ := h
  refine ⟨(abs_nonneg δ).trans hδ, (abs_nonneg η).trans hη, ?_⟩
  calc |x₀ * (1 + δ) + η - x₀| = |x₀ * δ + η| := by ring_nf
    _ ≤ |x₀| * |δ| + |η| := by rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ r * |x₀| + a := by rw [mul_comm]; gcongr

/-- A bound `|x₀| ≤ c` turns the mixed bound into the absolute bound `r * c + a`. -/
theorem abs_sub_le_of_abs_le (h : MixedError x x₀ r a) (hc : |x₀| ≤ c) :
    |x - x₀| ≤ r * c + a :=
  h.bound.trans (by have := h.r_nonneg; gcongr)

/-- A bound `|x₀| ≤ c` turns the error `(r, a)` into the absolute error `r * c + a`. -/
theorem absolute_of_abs_le (h : MixedError x x₀ r a) (hc : |x₀| ≤ c) :
    MixedError x x₀ 0 (r * c + a) :=
  of_abs_sub_le (h.abs_sub_le_of_abs_le hc)

/-- A lower bound `0 < m ≤ |x₀|` turns the error `(r, a)` into the relative error `r + a / m`. -/
theorem relative_of_le_abs (h : MixedError x x₀ r a) (hm : 0 < m) (hc : m ≤ |x₀|) :
    MixedError x x₀ (r + a / m) 0 := by
  have ha := h.a_nonneg
  refine of_abs_sub_le_mul (add_nonneg h.r_nonneg (by positivity)) (h.bound.trans ?_)
  have : a ≤ a / m * |x₀| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    gcongr
  linarith

/-- The approximation is at most `(1 + r) * |x₀| + a` in magnitude. -/
protected theorem abs_le (h : MixedError x x₀ r a) : |x| ≤ (1 + r) * |x₀| + a := by
  have := abs_sub_abs_le_abs_sub x x₀
  linarith [h.bound]

/-- The approximation is at least the lower end `x₀ - (r * |x₀| + a)` of its enclosure. -/
theorem lower_le (h : MixedError x x₀ r a) : x₀ - (r * |x₀| + a) ≤ x := by
  linarith [neg_abs_le (x - x₀), h.bound]

/-- The approximation is at most the upper end `x₀ + (r * |x₀| + a)` of its enclosure. -/
theorem le_upper (h : MixedError x x₀ r a) : x ≤ x₀ + (r * |x₀| + a) := by
  linarith [le_abs_self (x - x₀), h.bound]

/-- The lower end of the enclosure is at most the exact value. -/
theorem lower_le_center (h : MixedError x x₀ r a) : x₀ - (r * |x₀| + a) ≤ x₀ :=
  sub_le_self _ (add_nonneg (mul_nonneg h.r_nonneg (abs_nonneg _)) h.a_nonneg)

/-- The exact value is at most the upper end of the enclosure. -/
theorem center_le_upper (h : MixedError x x₀ r a) : x₀ ≤ x₀ + (r * |x₀| + a) :=
  le_add_of_nonneg_right (add_nonneg (mul_nonneg h.r_nonneg (abs_nonneg _)) h.a_nonneg)

/-- The approximation is at least `(1 - r) * |x₀| - a` in magnitude. -/
protected theorem le_abs (h : MixedError x x₀ r a) : (1 - r) * |x₀| - a ≤ |x| := by
  have := abs_sub_abs_le_abs_sub x₀ x
  rw [abs_sub_comm] at this
  linarith [h.bound]

/-- An error smaller than the exact magnitude leaves the approximation nonzero. -/
theorem ne_zero (h : MixedError x x₀ r a) (hlt : r * |x₀| + a < |x₀|) : x ≠ 0 := by
  rintro rfl
  have := h.bound
  rw [zero_sub, abs_neg] at this
  linarith

/-- An error smaller than a positive exact value leaves the approximation positive. -/
theorem pos (h : MixedError x x₀ r a) (hlt : r * |x₀| + a < x₀) : 0 < x := by
  linarith [neg_abs_le (x - x₀), h.bound]

/--
An error smaller than the magnitude of a negative exact value leaves the approximation negative.
-/
theorem lt_zero (h : MixedError x x₀ r a) (hlt : r * |x₀| + a < -x₀) : x < 0 := by
  linarith [le_abs_self (x - x₀), h.bound]

/-- A pure relative error below one keeps a positive exact value positive. -/
theorem pos_of_pos (h : MixedError x x₀ r 0) (hr : r < 1) (hx₀ : 0 < x₀) : 0 < x :=
  h.pos (by rw [abs_of_pos hx₀, add_zero]; nlinarith)

/-- A pure relative error below one keeps a negative exact value negative. -/
theorem lt_zero_of_lt_zero (h : MixedError x x₀ r 0) (hr : r < 1) (hx₀ : x₀ < 0) : x < 0 :=
  h.lt_zero (by rw [abs_of_neg hx₀, add_zero]; nlinarith)

/-- A pure relative error below one keeps a nonzero exact value nonzero. -/
theorem ne_zero_of_ne_zero (h : MixedError x x₀ r 0) (hr : r < 1) (hx₀ : x₀ ≠ 0) : x ≠ 0 :=
  h.ne_zero (by rw [add_zero]; nlinarith [abs_pos.mpr hx₀])

/-! ### Composition -/

/--
If `x` approximates `y` with error `(r, a)` and `y` approximates `z` with error `(r', a')`, then
`x` approximates `z` with relative error `(1 + r) * r' + r` and absolute error
`(1 + r) * a' + a`. With `y` the exact result of an operation on approximate operands, `z` the
exact result on exact operands and `(r, a)` the error of rounding `y`, this bounds a rounded
operation.
-/
protected theorem trans (h : MixedError x y r a) (h' : MixedError y z r' a') :
    MixedError x z ((1 + r) * r' + r) ((1 + r) * a' + a) := by
  have hr := h.r_nonneg
  have ha := h.a_nonneg
  have hr' := h'.r_nonneg
  have ha' := h'.a_nonneg
  refine ⟨by positivity, by positivity, ?_⟩
  calc |x - z| ≤ |x - y| + |y - z| := abs_sub_le x y z
    _ ≤ r * |y| + a + (r' * |z| + a') := add_le_add h.bound h'.bound
    _ ≤ r * ((1 + r') * |z| + a') + a + (r' * |z| + a') := by gcongr; exact h'.abs_le
    _ = ((1 + r) * r' + r) * |z| + ((1 + r) * a' + a) := by ring

/--
Rounding a perturbed value: if `x` approximates `y` with error `(r, a)` and `|y - z| ≤ c`, then
`x` approximates `z` with relative error `r` and absolute error `(1 + r) * c + a`.
-/
theorem trans_of_abs_sub_le (h : MixedError x y r a) (hc : |y - z| ≤ c) :
    MixedError x z r ((1 + r) * c + a) := by
  simpa only [mul_zero, zero_add] using h.trans (of_abs_sub_le hc)

/-! ### Exact real operations -/

/-- Negation preserves the error. -/
theorem neg (h : MixedError x x₀ r a) : MixedError (-x) (-x₀) r a :=
  ⟨h.r_nonneg, h.a_nonneg, by simpa only [neg_sub_neg, abs_sub_comm, abs_neg] using h.bound⟩

/-- The absolute value preserves the error. -/
protected theorem abs (h : MixedError x x₀ r a) : MixedError |x| |x₀| r a :=
  ⟨h.r_nonneg, h.a_nonneg, by
    simpa only [abs_abs] using (abs_abs_sub_abs_le_abs_sub x x₀).trans h.bound⟩

/--
Scaling by an exact constant `c` keeps the relative error and multiplies the absolute error by
`|c|`.
-/
theorem const_mul (h : MixedError x x₀ r a) (c : ℝ) :
    MixedError (c * x) (c * x₀) r (|c| * a) := by
  refine ⟨h.r_nonneg, mul_nonneg (abs_nonneg c) h.a_nonneg, ?_⟩
  rw [← mul_sub, abs_mul, abs_mul]
  calc |c| * |x - x₀| ≤ |c| * (r * |x₀| + a) := by gcongr; exact h.bound
    _ = r * (|c| * |x₀|) + |c| * a := by ring

/--
A sum has the pure absolute bound `rx * |x₀| + ax + (ry * |y₀| + ay)`, the sum of the error bounds
of its terms.
-/
theorem add (hx : MixedError x x₀ rx ax) (hy : MixedError y y₀ ry ay) :
    MixedError (x + y) (x₀ + y₀) 0 (rx * |x₀| + ax + (ry * |y₀| + ay)) := by
  refine of_abs_sub_le ?_
  calc |x + y - (x₀ + y₀)| = |(x - x₀) + (y - y₀)| := by ring_nf
    _ ≤ |x - x₀| + |y - y₀| := abs_add_le _ _
    _ ≤ rx * |x₀| + ax + (ry * |y₀| + ay) := add_le_add hx.bound hy.bound

/--
A sum of two exact values of the same sign has relative error `max rx ry` and absolute error
`ax + ay`.
-/
theorem add_of_mul_nonneg (hx : MixedError x x₀ rx ax) (hy : MixedError y y₀ ry ay)
    (hsign : 0 ≤ x₀ * y₀) :
    MixedError (x + y) (x₀ + y₀) (max rx ry) (ax + ay) := by
  refine ⟨le_max_of_le_left hx.r_nonneg, add_nonneg hx.a_nonneg hy.a_nonneg, ?_⟩
  have habs : |x₀ + y₀| = |x₀| + |y₀| :=
    (abs_add_eq_add_abs_iff x₀ y₀).2 (mul_nonneg_iff.1 hsign)
  calc |x + y - (x₀ + y₀)| = |(x - x₀) + (y - y₀)| := by ring_nf
    _ ≤ |x - x₀| + |y - y₀| := abs_add_le _ _
    _ ≤ rx * |x₀| + ax + (ry * |y₀| + ay) := add_le_add hx.bound hy.bound
    _ ≤ max rx ry * |x₀| + ax + (max rx ry * |y₀| + ay) := by
      gcongr
      exacts [le_max_left _ _, le_max_right _ _]
    _ = max rx ry * |x₀ + y₀| + (ax + ay) := by rw [habs]; ring

/--
A sum of two exact values of the same sign has relative error
`(rx * |x₀| + ry * |y₀|) / |x₀ + y₀|`, the average of the terms' relative errors weighted by their
magnitudes, and absolute error `ax + ay`. The total bound is then the sum of the terms' bounds.
When both exact terms are zero the relative error is `0 / 0 = 0`.
-/
theorem add_of_mul_nonneg_weighted (hx : MixedError x x₀ rx ax) (hy : MixedError y y₀ ry ay)
    (hsign : 0 ≤ x₀ * y₀) :
    MixedError (x + y) (x₀ + y₀) ((rx * |x₀| + ry * |y₀|) / |x₀ + y₀|) (ax + ay) := by
  have hrx := hx.r_nonneg
  have hry := hy.r_nonneg
  have hsum : |x₀ + y₀| = |x₀| + |y₀| :=
    (abs_add_eq_add_abs_iff x₀ y₀).2 (mul_nonneg_iff.1 hsign)
  have hweighted : (rx * |x₀| + ry * |y₀|) / |x₀ + y₀| * |x₀ + y₀| = rx * |x₀| + ry * |y₀| := by
    rcases eq_or_ne |x₀ + y₀| 0 with hzero | hzero
    · have hx₀ : |x₀| = 0 := by linarith [abs_nonneg x₀, abs_nonneg y₀]
      have hy₀ : |y₀| = 0 := by linarith [abs_nonneg x₀, abs_nonneg y₀]
      simp [hx₀, hy₀]
    · exact div_mul_cancel₀ _ hzero
  refine ⟨by positivity, add_nonneg hx.a_nonneg hy.a_nonneg, ?_⟩
  calc |x + y - (x₀ + y₀)| = |(x - x₀) + (y - y₀)| := by ring_nf
    _ ≤ |x - x₀| + |y - y₀| := abs_add_le _ _
    _ ≤ rx * |x₀| + ax + (ry * |y₀| + ay) := add_le_add hx.bound hy.bound
    _ = (rx * |x₀| + ry * |y₀|) / |x₀ + y₀| * |x₀ + y₀| + (ax + ay) := by rw [hweighted]; ring

/--
A difference has the pure absolute bound `rx * |x₀| + ax + (ry * |y₀| + ay)`, the sum of the error
bounds of its operands.
-/
theorem sub (hx : MixedError x x₀ rx ax) (hy : MixedError y y₀ ry ay) :
    MixedError (x - y) (x₀ - y₀) 0 (rx * |x₀| + ax + (ry * |y₀| + ay)) := by
  simpa only [sub_eq_add_neg, abs_neg] using hx.add hy.neg

/--
A difference of two exact values of opposite signs has relative error `max rx ry` and absolute
error `ax + ay`.
-/
theorem sub_of_mul_nonpos (hx : MixedError x x₀ rx ax) (hy : MixedError y y₀ ry ay)
    (hsign : x₀ * y₀ ≤ 0) :
    MixedError (x - y) (x₀ - y₀) (max rx ry) (ax + ay) := by
  simpa only [sub_eq_add_neg] using
    hx.add_of_mul_nonneg hy.neg (by rw [mul_neg]; exact neg_nonneg.2 hsign)

/--
A difference of two exact values of opposite signs has relative error
`(rx * |x₀| + ry * |y₀|) / |x₀ - y₀|`, the average of the operands' relative errors weighted by
their magnitudes, and absolute error `ax + ay`. When both exact operands are zero the relative
error is `0 / 0 = 0`.
-/
theorem sub_of_mul_nonpos_weighted (hx : MixedError x x₀ rx ax) (hy : MixedError y y₀ ry ay)
    (hsign : x₀ * y₀ ≤ 0) :
    MixedError (x - y) (x₀ - y₀) ((rx * |x₀| + ry * |y₀|) / |x₀ - y₀|) (ax + ay) := by
  simpa only [sub_eq_add_neg, abs_neg] using
    hx.add_of_mul_nonneg_weighted hy.neg (by rw [mul_neg]; exact neg_nonneg.2 hsign)

/--
A product has relative error `rx + ry + rx * ry` and absolute error
`(1 + ry) * ax * |y₀| + (1 + rx) * ay * |x₀| + ax * ay`: each absolute error is scaled by the
magnitude of the other factor.
-/
theorem mul (hx : MixedError x x₀ rx ax) (hy : MixedError y y₀ ry ay) :
    MixedError (x * y) (x₀ * y₀) (rx + ry + rx * ry)
      ((1 + ry) * ax * |y₀| + (1 + rx) * ay * |x₀| + ax * ay) := by
  have hrx := hx.r_nonneg
  have hax := hx.a_nonneg
  have hry := hy.r_nonneg
  have hay := hy.a_nonneg
  refine ⟨by positivity, by positivity, ?_⟩
  have hsplit : x * y - x₀ * y₀ = (x - x₀) * y₀ + x₀ * (y - y₀) + (x - x₀) * (y - y₀) := by
    ring
  calc |x * y - x₀ * y₀|
      ≤ |x - x₀| * |y₀| + |x₀| * |y - y₀| + |x - x₀| * |y - y₀| := by
        rw [hsplit, ← abs_mul, ← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ (rx * |x₀| + ax) * |y₀| + |x₀| * (ry * |y₀| + ay) +
        (rx * |x₀| + ax) * (ry * |y₀| + ay) := by
      gcongr
      exacts [hx.bound, hy.bound, hx.bound, hy.bound]
    _ = (rx + ry + rx * ry) * |x₀ * y₀| +
        ((1 + ry) * ax * |y₀| + (1 + rx) * ay * |x₀| + ax * ay) := by
      rw [abs_mul]
      ring

/--
The reciprocal of a value with pure relative error `r < 1` has relative error `r / (1 - r)`. At
`x₀ = 0` the hypothesis forces `x = 0`, and both reciprocals are `0` in Lean.
-/
theorem inv (h : MixedError x x₀ r 0) (hr : r < 1) :
    MixedError x⁻¹ x₀⁻¹ (r / (1 - r)) 0 := by
  have hr0 := h.r_nonneg
  have h1r : 0 < 1 - r := by linarith
  refine of_abs_sub_le_mul (by positivity) ?_
  rcases eq_or_ne x₀ 0 with rfl | hx₀
  · have : x = 0 := by simpa using h.bound
    simp [this]
  have hlow : (1 - r) * |x₀| ≤ |x| := by simpa using h.le_abs
  have hx : 0 < |x| := lt_of_lt_of_le (by positivity) hlow
  rw [inv_sub_inv (abs_pos.1 hx) hx₀, abs_div, abs_mul, abs_inv, div_le_iff₀ (by positivity)]
  calc |x₀ - x| ≤ r * |x₀| := by simpa [abs_sub_comm] using h.bound
    _ = r / (1 - r) * |x₀|⁻¹ * ((1 - r) * |x₀| * |x₀|) := by
      field_simp
    _ ≤ r / (1 - r) * |x₀|⁻¹ * (|x| * |x₀|) := by gcongr

/--
A quotient by a value with pure relative error `ry < 1` has relative error `(rx + ry) / (1 - ry)`,
and the absolute error of the numerator is divided by `(1 - ry) * |y₀|`. At `y₀ = 0` the
hypothesis forces `y = 0`, both quotients are `0` in Lean, and the absolute error is `ax / 0 = 0`.
A lower bound on `|y₀|` turns a mixed error of the denominator into a relative one, by
`relative_of_le_abs`.
-/
theorem div (hx : MixedError x x₀ rx ax) (hy : MixedError y y₀ ry 0) (hry : ry < 1) :
    MixedError (x / y) (x₀ / y₀) ((rx + ry) / (1 - ry)) (ax / ((1 - ry) * |y₀|)) := by
  have hrx := hx.r_nonneg
  have hax := hx.a_nonneg
  have hry0 := hy.r_nonneg
  have h1r : 0 < 1 - ry := by linarith
  refine ⟨by positivity, by positivity, ?_⟩
  rcases eq_or_ne y₀ 0 with rfl | hy₀
  · have : y = 0 := by simpa using hy.bound
    simp [this]
  have hlow : (1 - ry) * |y₀| ≤ |y| := by simpa using hy.le_abs
  have hden : 0 < (1 - ry) * |y₀| := by positivity
  have hinv : |y⁻¹ - y₀⁻¹| ≤ ry / (1 - ry) * |y₀|⁻¹ := by
    simpa [abs_inv] using (hy.inv hry).bound
  calc |x / y - x₀ / y₀| = |(x - x₀) * y⁻¹ + x₀ * (y⁻¹ - y₀⁻¹)| := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring_nf
    _ ≤ |x - x₀| * |y|⁻¹ + |x₀| * |y⁻¹ - y₀⁻¹| := by
      rw [← abs_inv, ← abs_mul, ← abs_mul]
      exact abs_add_le _ _
    _ ≤ (rx * |x₀| + ax) * ((1 - ry) * |y₀|)⁻¹ + |x₀| * (ry / (1 - ry) * |y₀|⁻¹) := by
      gcongr
      exact hx.bound
    _ = (rx + ry) / (1 - ry) * |x₀ / y₀| + ax / ((1 - ry) * |y₀|) := by
      rw [abs_div]
      field_simp
      ring

/--
A quotient by a value with mixed error `(ry, ay)` whose exact magnitude is at least `m > 0` has the
error of `div` for the relative denominator error `ry + ay / m`, when that is below one.
-/
theorem div_of_le_abs (hx : MixedError x x₀ rx ax) (hy : MixedError y y₀ ry ay) (hm : 0 < m)
    (hle : m ≤ |y₀|) (hr : ry + ay / m < 1) :
    MixedError (x / y) (x₀ / y₀) ((rx + (ry + ay / m)) / (1 - (ry + ay / m)))
      (ax / ((1 - (ry + ay / m)) * |y₀|)) :=
  hx.div (hy.relative_of_le_abs hm hle) hr

/-- The square-root error bound `|√x - √x₀| ≤ √|x - x₀|` for a nonnegative `x₀`. -/
private theorem abs_sqrt_sub_sqrt_le_sqrt (x : ℝ) (hx₀ : 0 ≤ x₀) :
    |√x - √x₀| ≤ √|x - x₀| := by
  rw [Real.le_sqrt (abs_nonneg _) (abs_nonneg _), sq_abs]
  rcases le_total 0 x with hx | hx
  · have hs := Real.sq_sqrt hx
    have ht := Real.sq_sqrt hx₀
    rcases le_total x₀ x with hle | hle
    · rw [abs_of_nonneg (sub_nonneg.2 hle)]
      nlinarith [mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg x₀)]
    · rw [abs_of_nonpos (sub_nonpos.2 hle)]
      nlinarith [mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg x)]
  · rw [Real.sqrt_eq_zero_of_nonpos hx, abs_of_nonpos (by linarith), zero_sub, neg_sq,
      Real.sq_sqrt hx₀]
    linarith

/-- The square-root error bound `|√x - √x₀| ≤ |x - x₀| / √x₀` for a positive `x₀`. -/
private theorem abs_sqrt_sub_sqrt_le_div (x : ℝ) (hx₀ : 0 < x₀) :
    |√x - √x₀| ≤ |x - x₀| / √x₀ := by
  rw [le_div_iff₀ (Real.sqrt_pos.2 hx₀)]
  exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.sqrt_nonneg x))
    (abs_nonneg _)).trans (abs_sqrt_sub_sqrt_mul_le x x₀)

/--
The square root of a value whose exact value is nonnegative keeps the relative error and takes
the square root of the absolute error. The absolute part is the Hölder bound near zero, where the
square root has no Lipschitz constant. The computed value may be negative, where `√x = 0`.
-/
theorem sqrt (h : MixedError x x₀ r a) (hx₀ : 0 ≤ x₀) :
    MixedError (√x) (√x₀) r (√a) := by
  have hr := h.r_nonneg
  have ha := h.a_nonneg
  refine ⟨hr, Real.sqrt_nonneg a, ?_⟩
  have hb : |x - x₀| ≤ r * x₀ + a := by simpa [abs_of_nonneg hx₀] using h.bound
  rw [abs_of_nonneg (Real.sqrt_nonneg x₀)]
  rcases le_or_gt x₀ a with hxa | hax
  · -- Near zero, `√(r * x₀ + a) ≤ r * √x₀ + √a` because `√x₀ ≤ √a`.
    have hsle : √x₀ * √x₀ ≤ √x₀ * √a :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxa) (Real.sqrt_nonneg x₀)
    calc |√x - √x₀| ≤ √|x - x₀| := abs_sqrt_sub_sqrt_le_sqrt x hx₀
      _ ≤ √(r * x₀ + a) := Real.sqrt_le_sqrt hb
      _ ≤ r * √x₀ + √a := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hsle hr,
          congrArg (r * ·) (Real.mul_self_sqrt hx₀), Real.mul_self_sqrt ha,
          mul_nonneg (mul_nonneg hr (Real.sqrt_nonneg x₀)) (Real.sqrt_nonneg a),
          mul_nonneg (mul_nonneg hr hr) (mul_self_nonneg √x₀)]
  · have hpos : 0 < x₀ := ha.trans_lt hax
    have hs₀ : 0 < √x₀ := Real.sqrt_pos.2 hpos
    calc |√x - √x₀| ≤ |x - x₀| / √x₀ := abs_sqrt_sub_sqrt_le_div x hpos
      _ ≤ (r * x₀ + a) / √x₀ := by gcongr
      _ = r * √x₀ + a / √x₀ := by rw [add_div, mul_div_assoc, Real.div_sqrt]
      _ ≤ r * √x₀ + √a := by
        gcongr
        rw [div_le_iff₀ hs₀]
        nlinarith [Real.mul_self_sqrt ha,
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hax.le) (Real.sqrt_nonneg a)]

/--
Away from zero, with `0 < m ≤ x₀`, the square root keeps the relative error and divides the
absolute error by `√m`.
-/
theorem sqrt_of_le (h : MixedError x x₀ r a) (hm : 0 < m) (hmx : m ≤ x₀) :
    MixedError (√x) (√x₀) r (a / √m) := by
  have hr := h.r_nonneg
  have ha := h.a_nonneg
  have hx₀ : 0 < x₀ := hm.trans_le hmx
  refine ⟨hr, by positivity, ?_⟩
  have hb : |x - x₀| ≤ r * x₀ + a := by simpa [abs_of_pos hx₀] using h.bound
  rw [abs_of_nonneg (Real.sqrt_nonneg x₀)]
  calc |√x - √x₀| ≤ |x - x₀| / √x₀ := abs_sqrt_sub_sqrt_le_div x hx₀
    _ ≤ (r * x₀ + a) / √x₀ := by gcongr
    _ = r * √x₀ + a / √x₀ := by rw [add_div, mul_div_assoc, Real.div_sqrt]
    _ ≤ r * √x₀ + a / √m := by gcongr

/--
Above zero the square root divides the error by `√x₀ + √((1 - r) * x₀ - a)`, a lower bound of
`√x₀ + √x`, which halves the relative error to first order. The absolute part is at most `√a`.
-/
theorem sqrt_of_pos (h : MixedError x x₀ r a) (hx₀ : 0 < x₀) :
    MixedError (√x) (√x₀) (r * √x₀ / (√x₀ + √((1 - r) * x₀ - a)))
      (min (√a) (a / (√x₀ + √((1 - r) * x₀ - a)))) := by
  have hr := h.r_nonneg
  have ha := h.a_nonneg
  have hs₀ : 0 < √x₀ := Real.sqrt_pos.2 hx₀
  set D := √x₀ + √((1 - r) * x₀ - a) with hD
  have hDpos : 0 < D := add_pos_of_pos_of_nonneg hs₀ (Real.sqrt_nonneg _)
  refine ⟨by positivity, le_min (Real.sqrt_nonneg a) (by positivity), ?_⟩
  have hb : |x - x₀| ≤ r * x₀ + a := by simpa [abs_of_pos hx₀] using h.bound
  have hlower : (1 - r) * x₀ - a ≤ x := by
    have := (abs_le.mp hb).1
    linarith
  have hDle : D ≤ √x + √x₀ := by
    rw [hD, add_comm (√x)]
    exact add_le_add le_rfl (Real.sqrt_le_sqrt hlower)
  have hmain : |√x - √x₀| ≤ r * √x₀ / D * √x₀ + a / D := by
    rw [div_mul_eq_mul_div, mul_assoc, Real.mul_self_sqrt hx₀.le, ← add_div, le_div_iff₀ hDpos]
    calc |√x - √x₀| * D ≤ |√x - √x₀| * (√x + √x₀) :=
          mul_le_mul_of_nonneg_left hDle (abs_nonneg _)
      _ ≤ |x - x₀| := abs_sqrt_sub_sqrt_mul_le x x₀
      _ ≤ r * x₀ + a := hb
  rw [abs_of_nonneg (Real.sqrt_nonneg x₀)]
  by_cases hsmall : a / D ≤ √a
  · rw [min_eq_right hsmall]
    exact hmain
  · have hlarge : √a < a / D := lt_of_not_ge hsmall
    rw [min_eq_left hlarge.le]
    -- `√a < a / D` forces `x₀ < a`, so the second root vanishes and `D = √x₀`.
    have hDa : D ≤ √a := by
      rw [lt_div_iff₀ hDpos] at hlarge
      have hapos : 0 < a := by
        rcases ha.eq_or_lt with ha0 | hapos
        · subst ha0; simp at hlarge
        · exact hapos
      have hsa : 0 < √a := Real.sqrt_pos.2 hapos
      nlinarith [Real.mul_self_sqrt ha]
    have hxa : x₀ ≤ a := by
      have : √x₀ ≤ √a := le_trans (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hDa
      exact (Real.sqrt_le_sqrt_iff ha).mp this
    have hneg : (1 - r) * x₀ - a ≤ 0 := by nlinarith
    have hDeq : D = √x₀ := by rw [hD, Real.sqrt_eq_zero_of_nonpos hneg, add_zero]
    have hold := (h.sqrt hx₀.le).bound
    rw [abs_of_nonneg (Real.sqrt_nonneg x₀)] at hold
    rw [hDeq, mul_div_assoc, div_self hs₀.ne', mul_one]
    exact hold

/--
A maximum has the pure absolute bound `max (rx * |x₀| + ax) (ry * |y₀| + ay)`, the larger of the
operands' error bounds.
-/
protected theorem max (hx : MixedError x x₀ rx ax) (hy : MixedError y y₀ ry ay) :
    MixedError (max x y) (max x₀ y₀) 0 (max (rx * |x₀| + ax) (ry * |y₀| + ay)) :=
  of_abs_sub_le ((abs_max_sub_max_le_max x y x₀ y₀).trans (max_le_max hx.bound hy.bound))

/--
The maximum of two nonnegative exact values has relative error `max rx ry` and absolute error
`max ax ay`.
-/
theorem max_of_nonneg (hx : MixedError x x₀ rx ax) (hy : MixedError y y₀ ry ay)
    (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) :
    MixedError (max x y) (max x₀ y₀) (max rx ry) (max ax ay) := by
  have hrx := hx.r_nonneg
  have hry := hy.r_nonneg
  refine ⟨le_max_of_le_left hrx, le_max_of_le_left hx.a_nonneg, ?_⟩
  rw [abs_of_nonneg (le_max_of_le_left hx₀)]
  refine (abs_max_sub_max_le_max x y x₀ y₀).trans (max_le ?_ ?_)
  · calc |x - x₀| ≤ rx * |x₀| + ax := hx.bound
      _ ≤ max rx ry * max x₀ y₀ + max ax ay := by
        rw [abs_of_nonneg hx₀]
        gcongr
        exacts [le_max_left _ _, le_max_left _ _, le_max_left _ _]
  · calc |y - y₀| ≤ ry * |y₀| + ay := hy.bound
      _ ≤ max rx ry * max x₀ y₀ + max ax ay := by
        rw [abs_of_nonneg hy₀]
        gcongr
        exacts [le_max_right _ _, le_max_right _ _, le_max_right _ _]

/--
A minimum has the pure absolute bound `max (rx * |x₀| + ax) (ry * |y₀| + ay)`, the larger of the
operands' error bounds.
-/
protected theorem min (hx : MixedError x x₀ rx ax) (hy : MixedError y y₀ ry ay) :
    MixedError (min x y) (min x₀ y₀) 0 (max (rx * |x₀| + ax) (ry * |y₀| + ay)) :=
  of_abs_sub_le ((abs_min_sub_min_le_max x y x₀ y₀).trans (max_le_max hx.bound hy.bound))

/--
The minimum of two nonpositive exact values has relative error `max rx ry` and absolute error
`max ax ay`.
-/
theorem min_of_nonpos (hx : MixedError x x₀ rx ax) (hy : MixedError y y₀ ry ay)
    (hx₀ : x₀ ≤ 0) (hy₀ : y₀ ≤ 0) :
    MixedError (min x y) (min x₀ y₀) (max rx ry) (max ax ay) := by
  simpa only [max_neg_neg, neg_neg] using
    (hx.neg.max_of_nonneg hy.neg (neg_nonneg.2 hx₀) (neg_nonneg.2 hy₀)).neg

end MixedError

end FloatLib.Numerics
