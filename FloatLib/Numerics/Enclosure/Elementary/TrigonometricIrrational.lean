/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.ComplexTranscendental
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Rational trigonometric arguments and rounding boundaries

At a nonzero rational argument, sine, cosine, and tangent are transcendental. If sine or cosine were
algebraic, the identity `sin² x + cos² x = 1` would make both algebraic, and Euler's formula would
contradict the transcendence of `exp (x * I)`. Tangent reduces to cosine through
`cos² x = 1 / (1 + tan² x)`.

The irrationality corollaries rule out exact rational rounding boundaries. Executable comparisons
have to handle the input zero themselves.
-/

public section

namespace FloatLib.Numerics.Enclosure

private theorem algebraic_exp_mul_I_of_sin_cos {x : ℝ}
    (hsin : IsAlgebraic ℚ (Real.sin x)) (hcos : IsAlgebraic ℚ (Real.cos x)) :
    IsAlgebraic ℚ (Complex.exp ((x : ℂ) * Complex.I)) := by
  have hI : IsAlgebraic ℚ Complex.I := IsAlgebraic.of_pow (n := 2) (by decide) (by
    simpa using (isAlgebraic_one (R := ℚ) (A := ℂ)).neg)
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  exact hcos.algebraMap.add (hsin.algebraMap.mul hI)

/--
If `a ^ 2 + b ^ 2 = 1` and `a` is algebraic, so is `b`: the identity `sin² x + cos² x = 1`
passes algebraicity between sine and cosine.
-/
private theorem isAlgebraic_of_sq_add_sq_eq_one {a b : ℝ} (ha : IsAlgebraic ℚ a)
    (h : a ^ 2 + b ^ 2 = 1) : IsAlgebraic ℚ b := by
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  rw [show b ^ 2 = 1 - a ^ 2 by linarith]
  exact isAlgebraic_one.sub (ha.pow 2)

/-- Cosine at a nonzero rational argument is transcendental. -/
theorem transcendental_cos_ratCast (q : ℚ) (hq : q ≠ 0) :
    Transcendental ℚ (Real.cos (q : ℝ)) := by
  intro hcos
  apply transcendental_exp_ratCast_mul_I q hq
  simpa using algebraic_exp_mul_I_of_sin_cos
    (isAlgebraic_of_sq_add_sq_eq_one hcos (Real.cos_sq_add_sin_sq _)) hcos

/-- Sine at a nonzero rational argument is transcendental. -/
theorem transcendental_sin_ratCast (q : ℚ) (hq : q ≠ 0) :
    Transcendental ℚ (Real.sin (q : ℝ)) := fun hsin =>
  transcendental_cos_ratCast q hq (isAlgebraic_of_sq_add_sq_eq_one hsin (Real.sin_sq_add_cos_sq _))

/-- A rational argument cannot be a pole of tangent. -/
theorem cos_ratCast_ne_zero (q : ℚ) : Real.cos (q : ℝ) ≠ 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  intro hzero
  apply transcendental_cos_ratCast q hq
  rw [hzero]
  exact isAlgebraic_zero

/-- Tangent at a nonzero rational argument is transcendental. -/
theorem transcendental_tan_ratCast (q : ℚ) (hq : q ≠ 0) :
    Transcendental ℚ (Real.tan (q : ℝ)) := by
  intro htan
  apply transcendental_cos_ratCast q hq
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  rw [← Real.inv_one_add_tan_sq (cos_ratCast_ne_zero q)]
  exact (isAlgebraic_one.add (htan.pow 2)).inv

/-- Sine at a nonzero rational input cannot equal a rational rounding boundary. -/
theorem irrational_sin_ratCast (q : ℚ) (hq : q ≠ 0) :
    Irrational (Real.sin (q : ℝ)) :=
  (transcendental_sin_ratCast q hq).irrational

/-- Cosine at a nonzero rational input cannot equal a rational rounding boundary. -/
theorem irrational_cos_ratCast (q : ℚ) (hq : q ≠ 0) :
    Irrational (Real.cos (q : ℝ)) :=
  (transcendental_cos_ratCast q hq).irrational

/-- Tangent at a nonzero rational input cannot equal a rational rounding boundary. -/
theorem irrational_tan_ratCast (q : ℚ) (hq : q ≠ 0) :
    Irrational (Real.tan (q : ℝ)) :=
  (transcendental_tan_ratCast q hq).irrational

/--
A value mapped to a rational `q` by a function that is irrational at every nonzero rational, and
that does not take the value `q` at zero, is itself irrational.
-/
private theorem irrational_of_map_eq_ratCast {f : ℝ → ℝ} {y : ℝ} {q : ℚ} (hfy : f y = q)
    (hzero : f 0 ≠ q) (hirrational : ∀ r : ℚ, r ≠ 0 → Irrational (f r)) :
    Irrational y := by
  rintro ⟨r, rfl⟩
  have hr : r ≠ 0 := by
    rintro rfl
    exact hzero (by simpa using hfy)
  exact (hirrational r hr).ne_rat q hfy

/-- Inverse tangent at a nonzero rational input is irrational. -/
theorem irrational_arctan_ratCast (q : ℚ) (hq : q ≠ 0) :
    Irrational (Real.arctan (q : ℝ)) :=
  irrational_of_map_eq_ratCast (Real.tan_arctan _)
    (by rw [Real.tan_zero]; exact_mod_cast hq.symm) irrational_tan_ratCast

/-- Inverse sine at a nonzero rational in its real domain is irrational. -/
theorem irrational_arcsin_ratCast (q : ℚ) (hq : q ≠ 0)
    (hlower : -1 ≤ q) (hupper : q ≤ 1) :
    Irrational (Real.arcsin (q : ℝ)) :=
  irrational_of_map_eq_ratCast
    (Real.sin_arcsin (by exact_mod_cast hlower) (by exact_mod_cast hupper))
    (by rw [Real.sin_zero]; exact_mod_cast hq.symm) irrational_sin_ratCast

/-- Inverse cosine is irrational throughout its rational real domain except at `1`. -/
theorem irrational_arccos_ratCast (q : ℚ) (hq : q ≠ 1)
    (hlower : -1 ≤ q) (hupper : q ≤ 1) :
    Irrational (Real.arccos (q : ℝ)) :=
  irrational_of_map_eq_ratCast
    (Real.cos_arccos (by exact_mod_cast hlower) (by exact_mod_cast hupper))
    (by rw [Real.cos_zero]; exact_mod_cast hq.symm) irrational_cos_ratCast

end FloatLib.Numerics.Enclosure
