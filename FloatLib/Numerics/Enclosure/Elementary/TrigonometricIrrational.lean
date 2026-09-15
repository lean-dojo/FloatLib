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

At a nonzero rational argument, sine, cosine, and tangent are transcendental. If sine or
cosine were algebraic, the identity `sin² x + cos² x = 1` would make both algebraic, and
Euler's formula would contradict the transcendence of `exp (x * I)`. Tangent reduces to
cosine through `cos² x = 1 / (1 + tan² x)`.

The irrationality corollaries rule out exact rational rounding boundaries. The input zero
must be handled separately by executable comparisons.
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

/-- Cosine at a nonzero rational argument is transcendental. -/
theorem transcendental_cos_ratCast (q : ℚ) (hq : q ≠ 0) :
    Transcendental ℚ (Real.cos (q : ℝ)) := by
  intro hcos
  have hsin : IsAlgebraic ℚ (Real.sin (q : ℝ)) := by
    apply IsAlgebraic.of_pow (n := 2) (by decide)
    have hsq : Real.sin (q : ℝ) ^ 2 = 1 - Real.cos (q : ℝ) ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq (q : ℝ)]
    rw [hsq]
    exact isAlgebraic_one.sub (hcos.pow 2)
  apply transcendental_exp_ratCast_mul_I q hq
  simpa using algebraic_exp_mul_I_of_sin_cos hsin hcos

/-- Sine at a nonzero rational argument is transcendental. -/
theorem transcendental_sin_ratCast (q : ℚ) (hq : q ≠ 0) :
    Transcendental ℚ (Real.sin (q : ℝ)) := by
  intro hsin
  apply transcendental_cos_ratCast q hq
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  have hsq : Real.cos (q : ℝ) ^ 2 = 1 - Real.sin (q : ℝ) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (q : ℝ)]
  rw [hsq]
  exact isAlgebraic_one.sub (hsin.pow 2)

/-- A nonzero rational argument cannot be a pole of tangent. -/
theorem cos_ratCast_ne_zero (q : ℚ) (hq : q ≠ 0) : Real.cos (q : ℝ) ≠ 0 := by
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
  rw [← Real.inv_one_add_tan_sq (cos_ratCast_ne_zero q hq)]
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

/-- Inverse tangent at a nonzero rational input is irrational. -/
theorem irrational_arctan_ratCast (q : ℚ) (hq : q ≠ 0) :
    Irrational (Real.arctan (q : ℝ)) := by
  rintro ⟨r, hr⟩
  have htangent : Real.tan (r : ℝ) = q := by rw [hr, Real.tan_arctan]
  have hrzero : r ≠ 0 := by
    intro hzero
    simp only [hzero, Rat.cast_zero, Real.tan_zero] at htangent
    exact hq (by exact_mod_cast htangent.symm)
  exact (irrational_tan_ratCast r hrzero).ne_rat q htangent

/-- Inverse sine at a nonzero rational in its real domain is irrational. -/
theorem irrational_arcsin_ratCast (q : ℚ) (hq : q ≠ 0)
    (hlower : -1 ≤ q) (hupper : q ≤ 1) :
    Irrational (Real.arcsin (q : ℝ)) := by
  rintro ⟨r, hr⟩
  have hsine : Real.sin (r : ℝ) = q := by
    rw [hr, Real.sin_arcsin (by exact_mod_cast hlower) (by exact_mod_cast hupper)]
  have hrzero : r ≠ 0 := by
    intro hzero
    simp only [hzero, Rat.cast_zero, Real.sin_zero] at hsine
    exact hq (by exact_mod_cast hsine.symm)
  exact (irrational_sin_ratCast r hrzero).ne_rat q hsine

/-- Inverse cosine is irrational throughout its rational real domain except at `1`. -/
theorem irrational_arccos_ratCast (q : ℚ) (hq : q ≠ 1)
    (hlower : -1 ≤ q) (hupper : q ≤ 1) :
    Irrational (Real.arccos (q : ℝ)) := by
  rintro ⟨r, hr⟩
  have hcosine : Real.cos (r : ℝ) = q := by
    rw [hr, Real.cos_arccos (by exact_mod_cast hlower) (by exact_mod_cast hupper)]
  have hrzero : r ≠ 0 := by
    intro hzero
    simp only [hzero, Rat.cast_zero, Real.cos_zero] at hcosine
    exact hq (by exact_mod_cast hcosine.symm)
  exact (irrational_cos_ratCast r hrzero).ne_rat q hcosine

end FloatLib.Numerics.Enclosure
