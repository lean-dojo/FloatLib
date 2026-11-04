/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Transcendental
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Irrationality of exponentials at nonzero rational arguments

Convergent intervals aren't enough for adaptive rounding, because an interval can straddle an exact
rounding boundary forever. For the exponential at a nonzero rational argument, irrationality rules
that out.

The fact comes from the transcendence theorem in `Elementary.Transcendental`. Inverting the
exponential gives the matching logarithm result, with `log 1 = 0` handled on its own.
-/

public section

namespace FloatLib.Numerics.Enclosure

/-- The exponential of a nonzero integer is irrational. -/
theorem irrational_exp_intCast (m : ℤ) (hm : m ≠ 0) :
    Irrational (Real.exp (m : ℝ)) :=
  (transcendental_exp_intCast m hm).irrational

/-- A nonzero rational input has an irrational exponential. The zero case is exactly `1`. -/
theorem irrational_exp_ratCast (q : ℚ) (hq : q ≠ 0) :
    Irrational (Real.exp (q : ℝ)) :=
  (transcendental_exp_ratCast q hq).irrational

/-- A positive rational input other than `1` has an irrational natural logarithm. -/
theorem irrational_log_ratCast (q : ℚ) (hq : 0 < q) (hqone : q ≠ 1) :
    Irrational (Real.log (q : ℝ)) := by
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  rintro ⟨r, hr⟩
  have hexp : Real.exp (r : ℝ) = (q : ℝ) := by
    rw [hr, Real.exp_log hqreal]
  have hrzero : r ≠ 0 := by
    intro hz
    simp only [hz, Rat.cast_zero, Real.exp_zero] at hexp
    exact hqone (by exact_mod_cast hexp.symm)
  exact (irrational_exp_ratCast r hrzero).ne_rat q hexp

end FloatLib.Numerics.Enclosure
