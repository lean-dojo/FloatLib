/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Hyperbolic
public import FloatLib.Numerics.Enclosure.Interval.ElementaryProof
public import FloatLib.Numerics.Enclosure.Interval.OperationsProof
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Containment for tangent and hyperbolic interval bounds

The tangent proof composes the existing sine, cosine, and division contracts. Hyperbolic sine
is monotone; hyperbolic cosine is monotone on absolute values. Hyperbolic tangent uses the
increasing map `(u - 1) / (u + 1)` on nonnegative exponential values, keeping its denominator
strictly positive even when a coarse exponential enclosure has lower endpoint zero.
-/

public section

namespace FloatLib.Numerics.Interval

/-- Successful tangent bounds contain the tangent of every real member of the input. -/
theorem containsReal_tanBounds? {I K : Interval ℚ} {terms : Nat}
    (h : tanBounds? I terms = some K) {x : ℝ} (hx : I.ContainsReal some x) :
    K.ContainsReal some (Real.tan x) := by
  simpa only [Real.tan_eq_sin_div_cos, Internal.rationalOutwardRounding] using
    containsReal_div? Internal.rationalOutwardRounding h
      (containsReal_sinBounds I terms hx) (containsReal_cosBounds I terms hx)

private theorem containsReal_sinhPointBounds (x : ℚ) (terms : Nat) :
    (Internal.sinhPointBounds x terms).ContainsReal some (Real.sinh x) := by
  have hp := Enclosure.contains_exp x terms
  have hn := Enclosure.contains_exp (-x) terms
  simp only [Rat.cast_neg] at hn
  apply (containsReal_some_iff _ _).mpr
  dsimp [Internal.sinhPointBounds]
  push_cast
  rw [Real.sinh_eq]
  exact ⟨div_le_div_of_nonneg_right (sub_le_sub hp.1 hn.2) (by norm_num),
    div_le_div_of_nonneg_right (sub_le_sub hp.2 hn.1) (by norm_num)⟩

/-- Hyperbolic sine bounds contain the image of every real member of the input. -/
theorem containsReal_sinhBounds (I : Interval ℚ) (terms : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) :
    (sinhBounds I terms).ContainsReal some (Real.sinh x) := by
  apply containsReal_monotoneBounds _ Real.sinh I
    (Real.sinh_strictMono.monotone.monotoneOn _) ?_ hx
  intro q _
  exact containsReal_sinhPointBounds q terms

private theorem containsReal_coshPointBounds (x : ℚ) (terms : Nat) :
    (Internal.coshPointBounds x terms).ContainsReal some (Real.cosh x) := by
  have hp := Enclosure.contains_exp x terms
  have hn := Enclosure.contains_exp (-x) terms
  simp only [Rat.cast_neg] at hn
  apply (containsReal_some_iff _ _).mpr
  dsimp [Internal.coshPointBounds]
  push_cast
  refine ⟨max_le (Real.one_le_cosh _) ?_, ?_⟩
  · rw [Real.cosh_eq]
    exact div_le_div_of_nonneg_right (add_le_add hp.1 hn.1) (by norm_num)
  · rw [Real.cosh_eq]
    exact div_le_div_of_nonneg_right (add_le_add hp.2 hn.2) (by norm_num)

/-- Hyperbolic cosine bounds retain the minimum at zero and contain the whole real image. -/
theorem containsReal_coshBounds (I : Interval ℚ) (terms : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) :
    (coshBounds I terms).ContainsReal some (Real.cosh x) := by
  have ha : (absBounds I).ContainsReal some |x| :=
    containsReal_abs? Internal.rationalOutwardRounding
      (by simp [abs?, liftUnary?, decode?, encloseInterval?,
        Internal.rationalOutwardRounding, point]) hx
  have hnonneg : 0 ≤ (absBounds I).lo := by
    unfold absBounds
    split
    · assumption
    · split
      · exact neg_nonneg.mpr ‹I.hi ≤ 0›
      · exact le_rfl
  have hnonnegReal : (0 : ℝ) ≤ (absBounds I).lo := by exact_mod_cast hnonneg
  rw [← Real.cosh_abs x]
  apply containsReal_monotoneBounds _ Real.cosh (absBounds I) ?_ ?_ ha
  · intro a ha b hb hab
    exact Real.cosh_strictMonoOn.monotoneOn
      (hnonnegReal.trans ha.1) (hnonnegReal.trans hb.1) hab
  · intro q _
    exact containsReal_coshPointBounds q terms

private theorem tanh_eq_exp_twice (x : ℝ) :
    Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
  rw [Real.tanh_eq, Real.exp_neg, two_mul, Real.exp_add]
  have hpos := Real.exp_pos x
  have hne := ne_of_gt hpos
  have hden : Real.exp x * Real.exp x + 1 ≠ 0 := by positivity
  field_simp

private theorem tanh_ratio_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (a - 1) / (a + 1) ≤ (b - 1) / (b + 1) := by
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

/-- Hyperbolic tangent bounds contain every real image without a denominator-domain failure. -/
theorem containsReal_tanhBounds (I : Interval ℚ) (terms : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) :
    (tanhBounds I terms).ContainsReal some (Real.tanh x) := by
  obtain ⟨hlo, hhi⟩ := (containsReal_some_iff I x).mp hx
  have htwice : (⟨2 * I.lo, 2 * I.hi⟩ : Interval ℚ).ContainsReal some (2 * x) := by
    apply (containsReal_some_iff _ _).mpr
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left hlo (by norm_num),
      mul_le_mul_of_nonneg_left hhi (by norm_num)⟩
  have he := (containsReal_some_iff _ _).mp (containsReal_expBounds _ terms htwice)
  apply (containsReal_some_iff _ _).mpr
  dsimp [tanhBounds]
  push_cast
  rw [tanh_eq_exp_twice]
  exact ⟨tanh_ratio_mono (le_max_left _ _) (max_le (Real.exp_pos _).le he.1),
    tanh_ratio_mono (Real.exp_pos _).le (he.2.trans (le_max_right _ _))⟩

end FloatLib.Numerics.Interval
