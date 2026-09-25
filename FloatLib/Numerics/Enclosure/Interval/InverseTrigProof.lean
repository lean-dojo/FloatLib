/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.InverseTrig
public import FloatLib.Numerics.Enclosure.Interval.ElementaryProof
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.Linarith

/-!
# Real containment for interval arcsine and arccosine

Mathlib's `Real.arcsin_eq_arctan` connects interior point enclosures to arcsine. Its
monotonicity theorem then bounds every real member of an interval by the endpoint images.
The cases at `-1` and `1` use the existing enclosure of π/4. Arccosine containment follows
from `Real.arccos_eq_pi_div_two_sub_arcsin`.
-/

public section

namespace FloatLib.Numerics.Interval

/-- Arcsine preserves exact zero independently of both accuracy parameters. -/
@[simp]
theorem asinBounds?_point_zero (terms precision : Nat) :
    asinBounds? (point 0) terms precision = some (point 0) := by
  simp [asinBounds?, point, Internal.asinPointBounds?]

/-- Arccosine at one is exactly zero independently of both accuracy parameters. -/
@[simp]
theorem acosBounds?_point_one (terms precision : Nat) :
    acosBounds? (point 1) terms precision = some (point 0) := by
  simp [acosBounds?, point]

/-- A successful point enclosure contains the real arcsine, including at both endpoints. -/
theorem Internal.containsReal_asinPointBounds? {q : ℚ} {terms precision : Nat}
    {K : Interval ℚ} (h : asinPointBounds? q terms precision = some K) :
    K.ContainsReal some (Real.arcsin q) := by
  unfold asinPointBounds? at h
  dsimp only at h
  split_ifs at h with hzero hone hneg hdomain hroot
  · subst q
    cases h
    simp [ContainsReal, Contains, point]
  · subst q
    cases h
    apply (containsReal_some_iff _ _).2
    have hpi := Enclosure.contains_piQuarter terms
    simp only [Rat.cast_one, Real.arcsin_one, Rat.cast_mul, Rat.cast_ofNat]
    constructor <;> linarith [hpi.1, hpi.2]
  · subst q
    cases h
    apply (containsReal_some_iff _ _).2
    have hpi := Enclosure.contains_piQuarter terms
    simp only [Rat.cast_neg, Rat.cast_one, Real.arcsin_neg_one,
      Rat.cast_mul, Rat.cast_ofNat]
    constructor <;> linarith [hpi.1, hpi.2]
  · cases h
    have hradicand : 0 ≤ 1 - q ^ 2 := by nlinarith [hdomain.1, hdomain.2]
    have hsqrt := (containsReal_some_iff _ _).1
      (containsReal_sqrtPointBounds (1 - q ^ 2) precision hradicand)
    have hrootReal : (0 : ℝ) < (sqrtPointBounds (1 - q ^ 2) precision).lo := by
      exact_mod_cast hroot
    have hdomainReal : (q : ℝ) ∈ Set.Ioo (-1) 1 :=
      ⟨by exact_mod_cast hdomain.1, by exact_mod_cast hdomain.2⟩
    rw [Real.arcsin_eq_arctan hdomainReal]
    apply containsReal_atanBounds
    apply (containsReal_some_iff _ _).2
    have hdiv := div_bounds_Icc (q : ℝ) q
      (sqrtPointBounds (1 - q ^ 2) precision).lo
      (sqrtPointBounds (1 - q ^ 2) precision).hi
      q (Real.sqrt (1 - (q : ℝ) ^ 2)) ⟨le_rfl, le_rfl⟩
      (by simpa using hsqrt) (Or.inr hrootReal)
    simpa [minOfFour, maxOfFour] using hdiv

/-- Successful arcsine bounds contain the image of every real member of the input interval. -/
theorem containsReal_asinBounds? {I K : Interval ℚ} {terms precision : Nat}
    (h : asinBounds? I terms precision = some K) {x : ℝ}
    (hx : I.ContainsReal some x) : K.ContainsReal some (Real.arcsin x) := by
  obtain ⟨hxlo, hxhi⟩ := (containsReal_some_iff _ _).1 hx
  unfold asinBounds? at h
  split at h
  · cases hlo : Internal.asinPointBounds? I.lo terms precision with
    | none => simp [hlo] at h
    | some lo =>
      simp only [hlo] at h
      have hloReal := (containsReal_some_iff _ _).1
        (Internal.containsReal_asinPointBounds? hlo)
      split at h
      · rename_i heq
        cases h
        have hpoint : x = (I.lo : ℝ) := le_antisymm (by simpa [heq] using hxhi) hxlo
        simpa [hpoint] using Internal.containsReal_asinPointBounds? hlo
      · cases hhi : Internal.asinPointBounds? I.hi terms precision with
        | none => simp [hhi] at h
        | some hi =>
          simp [hhi] at h
          subst K
          have hhiReal := (containsReal_some_iff _ _).1
            (Internal.containsReal_asinPointBounds? hhi)
          exact (containsReal_some_iff _ _).2
            ⟨hloReal.1.trans (Real.monotone_arcsin hxlo),
              (Real.monotone_arcsin hxhi).trans hhiReal.2⟩
  · simp at h

/-- Successful arccosine bounds contain the image of every real member of the input interval. -/
theorem containsReal_acosBounds? {I K : Interval ℚ} {terms precision : Nat}
    (h : acosBounds? I terms precision = some K) {x : ℝ}
    (hx : I.ContainsReal some x) : K.ContainsReal some (Real.arccos x) := by
  unfold acosBounds? at h
  split at h
  · rename_i hone
    cases h
    obtain ⟨hxlo, hxhi⟩ := (containsReal_some_iff _ _).1 hx
    have hxone : x = 1 :=
      le_antisymm (by simpa [hone.2] using hxhi) (by simpa [hone.1] using hxlo)
    simp [ContainsReal, Contains, point, hxone]
  · cases hsin : asinBounds? I terms precision with
    | none => simp [hsin] at h
    | some J =>
      simp [hsin] at h
      subst K
      have hJ := (containsReal_some_iff _ _).1 (containsReal_asinBounds? hsin hx)
      have hpi := Enclosure.contains_piQuarter terms
      apply (containsReal_some_iff _ _).2
      simp only [Rat.cast_max, Rat.cast_zero, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
      refine ⟨max_le (Real.arccos_nonneg x) ?_, ?_⟩ <;>
        rw [Real.arccos_eq_pi_div_two_sub_arcsin] <;> linarith [hpi.1, hpi.2]

end FloatLib.Numerics.Interval
