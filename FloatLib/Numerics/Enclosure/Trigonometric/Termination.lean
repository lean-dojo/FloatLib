/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.Tangent.Runtime
public import FloatLib.Numerics.Enclosure.Trigonometric.Reduction.Convergence
public import FloatLib.Numerics.Enclosure.Elementary.TrigonometricIrrational
public import FloatLib.Numerics.Enclosure.Comparison.Proof
public import FloatLib.Numerics.Enclosure.Rational.AffineConvergence

/-!
# Termination of ordinary trigonometric comparisons

At nonzero rational arguments, sine, cosine, and arctangent are irrational. Their converging
rational endpoints therefore exclude every rational boundary at some finite degree.
Tangent uses a linear residual: its nonvanishing follows from tangent's irrationality and
the absence of tangent poles at rational inputs. Exact zero-input values are handled by the
comparison runtime before refinement.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter
open scoped Topology

/-- Adaptive reduced sine enclosures eventually separate every rational boundary. -/
theorem exists_sin_separating (argument boundary : ℚ) (hnonzero : argument ≠ 0) :
    ∃ n, Comparison.Separates (sinReduced argument (2 ^ n)) boundary :=
  Comparison.exists_separating_of_irrational (irrational_sin_ratCast argument hnonzero) boundary
    ((tendsto_sinReduced_lo argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))
    ((tendsto_sinReduced_hi argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))

/-- Adaptive reduced cosine enclosures eventually separate every rational boundary. -/
theorem exists_cos_separating (argument boundary : ℚ) (hnonzero : argument ≠ 0) :
    ∃ n, Comparison.Separates (cosReduced argument (2 ^ n)) boundary :=
  Comparison.exists_separating_of_irrational (irrational_cos_ratCast argument hnonzero) boundary
    ((tendsto_cosReduced_lo argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))
    ((tendsto_cosReduced_hi argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))

/-- Adaptive arctangent enclosures eventually separate every rational boundary. -/
theorem exists_atan_separating (argument boundary : ℚ) (hnonzero : argument ≠ 0) :
    ∃ n, Comparison.Separates (atan argument (2 ^ n)) boundary :=
  Comparison.exists_separating_of_irrational (irrational_arctan_ratCast argument hnonzero) boundary
    ((tendsto_atan_lo argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))
    ((tendsto_atan_hi argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))

/-- The tangent residual enclosure contains its exact real linear combination. -/
theorem contains_sinSubCos (argument boundary : ℚ) (degree : Nat) :
    (sinSubCos argument boundary degree).Contains
      (Real.sin (argument : ℝ) - (boundary : ℝ) * Real.cos (argument : ℝ)) :=
  RationalInterval.contains_sub (contains_sinReduced argument degree)
    (RationalInterval.contains_scale (contains_cosReduced argument degree) boundary)

/-- The lower endpoints of the tangent residual converge to the exact residual. -/
theorem tendsto_sinSubCos_lo (argument boundary : ℚ) :
    Tendsto (fun n : Nat => ((sinSubCos argument boundary n).lo : ℝ)) atTop
      (𝓝 (Real.sin (argument : ℝ) - (boundary : ℝ) * Real.cos (argument : ℝ))) :=
  RationalInterval.tendsto_sub_lo (tendsto_sinReduced_lo argument)
    (RationalInterval.tendsto_scale_hi (tendsto_cosReduced_lo argument)
      (tendsto_cosReduced_hi argument) boundary)

/-- The upper endpoints of the tangent residual converge to the exact residual. -/
theorem tendsto_sinSubCos_hi (argument boundary : ℚ) :
    Tendsto (fun n : Nat => ((sinSubCos argument boundary n).hi : ℝ)) atTop
      (𝓝 (Real.sin (argument : ℝ) - (boundary : ℝ) * Real.cos (argument : ℝ))) :=
  RationalInterval.tendsto_sub_hi (tendsto_sinReduced_hi argument)
    (RationalInterval.tendsto_scale_lo (tendsto_cosReduced_lo argument)
      (tendsto_cosReduced_hi argument) boundary)

/-- A rational tangent boundary never makes the residual zero at a nonzero rational argument. -/
theorem sin_sub_rat_mul_cos_ne_zero (argument boundary : ℚ) (hnonzero : argument ≠ 0) :
    Real.sin (argument : ℝ) - (boundary : ℝ) * Real.cos (argument : ℝ) ≠ 0 := by
  intro hzero
  apply (irrational_tan_ratCast argument hnonzero).ne_rat boundary
  rw [Real.tan_eq_sin_div_cos]
  exact (div_eq_iff (cos_ratCast_ne_zero argument hnonzero)).mpr (sub_eq_zero.mp hzero)

/-- The tangent residual comparison terminates without constructing a quotient enclosure. -/
theorem exists_sinSubCos_separating (argument boundary : ℚ) (hnonzero : argument ≠ 0) :
    ∃ n, Comparison.Separates (sinSubCos argument boundary (2 ^ n)) 0 :=
  Comparison.exists_separating 0
    (by simpa using sin_sub_rat_mul_cos_ne_zero argument boundary hnonzero)
    ((tendsto_sinSubCos_lo argument boundary).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))
    ((tendsto_sinSubCos_hi argument boundary).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))

end FloatLib.Numerics.Enclosure
