/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.Pi.Convergence
public import FloatLib.Numerics.Exact.Trigonometric.PiValues.TangentClassify
public import FloatLib.Numerics.Enclosure.Comparison.Proof
public import FloatLib.Numerics.Enclosure.Rational.AffineConvergence

/-!
# Terminating comparisons at rational multiples of pi

The exact-value classifiers remove all rational answers before refinement. Their completeness
and endpoint convergence then separate every rational boundary. Tangent additionally excludes
half-integer poles and compares a linear sine/cosine residual without dividing intervals.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter TrigonometricComparison
open scoped Topology

/-- An unclassified pi-scaled sine eventually separates every rational boundary. -/
theorem exists_sinPi_separating (argument boundary : ℚ)
    (hnone : sinPiExact argument = none) :
    ∃ n, Comparison.Separates (sinPi argument (2 ^ n)) boundary :=
  Comparison.exists_separating_of_irrational
    (irrational_sinPi_of_exact_none argument hnone) boundary
    ((tendsto_sinPi_lo argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))
    ((tendsto_sinPi_hi argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))

/-- An unclassified pi-scaled cosine eventually separates every rational boundary. -/
theorem exists_cosPi_separating (argument boundary : ℚ)
    (hnone : cosPiExact argument = none) :
    ∃ n, Comparison.Separates (cosPi argument (2 ^ n)) boundary :=
  Comparison.exists_separating_of_irrational
    (irrational_cosPi_of_exact_none argument hnone) boundary
    ((tendsto_cosPi_lo argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))
    ((tendsto_cosPi_hi argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))

/-- The tangent residual enclosure contains its exact real linear combination. -/
theorem contains_sinPiSubCos (argument boundary : ℚ) (degree : Nat) :
    (sinPiSubCos argument boundary degree).Contains
      (Real.sin ((argument : ℝ) * Real.pi) -
        (boundary : ℝ) * Real.cos ((argument : ℝ) * Real.pi)) :=
  RationalInterval.contains_sub (contains_sinPi argument degree)
    (RationalInterval.contains_scale (contains_cosPi argument degree) boundary)

/-- The lower endpoints of the tangent residual converge to the exact residual. -/
theorem tendsto_sinPiSubCos_lo (argument boundary : ℚ) :
    Tendsto (fun n : Nat => ((sinPiSubCos argument boundary n).lo : ℝ)) atTop
      (𝓝 (Real.sin ((argument : ℝ) * Real.pi) -
        (boundary : ℝ) * Real.cos ((argument : ℝ) * Real.pi))) :=
  RationalInterval.tendsto_sub_lo (tendsto_sinPi_lo argument)
    (RationalInterval.tendsto_scale_hi (tendsto_cosPi_lo argument)
      (tendsto_cosPi_hi argument) boundary)

/-- The upper endpoints of the tangent residual converge to the exact residual. -/
theorem tendsto_sinPiSubCos_hi (argument boundary : ℚ) :
    Tendsto (fun n : Nat => ((sinPiSubCos argument boundary n).hi : ℝ)) atTop
      (𝓝 (Real.sin ((argument : ℝ) * Real.pi) -
        (boundary : ℝ) * Real.cos ((argument : ℝ) * Real.pi))) :=
  RationalInterval.tendsto_sub_hi (tendsto_sinPi_hi argument)
    (RationalInterval.tendsto_scale_lo (tendsto_cosPi_lo argument)
      (tendsto_cosPi_hi argument) boundary)

/-- Outside exact tangent values and poles, no rational boundary makes the residual vanish. -/
theorem sinPi_sub_rat_mul_cosPi_ne_zero (argument boundary : ℚ)
    (hpole : Int.fract argument ≠ 1 / 2) (hnone : tanPiExact argument = none) :
    Real.sin ((argument : ℝ) * Real.pi) -
      (boundary : ℝ) * Real.cos ((argument : ℝ) * Real.pi) ≠ 0 := by
  intro hzero
  apply (irrational_tanPi_of_exact_none argument hpole hnone).ne_rat boundary
  rw [Real.tan_eq_sin_div_cos]
  exact (div_eq_iff ((cosPi_eq_zero_iff argument).not.mpr hpole)).mpr (sub_eq_zero.mp hzero)

/-- The pi-scaled tangent residual search terminates away from exact values and poles. -/
theorem exists_sinPiSubCos_separating (argument boundary : ℚ)
    (hpole : Int.fract argument ≠ 1 / 2) (hnone : tanPiExact argument = none) :
    ∃ n, Comparison.Separates (sinPiSubCos argument boundary (2 ^ n)) 0 :=
  Comparison.exists_separating 0
    (by simpa using sinPi_sub_rat_mul_cosPi_ne_zero argument boundary hpole hnone)
    ((tendsto_sinPiSubCos_lo argument boundary).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))
    ((tendsto_sinPiSubCos_hi argument boundary).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))

end FloatLib.Numerics.Enclosure
