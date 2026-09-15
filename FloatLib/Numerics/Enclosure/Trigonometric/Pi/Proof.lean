/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.Pi.Runtime
public import FloatLib.Numerics.Enclosure.Trigonometric.Reduction.Proof

/-!
# Containment after exact rational angle reduction

Removing an integer number of full turns preserves sine and cosine exactly. Their global
Lipschitz bounds control the remaining uncertainty in pi, and the usual Taylor remainder
then gives a real containment theorem at every degree.
-/

public section

namespace FloatLib.Numerics.Enclosure

/-- Exact angle reduction bounds the remaining pi-scaled angle by one. -/
theorem abs_piReduced_le (argument : ℚ) : |piReduced argument| ≤ 1 := by
  have hlo := Int.floor_le (argument / 2 + 1 / 2)
  have hhi := Int.lt_floor_add_one (argument / 2 + 1 / 2)
  rw [abs_le]
  dsimp [piReduced, piTurns]
  constructor <;> linarith

/-- The Taylor argument is bounded by four independently of the unreduced input. -/
theorem abs_piArgument_le (argument : ℚ) (degree : Nat) :
    |piArgument argument degree| ≤ 4 := by
  have hq := half_le_trigQuarter degree
  have hqhi := trigQuarter_le_one degree
  rw [piArgument, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 4),
    abs_of_nonneg (by linarith : 0 ≤ trigQuarter degree)]
  nlinarith [abs_piReduced_le argument, abs_nonneg (piReduced argument)]

/-- Exact removal of full turns preserves sine. -/
theorem sin_piReduced (argument : ℚ) :
    Real.sin ((piReduced argument : ℚ) * Real.pi) =
      Real.sin ((argument : ℝ) * Real.pi) := by
  have hangle : ((piReduced argument : ℚ) : ℝ) * Real.pi =
      (argument : ℝ) * Real.pi - (piTurns argument : ℝ) * (2 * Real.pi) := by
    push_cast [piReduced]
    ring
  rw [hangle, Real.sin_sub_int_mul_two_pi]

/-- Exact removal of full turns preserves cosine. -/
theorem cos_piReduced (argument : ℚ) :
    Real.cos ((piReduced argument : ℚ) * Real.pi) =
      Real.cos ((argument : ℝ) * Real.pi) := by
  have hangle : ((piReduced argument : ℚ) : ℝ) * Real.pi =
      (argument : ℝ) * Real.pi - (piTurns argument : ℝ) * (2 * Real.pi) := by
    push_cast [piReduced]
    ring
  rw [hangle, Real.cos_sub_int_mul_two_pi]

/-- The rational approximation error bounds distance from the exact reduced angle. -/
theorem abs_piArgument_sub_le (argument : ℚ) (degree : Nat) :
    |(piArgument argument degree : ℝ) - (piReduced argument : ℚ) * Real.pi| ≤
      (piArgumentError argument degree : ℝ) := by
  have hlo := trigQuarter_le_pi_quarter degree
  have hhi := (contains_piQuarter degree).2
  have hid : (piArgument argument degree : ℝ) - (piReduced argument : ℚ) * Real.pi =
      -(4 * (piReduced argument : ℚ) * (Real.pi / 4 - (trigQuarter degree : ℝ))) := by
    push_cast [piArgument]
    ring
  rw [hid, abs_neg, abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hlo)]
  push_cast [piArgumentError]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hhi _)
    (mul_nonneg (by norm_num) (abs_nonneg _))

/-- The argument uncertainty transfers through sine by its global Lipschitz bound. -/
theorem abs_sinPi_sub_sinArgument_le (argument : ℚ) (degree : Nat) :
    |Real.sin ((argument : ℝ) * Real.pi) - Real.sin (piArgument argument degree : ℝ)| ≤
      (piArgumentError argument degree : ℝ) := by
  have h := Real.abs_sin_sub_sin_le (piArgument argument degree : ℝ)
    ((piReduced argument : ℚ) * Real.pi)
  rw [sin_piReduced, abs_sub_comm] at h
  exact h.trans (abs_piArgument_sub_le argument degree)

/-- The argument uncertainty transfers through cosine by its global Lipschitz bound. -/
theorem abs_cosPi_sub_cosArgument_le (argument : ℚ) (degree : Nat) :
    |Real.cos ((argument : ℝ) * Real.pi) - Real.cos (piArgument argument degree : ℝ)| ≤
      (piArgumentError argument degree : ℝ) := by
  have h := Real.abs_cos_sub_cos_le (piArgument argument degree : ℝ)
    ((piReduced argument : ℚ) * Real.pi)
  rw [cos_piReduced, abs_sub_comm] at h
  exact h.trans (abs_piArgument_sub_le argument degree)

/-- Taylor and argument errors together bound the pi-scaled sine polynomial. -/
theorem abs_sinPi_sub_taylor_le (argument : ℚ) (degree : Nat) :
    |Real.sin ((argument : ℝ) * Real.pi) -
      (sinTaylor (piArgument argument degree) degree : ℝ)| ≤ (piRadius argument degree : ℝ) := by
  calc
    _ ≤ |Real.sin ((argument : ℝ) * Real.pi) - Real.sin (piArgument argument degree : ℝ)| +
        |Real.sin (piArgument argument degree : ℝ) -
          (sinTaylor (piArgument argument degree) degree : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := by
      have h₁ := abs_sinPi_sub_sinArgument_le argument degree
      have h₂ := abs_sin_sub_sinTaylor_le (piArgument argument degree) degree
      push_cast [piRadius]
      linarith

/-- Taylor and argument errors together bound the pi-scaled cosine polynomial. -/
theorem abs_cosPi_sub_taylor_le (argument : ℚ) (degree : Nat) :
    |Real.cos ((argument : ℝ) * Real.pi) -
      (cosTaylor (piArgument argument degree) degree : ℝ)| ≤ (piRadius argument degree : ℝ) := by
  calc
    _ ≤ |Real.cos ((argument : ℝ) * Real.pi) - Real.cos (piArgument argument degree : ℝ)| +
        |Real.cos (piArgument argument degree : ℝ) -
          (cosTaylor (piArgument argument degree) degree : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := by
      have h₁ := abs_cosPi_sub_cosArgument_le argument degree
      have h₂ := abs_cos_sub_cosTaylor_le (piArgument argument degree) degree
      push_cast [piRadius]
      linarith

/-- Every sine enclosure contains the exact value, including rational-angle special values. -/
theorem contains_sinPi (argument : ℚ) (degree : Nat) :
    (sinPi argument degree).Contains (Real.sin ((argument : ℝ) * Real.pi)) :=
  contains_restrictUnit (RationalInterval.contains_around (abs_sinPi_sub_taylor_le argument degree))
    (Real.abs_sin_le_one _)

/-- Every cosine enclosure contains the exact value. -/
theorem contains_cosPi (argument : ℚ) (degree : Nat) :
    (cosPi argument degree).Contains (Real.cos ((argument : ℝ) * Real.pi)) :=
  contains_restrictUnit (RationalInterval.contains_around (abs_cosPi_sub_taylor_le argument degree))
    (Real.abs_cos_le_one _)

end FloatLib.Numerics.Enclosure
