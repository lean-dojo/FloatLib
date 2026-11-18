/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Functions.Proof

/-!
# Real-domain cases for P3109 functions

P3109 interim report v4.1 (unapproved draft), §§4.10.9–4.10.12, 4.10.15–4.10.16.
These results identify the rational pole test and sign with the report's
real sine/cosine conditions, and record the logarithm and inverse-function
endpoints before destination saturation.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Functions

/-- The finite angle expression denotes a rational multiple of π or its pi-scaled coefficient. -/
theorem toReal_angle (piScaled : Bool) (multiple : Rat) :
    (angle piScaled multiple).toReal =
      if piScaled then (multiple : ℝ) else (multiple : ℝ) * Real.pi := by
  have hpoint : (⟨((-1 : Rat) : ℝ), ((0 : Rat) : ℝ)⟩ : ℂ) = -1 := by
    apply Complex.ext <;> simp
  cases piScaled with
  | false =>
      change (multiple : ℝ) *
        Complex.arg ⟨((-1 : Rat) : ℝ), ((0 : Rat) : ℝ)⟩ + (0 : Rat) =
          (multiple : ℝ) * Real.pi
      rw [hpoint, Complex.arg_neg_one]
      simp
  | true => rfl

/-- A half-integer angle has sine given exactly by the parity of its integer part. -/
theorem sinPi_of_fract_half (argument : Rat) (hpole : Int.fract argument = 1 / 2) :
    Real.sin ((argument : ℝ) * Real.pi) =
      (TrigonometricComparison.halfTurnSign (Int.floor argument) : ℝ) := by
  have hsplit : (argument : ℝ) = 1 / 2 + (Int.floor argument : ℝ) := by
    have h := congrArg (fun value : Rat => (value : ℝ)) (Int.fract_add_floor argument)
    rw [hpole] at h
    push_cast at h
    linarith
  rw [hsplit, add_mul, show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring,
    Real.sin_add_int_mul_pi, Real.sin_pi_div_two, mul_one,
    TrigonometricComparison.halfTurnSign_eq_zpow]
  push_cast
  rfl

/-- The executable tangent-pole branch has precisely the sine sign required by §4.10.12. -/
theorem finiteUnary_tanPi_of_cos_eq_zero (argument : Rat)
    (hpole : Real.cos ((argument : ℝ) * Real.pi) = 0) :
    finiteUnary .tanPi argument =
      .infinity (decide (Real.sin ((argument : ℝ) * Real.pi) < 0)) := by
  have hfract := (TrigonometricComparison.cosPi_eq_zero_iff argument).mp hpole
  rw [sinPi_of_fract_half argument hfract]
  simp only [finiteUnary, hfract, ite_true, TrigonometricComparison.halfTurnSign]
  by_cases heven : Int.floor argument % 2 = 0 <;> simp [heven]

/-- Away from the report's poles, pi-scaled tangent keeps its exact finite expression. -/
theorem finiteUnary_tanPi_of_cos_ne_zero (argument : Rat)
    (hpole : Real.cos ((argument : ℝ) * Real.pi) ≠ 0) :
    finiteUnary .tanPi argument = .finite (.tanPi argument) := by
  have hfract : Int.fract argument ≠ 1 / 2 :=
    fun h => hpole ((TrigonometricComparison.cosPi_eq_zero_iff argument).mpr h)
  dsimp only [finiteUnary]
  rw [ite_eq_right hfract]

/-- Both report logarithms send zero to negative infinity before saturation. -/
@[simp] theorem logarithm_zero (baseTwo : Bool) :
    logarithm baseTwo 0 = .infinity true := by
  simp [logarithm]

/-- Both report logarithms reject every strictly negative finite argument. -/
theorem logarithm_of_neg (baseTwo : Bool) (argument : Rat) (hnegative : argument < 0) :
    logarithm baseTwo argument = .exceptional (.nan) := by
  simp [logarithm, not_lt.mpr hnegative.le, ne_of_lt hnegative]

/-- The two inverse hyperbolic tangent endpoints yield their signed infinities. -/
theorem finiteUnary_arcTanh_endpoint (negative : Bool) :
    finiteUnary .arcTanh (if negative then -1 else 1) = .infinity negative := by
  cases negative <;> norm_num [finiteUnary]

/-- Every unary operation propagates the report's unique NaN. -/
@[simp] theorem unary_exceptional (operation : Unary) (category : ExceptionalValue) :
    unary operation (.exceptional category) = .exceptional (.nan) := rfl

/-- The origin is invalid in both two-coordinate inverse tangent variants. -/
@[simp] theorem arcTan2_origin (piScaled : Bool) :
    arcTan2 piScaled (.finite 0) (.finite 0) = .exceptional (.nan) := by
  simp [arcTan2]

/-- Every combination of two infinite coordinates is invalid in both report variants. -/
@[simp] theorem arcTan2_infinities (piScaled yNegative xNegative : Bool) :
    arcTan2 piScaled (.infinity yNegative) (.infinity xNegative) = .exceptional (.nan) := rfl

end FloatLib.Floats.Formats.P3109.Functions
