/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Algebraic.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof

/-!
# Single-rounding semantics of posit algebraic functions

The finite-input theorems identify the exact expression before rounding, including irrational
square roots. Exceptional-input theorems give the NaR rules from the Posit Standard (2022), §5.1.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/-- A positive finite reciprocal square root is the once-rounded reciprocal of the real root. -/
theorem rSqrt_eq_roundPositive (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : 0 < q) :
    rSqrt value =
      RealRounding.roundPositive format (1 / Real.sqrt (q : ℝ)) := by
  simp only [rSqrt, hvalue, if_neg (not_le.mpr hq)]
  rw [roundSqrtRat_eq_roundPositive format q⁻¹ (inv_nonneg.mpr hq.le)]
  simp [Real.sqrt_inv, one_div]

/-- Nonpositive finite inputs lie outside the real domain of reciprocal square root. -/
theorem rSqrt_eq_nar_of_nonpositive (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : q ≤ 0) :
    rSqrt value = nar format := by
  simp [rSqrt, hvalue, hq]

/-- Reciprocal square root propagates NaR. -/
@[simp] theorem rSqrt_nar : rSqrt (nar format) = nar format := by
  simp [rSqrt]

/-- Reciprocal square root of zero is NaR. -/
@[simp] theorem rSqrt_zero : rSqrt (zero format) = nar format := by
  simp [rSqrt]

/-- Finite hypotenuse inputs give the standard rounding of the exact Euclidean norm. -/
theorem hypot_eq_roundPositive (left right : Model format) {a b : Rat}
    (hleft : left.toRat? = some a) (hright : right.toRat? = some b) :
    hypot left right =
      RealRounding.roundPositive format (Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2)) := by
  simp only [hypot, hleft, hright]
  rw [roundSqrtRat_eq_roundPositive format _
    (add_nonneg (mul_self_nonneg a) (mul_self_nonneg b))]
  simp [pow_two]

/-- A NaR first argument makes the hypotenuse NaR. -/
@[simp] theorem hypot_nar_left (right : Model format) :
    hypot (nar format) right = nar format := by
  simp [hypot]

/-- A NaR second argument makes the hypotenuse NaR. -/
@[simp] theorem hypot_nar_right (left : Model format) :
    hypot left (nar format) = nar format := by
  cases hleft : left.toRat? <;> simp [hypot, hleft]

/-- The norm of the zero pair is zero. -/
@[simp] theorem hypot_zero_zero : hypot (zero format) (zero format) = zero format := by
  simp only [hypot, toRat?_zero]
  simp [roundSqrtRat, roundSqrtCode]
  rfl

/-- Hypotenuse does not depend on the order of its inputs. -/
theorem hypot_comm (left right : Model format) : hypot left right = hypot right left := by
  cases hleft : left.toRat? <;> cases hright : right.toRat? <;>
    simp [hypot, hleft, hright, add_comm]

/-- Finite fused triple multiplication rounds the exact three-factor rational product once. -/
theorem fMM_eq_roundRat (left right third : Model format) {a b c : Rat}
    (hleft : left.toRat? = some a) (hright : right.toRat? = some b)
    (hthird : third.toRat? = some c) :
    fMM left right third = roundRat format (a * b * c) := by
  simp [fMM, hleft, hright, hthird]

/-- A NaR first factor propagates through fused triple multiplication, even beside zero. -/
@[simp] theorem fMM_nar_left (right third : Model format) :
    fMM (nar format) right third = nar format := by
  simp [fMM]

/-- A NaR second factor propagates through fused triple multiplication. -/
@[simp] theorem fMM_nar_right (left third : Model format) :
    fMM left (nar format) third = nar format := by
  cases hleft : left.toRat? <;> simp [fMM, hleft]

/-- A NaR third factor propagates through fused triple multiplication. -/
@[simp] theorem fMM_nar_third (left right : Model format) :
    fMM left right (nar format) = nar format := by
  cases hleft : left.toRat? <;> cases hright : right.toRat? <;> simp [fMM, hleft, hright]

/-- Swapping the first two factors preserves the once-rounded triple product. -/
theorem fMM_swap_left (left right third : Model format) :
    fMM left right third = fMM right left third := by
  cases hleft : left.toRat? <;> cases hright : right.toRat? <;>
    cases hthird : third.toRat? <;> simp [fMM, hleft, hright, hthird, mul_comm]

/-- Swapping the last two factors preserves the once-rounded triple product. -/
theorem fMM_swap_right (left right third : Model format) :
    fMM left right third = fMM left third right := by
  cases hleft : left.toRat? <;> cases hright : right.toRat? <;>
    cases hthird : third.toRat? <;> simp [fMM, hleft, hright, hthird, mul_right_comm]

end FloatLib.Floats.Formats.Posit.Model
