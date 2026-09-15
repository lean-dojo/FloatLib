/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Trigonometric.Atan2.Runtime
public import FloatLib.Floats.Formats.Posit.Trigonometric.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Proof

/-!
# Real rounding and exceptional cases for posit two-coordinate arctangent

The operations round the exact principal complex argument, in radians or divided by pi,
including its value on the negative real axis. NaR and the origin are rejected before the
comparison search.
-/

public section

namespace FloatLib.Floats.Formats.Posit.Model

namespace Trigonometric

open FloatLib.Numerics.Enclosure.Comparison

/-- An exact two-coordinate comparator gives the standard rounding away from the origin. -/
theorem evaluateArgument_eq_real (prepare : Rat → Rat → Nat → Prepared)
    (function : ℝ → ℝ → ℝ)
    (hprepare : ∀ a b levels boundary,
      (prepare a b levels).compare boundary = cmp (function a b) (boundary : ℝ))
    {format : Format} (x y : Model format) {a b : Rat}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (horigin : ¬ (a = 0 ∧ b = 0)) :
    evaluateArgument prepare x y = RealRounding.round format (function a b) := by
  simp only [evaluateArgument, hx, hy, if_neg horigin]
  exact ComparisonRounding.roundSigned_eq_real format _ _ (hprepare a b _)

/-- A NaR first coordinate propagates. -/
@[simp] theorem evaluateArgument_nar_left (prepare : Rat → Rat → Nat → Prepared)
    {format : Format} (y : Model format) :
    evaluateArgument prepare (nar format) y = nar format := by
  simp [evaluateArgument]

/-- A NaR second coordinate propagates. -/
@[simp] theorem evaluateArgument_nar_right (prepare : Rat → Rat → Nat → Prepared)
    {format : Format} (x : Model format) :
    evaluateArgument prepare x (nar format) = nar format := by
  simp only [evaluateArgument, toRat?_nar]
  cases x.toRat? <;> rfl

/-- The origin is outside the posit operation's domain. -/
@[simp] theorem evaluateArgument_origin (prepare : Rat → Rat → Nat → Prepared)
    {format : Format} :
    evaluateArgument prepare (zero format) (zero format) = nar format := by
  simp [evaluateArgument]

end Trigonometric

open FloatLib.Numerics.TrigonometricComparison

variable {format : Format}

/-- Two-coordinate arctangent rounds the exact principal angle of `a + i*b`. -/
theorem arcTan2_eq_real (x y : Model format) {a b : Rat}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (horigin : ¬ (a = 0 ∧ b = 0)) :
    arcTan2 x y = RealRounding.round format (Complex.arg ⟨(a : ℝ), (b : ℝ)⟩) :=
  Trigonometric.evaluateArgument_eq_real prepareAtan2 (fun a b => Complex.arg ⟨a, b⟩)
    prepareAtan2_eq_real x y hx hy horigin

/-- Pi-scaled two-coordinate arctangent divides the exact angle before rounding. -/
theorem arcTan2Pi_eq_real (x y : Model format) {a b : Rat}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (horigin : ¬ (a = 0 ∧ b = 0)) :
    arcTan2Pi x y = RealRounding.round format (Complex.arg ⟨(a : ℝ), (b : ℝ)⟩ / Real.pi) :=
  Trigonometric.evaluateArgument_eq_real prepareAtan2Pi
    (fun a b => Complex.arg ⟨a, b⟩ / Real.pi) prepareAtan2Pi_eq_real x y hx hy horigin

/-- `arcTan2` propagates a NaR first coordinate. -/
@[simp] theorem arcTan2_nar_left (y : Model format) :
    arcTan2 (nar format) y = nar format := Trigonometric.evaluateArgument_nar_left _ _

/-- `arcTan2` propagates a NaR second coordinate. -/
@[simp] theorem arcTan2_nar_right (x : Model format) :
    arcTan2 x (nar format) = nar format := Trigonometric.evaluateArgument_nar_right _ _

/-- `arcTan2` rejects the origin. -/
@[simp] theorem arcTan2_origin : arcTan2 (zero format) (zero format) = nar format :=
  Trigonometric.evaluateArgument_origin _

/-- `arcTan2Pi` propagates a NaR first coordinate. -/
@[simp] theorem arcTan2Pi_nar_left (y : Model format) :
    arcTan2Pi (nar format) y = nar format := Trigonometric.evaluateArgument_nar_left _ _

/-- `arcTan2Pi` propagates a NaR second coordinate. -/
@[simp] theorem arcTan2Pi_nar_right (x : Model format) :
    arcTan2Pi x (nar format) = nar format := Trigonometric.evaluateArgument_nar_right _ _

/-- `arcTan2Pi` rejects the origin. -/
@[simp] theorem arcTan2Pi_origin : arcTan2Pi (zero format) (zero format) = nar format :=
  Trigonometric.evaluateArgument_origin _

end FloatLib.Floats.Formats.Posit.Model
