/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Trigonometric.Atan2.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Trigonometric.Atan2.Runtime

/-!
# Correct rounding of configured posit two-coordinate arctangent

The configured operations inherit the model's principal-branch rounding and exceptional-value
rules for every lawful storage carrier and valid posit width.
-/

public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Configured `arcTan2` refines the model operation. -/
@[simp] theorem toModel_arcTan2 (x y : Value) :
    toModel (arcTan2 x y) = Model.arcTan2 (toModel x) (toModel y) := by
  simp [arcTan2, toModel, Configured.Family.toModel]

/-- Configured `arcTan2` rounds the exact principal argument. -/
theorem arcTan2_eq_real (x y : Value) {a b : Rat}
    (hx : toRat? x = some a) (hy : toRat? y = some b) (horigin : ¬ (a = 0 ∧ b = 0)) :
    toModel (arcTan2 x y) = Model.RealRounding.round format (Complex.arg ⟨(a : ℝ), (b : ℝ)⟩) := by
  rw [toModel_arcTan2]
  exact Model.arcTan2_eq_real _ _ hx hy horigin

/-- Configured `arcTan2` propagates a NaR first coordinate. -/
theorem arcTan2_eq_nar_left (x y : Value) (hx : toModel x = Model.nar format) :
    toModel (arcTan2 x y) = Model.nar format := by simp [hx]

/-- Configured `arcTan2` propagates a NaR second coordinate. -/
theorem arcTan2_eq_nar_right (x y : Value) (hy : toModel y = Model.nar format) :
    toModel (arcTan2 x y) = Model.nar format := by simp [hy]

/-- Configured `arcTan2` rejects the origin. -/
theorem arcTan2_eq_nar_of_origin (x y : Value)
    (hx : toModel x = Model.zero format) (hy : toModel y = Model.zero format) :
    toModel (arcTan2 x y) = Model.nar format := by simp [hx, hy]

/-- Configured `arcTan2Pi` refines the model operation. -/
@[simp] theorem toModel_arcTan2Pi (x y : Value) :
    toModel (arcTan2Pi x y) = Model.arcTan2Pi (toModel x) (toModel y) := by
  simp [arcTan2Pi, toModel, Configured.Family.toModel]

/-- Configured `arcTan2Pi` rounds the exact principal argument divided by pi. -/
theorem arcTan2Pi_eq_real (x y : Value) {a b : Rat}
    (hx : toRat? x = some a) (hy : toRat? y = some b) (horigin : ¬ (a = 0 ∧ b = 0)) :
    toModel (arcTan2Pi x y) = Model.RealRounding.round format (Complex.arg ⟨(a : ℝ), (b : ℝ)⟩ / Real.pi) := by
  rw [toModel_arcTan2Pi]
  exact Model.arcTan2Pi_eq_real _ _ hx hy horigin

/-- Configured `arcTan2Pi` propagates a NaR first coordinate. -/
theorem arcTan2Pi_eq_nar_left (x y : Value) (hx : toModel x = Model.nar format) :
    toModel (arcTan2Pi x y) = Model.nar format := by simp [hx]

/-- Configured `arcTan2Pi` propagates a NaR second coordinate. -/
theorem arcTan2Pi_eq_nar_right (x y : Value) (hy : toModel y = Model.nar format) :
    toModel (arcTan2Pi x y) = Model.nar format := by simp [hy]

/-- Configured `arcTan2Pi` rejects the origin. -/
theorem arcTan2Pi_eq_nar_of_origin (x y : Value)
    (hx : toModel x = Model.zero format) (hy : toModel y = Model.zero format) :
    toModel (arcTan2Pi x y) = Model.nar format := by simp [hx, hy]

end ExecFloat.Posit
end FloatLib.Floats
