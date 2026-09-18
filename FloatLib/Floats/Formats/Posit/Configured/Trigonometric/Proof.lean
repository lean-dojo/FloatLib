/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Trigonometric.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Trigonometric.Runtime

/-!
# Correct rounding of configured posit trigonometric operations

The sine, cosine, tangent, and inverse-function theorems identify each configured result with
one rounding of the real function, under the stated domain conditions. NaR propagation and
out-of-domain results are proved separately. All results hold for every lawful storage codec
and every valid posit width.
-/

public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Configured sine refines the model operation. -/
@[simp] theorem toModel_sin (value : Value) :
    toModel (sin value) = Model.sin (toModel value) := by
  simp [sin, toModel, Configured.Family.toModel]

/-- Configured cosine refines the model operation. -/
@[simp] theorem toModel_cos (value : Value) :
    toModel (cos value) = Model.cos (toModel value) := by
  simp [cos, toModel, Configured.Family.toModel]

/-- Configured tangent refines the model operation. -/
@[simp] theorem toModel_tan (value : Value) :
    toModel (tan value) = Model.tan (toModel value) := by
  simp [tan, toModel, Configured.Family.toModel]

/-- Configured inverse sine refines the model operation. -/
@[simp] theorem toModel_arcSin (value : Value) :
    toModel (arcSin value) = Model.arcSin (toModel value) := by
  simp [arcSin, toModel, Configured.Family.toModel]

/-- Configured inverse cosine refines the model operation. -/
@[simp] theorem toModel_arcCos (value : Value) :
    toModel (arcCos value) = Model.arcCos (toModel value) := by
  simp [arcCos, toModel, Configured.Family.toModel]

/-- Configured inverse tangent refines the model operation. -/
@[simp] theorem toModel_arcTan (value : Value) :
    toModel (arcTan value) = Model.arcTan (toModel value) := by
  simp [arcTan, toModel, Configured.Family.toModel]

/-- Configured sine rounds the exact real result once. -/
theorem sin_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q) :
    toModel (sin value) = Model.RealRounding.round format (Real.sin (q : ℝ)) := by
  rw [toModel_sin]
  exact Model.sin_eq_real _ hvalue

/-- Configured cosine rounds the exact real result once. -/
theorem cos_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q) :
    toModel (cos value) = Model.RealRounding.round format (Real.cos (q : ℝ)) := by
  rw [toModel_cos]
  exact Model.cos_eq_real _ hvalue

/-- Configured tangent rounds the exact real result once. -/
theorem tan_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q) :
    toModel (tan value) = Model.RealRounding.round format (Real.tan (q : ℝ)) := by
  rw [toModel_tan]
  exact Model.tan_eq_real _ hvalue

/-- Configured inverse sine includes both real-domain endpoints. -/
theorem arcSin_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q)
    (hlower : -1 ≤ q) (hupper : q ≤ 1) :
    toModel (arcSin value) = Model.RealRounding.round format (Real.arcsin (q : ℝ)) := by
  rw [toModel_arcSin]
  exact Model.arcSin_eq_real _ hvalue hlower hupper

/-- Configured inverse cosine includes both real-domain endpoints. -/
theorem arcCos_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q)
    (hlower : -1 ≤ q) (hupper : q ≤ 1) :
    toModel (arcCos value) = Model.RealRounding.round format (Real.arccos (q : ℝ)) := by
  rw [toModel_arcCos]
  exact Model.arcCos_eq_real _ hvalue hlower hupper

/-- Configured inverse tangent rounds its exact principal value. -/
theorem arcTan_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q) :
    toModel (arcTan value) = Model.RealRounding.round format (Real.arctan (q : ℝ)) := by
  rw [toModel_arcTan]
  exact Model.arcTan_eq_real _ hvalue

/-- NaR propagates through configured sine. -/
theorem sin_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (sin value) = Model.nar format := by simp [hvalue]

/-- NaR propagates through configured cosine. -/
theorem cos_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (cos value) = Model.nar format := by simp [hvalue]

/-- NaR propagates through configured tangent. -/
theorem tan_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (tan value) = Model.nar format := by simp [hvalue]

/-- NaR propagates through configured inverse sine. -/
theorem arcSin_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (arcSin value) = Model.nar format := by simp [hvalue]

/-- NaR propagates through configured inverse cosine. -/
theorem arcCos_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (arcCos value) = Model.nar format := by simp [hvalue]

/-- NaR propagates through configured inverse tangent. -/
theorem arcTan_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (arcTan value) = Model.nar format := by simp [hvalue]

/-- Configured inverse sine rejects the exterior of its real domain. -/
theorem arcSin_eq_nar_of_outside (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (houtside : q < -1 ∨ 1 < q) :
    toModel (arcSin value) = Model.nar format := by
  rw [toModel_arcSin]
  exact Model.arcSin_eq_nar_of_outside _ hvalue houtside

/-- Configured inverse cosine rejects the exterior of its real domain. -/
theorem arcCos_eq_nar_of_outside (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (houtside : q < -1 ∨ 1 < q) :
    toModel (arcCos value) = Model.nar format := by
  rw [toModel_arcCos]
  exact Model.arcCos_eq_nar_of_outside _ hvalue houtside

end ExecFloat.Posit
end FloatLib.Floats
