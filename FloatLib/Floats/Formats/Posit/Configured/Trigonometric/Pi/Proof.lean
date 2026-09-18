/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Trigonometric.Pi.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Trigonometric.Pi.Runtime

/-!
# Correct rounding of configured posit pi-scaled trigonometric operations

The configured pi-scaled operations inherit the model's real-rounding theorems through any
lawful storage codec. Separate equations cover NaR inputs, inverse-function domain failures,
and the half-integer poles of `tanPi`.
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
@[simp] theorem toModel_sinPi (value : Value) :
    toModel (sinPi value) = Model.sinPi (toModel value) := by
  simp [sinPi, toModel, Configured.Family.toModel]

/-- Configured cosine refines the model operation. -/
@[simp] theorem toModel_cosPi (value : Value) :
    toModel (cosPi value) = Model.cosPi (toModel value) := by
  simp [cosPi, toModel, Configured.Family.toModel]

/-- Configured tangent refines the model operation. -/
@[simp] theorem toModel_tanPi (value : Value) :
    toModel (tanPi value) = Model.tanPi (toModel value) := by
  simp [tanPi, toModel, Configured.Family.toModel]

/-- Configured inverse sine refines the model operation. -/
@[simp] theorem toModel_arcSinPi (value : Value) :
    toModel (arcSinPi value) = Model.arcSinPi (toModel value) := by
  simp [arcSinPi, toModel, Configured.Family.toModel]

/-- Configured inverse cosine refines the model operation. -/
@[simp] theorem toModel_arcCosPi (value : Value) :
    toModel (arcCosPi value) = Model.arcCosPi (toModel value) := by
  simp [arcCosPi, toModel, Configured.Family.toModel]

/-- Configured inverse tangent refines the model operation. -/
@[simp] theorem toModel_arcTanPi (value : Value) :
    toModel (arcTanPi value) = Model.arcTanPi (toModel value) := by
  simp [arcTanPi, toModel, Configured.Family.toModel]

/-- Configured sine rounds the exact real result once. -/
theorem sinPi_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q) :
    toModel (sinPi value) = Model.RealRounding.round format (Real.sin ((q : ℝ) * Real.pi)) := by
  rw [toModel_sinPi]
  exact Model.sinPi_eq_real _ hvalue

/-- Configured cosine rounds the exact real result once. -/
theorem cosPi_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q) :
    toModel (cosPi value) = Model.RealRounding.round format (Real.cos ((q : ℝ) * Real.pi)) := by
  rw [toModel_cosPi]
  exact Model.cosPi_eq_real _ hvalue

/-- Configured tangent rounds the exact real result once. -/
theorem tanPi_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q)
    (hpole : Int.fract q ≠ 1 / 2) :
    toModel (tanPi value) = Model.RealRounding.round format (Real.tan ((q : ℝ) * Real.pi)) := by
  rw [toModel_tanPi]
  exact Model.tanPi_eq_real _ hvalue hpole

/-- Configured inverse sine includes both real-domain endpoints. -/
theorem arcSinPi_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q)
    (hlower : -1 ≤ q) (hupper : q ≤ 1) :
    toModel (arcSinPi value) = Model.RealRounding.round format (Real.arcsin (q : ℝ) / Real.pi) := by
  rw [toModel_arcSinPi]
  exact Model.arcSinPi_eq_real _ hvalue hlower hupper

/-- Configured inverse cosine includes both real-domain endpoints. -/
theorem arcCosPi_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q)
    (hlower : -1 ≤ q) (hupper : q ≤ 1) :
    toModel (arcCosPi value) = Model.RealRounding.round format (Real.arccos (q : ℝ) / Real.pi) := by
  rw [toModel_arcCosPi]
  exact Model.arcCosPi_eq_real _ hvalue hlower hupper

/-- Configured inverse tangent rounds its exact principal value. -/
theorem arcTanPi_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q) :
    toModel (arcTanPi value) = Model.RealRounding.round format (Real.arctan (q : ℝ) / Real.pi) := by
  rw [toModel_arcTanPi]
  exact Model.arcTanPi_eq_real _ hvalue

/-- NaR propagates through configured sine. -/
theorem sinPi_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (sinPi value) = Model.nar format := by simp [hvalue]

/-- NaR propagates through configured cosine. -/
theorem cosPi_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (cosPi value) = Model.nar format := by simp [hvalue]

/-- NaR propagates through configured tangent. -/
theorem tanPi_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (tanPi value) = Model.nar format := by simp [hvalue]

/-- NaR propagates through configured inverse sine. -/
theorem arcSinPi_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (arcSinPi value) = Model.nar format := by simp [hvalue]

/-- NaR propagates through configured inverse cosine. -/
theorem arcCosPi_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (arcCosPi value) = Model.nar format := by simp [hvalue]

/-- NaR propagates through configured inverse tangent. -/
theorem arcTanPi_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (arcTanPi value) = Model.nar format := by simp [hvalue]

/-- Configured inverse sine rejects the exterior of its real domain. -/
theorem arcSinPi_eq_nar_of_outside (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (houtside : q < -1 ∨ 1 < q) :
    toModel (arcSinPi value) = Model.nar format := by
  rw [toModel_arcSinPi]
  exact Model.arcSinPi_eq_nar_of_outside _ hvalue houtside

/-- Configured inverse cosine rejects the exterior of its real domain. -/
theorem arcCosPi_eq_nar_of_outside (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (houtside : q < -1 ∨ 1 < q) :
    toModel (arcCosPi value) = Model.nar format := by
  rw [toModel_arcCosPi]
  exact Model.arcCosPi_eq_nar_of_outside _ hvalue houtside

/-- Configured pi-scaled tangent rejects every half-integer pole. -/
theorem tanPi_eq_nar_of_pole (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (hpole : Int.fract q = 1 / 2) :
    toModel (tanPi value) = Model.nar format := by
  rw [toModel_tanPi]
  exact Model.tanPi_eq_nar_of_pole _ hvalue hpole

end ExecFloat.Posit
end FloatLib.Floats
