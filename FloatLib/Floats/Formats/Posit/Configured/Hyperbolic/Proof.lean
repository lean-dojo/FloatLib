/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Hyperbolic.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Hyperbolic.Runtime

/-!
# Correct rounding of configured posit hyperbolic functions

Refinement holds for every lawful codec. The real-rounding and exceptional-domain theorems
therefore apply to every configured width and carrier.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Configured hyperbolic tangent refines the model operation. -/
@[simp] theorem toModel_tanH (value : Value) :
    toModel (tanH value) = Model.tanH (toModel value) := by
  simp [tanH, toModel, Configured.Family.toModel]

/-- Configured inverse hyperbolic tangent refines the model operation. -/
@[simp] theorem toModel_arcTanH (value : Value) :
    toModel (arcTanH value) = Model.arcTanH (toModel value) := by
  simp [arcTanH, toModel, Configured.Family.toModel]

/-- Finite configured hyperbolic tangent rounds its exact real value once. -/
theorem tanH_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q) :
    toModel (tanH value) = Model.RealRounding.round format (Real.tanh (q : ℝ)) := by
  rw [toModel_tanH]
  exact Model.tanH_eq_real _ hvalue

/-- Configured inverse hyperbolic tangent rounds its exact value on the open real domain. -/
theorem arcTanH_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q)
    (hlower : -1 < q) (hupper : q < 1) :
    toModel (arcTanH value) = Model.RealRounding.round format (Real.artanh (q : ℝ)) := by
  rw [toModel_arcTanH]
  exact Model.arcTanH_eq_real _ hvalue hlower hupper

/-- NaR inputs propagate through configured hyperbolic tangent. -/
theorem tanH_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (tanH value) = Model.nar format := by
  simp [hvalue]

/-- NaR inputs propagate through configured inverse hyperbolic tangent. -/
theorem arcTanH_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (arcTanH value) = Model.nar format := by
  simp [hvalue]

/-- The configured inverse hyperbolic tangent rejects both endpoints and the exterior. -/
theorem arcTanH_eq_nar_of_outside (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (houtside : q ≤ -1 ∨ 1 ≤ q) :
    toModel (arcTanH value) = Model.nar format := by
  rw [toModel_arcTanH]
  exact Model.arcTanH_eq_nar_of_outside _ hvalue houtside

/-- Configured hyperbolic sine refines the model operation. -/
@[simp] theorem toModel_sinH (value : Value) :
    toModel (sinH value) = Model.sinH (toModel value) := by
  simp [sinH, toModel, Configured.Family.toModel]

/-- Configured hyperbolic sine rounds its exact real value on its real domain. -/
theorem sinH_eq_real (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) :
    toModel (sinH value) = Model.RealRounding.round format (Real.sinh (q : ℝ)) := by
  rw [toModel_sinH]
  exact Model.sinH_eq_real _ hvalue

/-- NaR inputs propagate through configured hyperbolic sine. -/
theorem sinH_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (sinH value) = Model.nar format := by
  simp [hvalue]

/-- Configured hyperbolic cosine refines the model operation. -/
@[simp] theorem toModel_cosH (value : Value) :
    toModel (cosH value) = Model.cosH (toModel value) := by
  simp [cosH, toModel, Configured.Family.toModel]

/-- Configured hyperbolic cosine rounds its exact real value on its real domain. -/
theorem cosH_eq_real (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) :
    toModel (cosH value) = Model.RealRounding.round format (Real.cosh (q : ℝ)) := by
  rw [toModel_cosH]
  exact Model.cosH_eq_real _ hvalue

/-- NaR inputs propagate through configured hyperbolic cosine. -/
theorem cosH_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (cosH value) = Model.nar format := by
  simp [hvalue]

/-- Configured inverse hyperbolic sine refines the model operation. -/
@[simp] theorem toModel_arcSinH (value : Value) :
    toModel (arcSinH value) = Model.arcSinH (toModel value) := by
  simp [arcSinH, toModel, Configured.Family.toModel]

/-- Configured inverse hyperbolic sine rounds its exact real value on its real domain. -/
theorem arcSinH_eq_real (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) :
    toModel (arcSinH value) = Model.RealRounding.round format (Real.arsinh (q : ℝ)) := by
  rw [toModel_arcSinH]
  exact Model.arcSinH_eq_real _ hvalue

/-- NaR inputs propagate through configured inverse hyperbolic sine. -/
theorem arcSinH_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (arcSinH value) = Model.nar format := by
  simp [hvalue]

/-- Configured inverse hyperbolic cosine refines the model operation. -/
@[simp] theorem toModel_arcCosH (value : Value) :
    toModel (arcCosH value) = Model.arcCosH (toModel value) := by
  simp [arcCosH, toModel, Configured.Family.toModel]

/-- Configured inverse hyperbolic cosine rounds its exact real value on its real domain. -/
theorem arcCosH_eq_real (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (hdomain : 1 ≤ q) :
    toModel (arcCosH value) = Model.RealRounding.round format (Real.arcosh (q : ℝ)) := by
  rw [toModel_arcCosH]
  exact Model.arcCosH_eq_real _ hvalue hdomain

/-- NaR inputs propagate through configured inverse hyperbolic cosine. -/
theorem arcCosH_eq_nar (value : Value) (hvalue : toModel value = Model.nar format) :
    toModel (arcCosH value) = Model.nar format := by
  simp [hvalue]

/-- Configured inverse hyperbolic cosine rejects finite inputs below one. -/
theorem arcCosH_eq_nar_of_lt_one (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (houtside : q < 1) :
    toModel (arcCosH value) = Model.nar format := by
  rw [toModel_arcCosH]
  exact Model.arcCosH_eq_nar_of_lt_one _ hvalue houtside

end ExecFloat.Posit
end FloatLib.Floats
