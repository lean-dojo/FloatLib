/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Trigonometric.Pi.Runtime
public import FloatLib.Floats.Formats.Posit.Trigonometric.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Pi.Proof

/-!
# Real rounding and domains of pi-scaled posit functions

The exact rational classifiers and convergent comparison kernels determine the standard
rounding of the mathematical result. Tangent poles are excluded explicitly: Mathlib's
zero-valued totalization at a pole is not the posit operation's exceptional-value policy.
-/

public section

namespace FloatLib.Floats.Formats.Posit.Model

open FloatLib.Numerics.TrigonometricComparison

variable {format : Format}

/-- Pi-scaled sine rounds the exact product-angle expression once. -/
theorem sinPi_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q) :
    sinPi value = RealRounding.round format (Real.sin ((q : ℝ) * Real.pi)) :=
  Trigonometric.evaluate_eq_real prepareSinPi (fun x => Real.sin (x * Real.pi))
    prepareSinPi_eq_real value hvalue

/-- Pi-scaled cosine rounds the exact product-angle expression once. -/
theorem cosPi_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q) :
    cosPi value = RealRounding.round format (Real.cos ((q : ℝ) * Real.pi)) :=
  Trigonometric.evaluate_eq_real prepareCosPi (fun x => Real.cos (x * Real.pi))
    prepareCosPi_eq_real value hvalue

/-- Pi-scaled tangent has the required real rounding away from its exact half-integer poles. -/
theorem tanPi_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q)
    (hpole : Int.fract q ≠ 1 / 2) :
    tanPi value = RealRounding.round format (Real.tan ((q : ℝ) * Real.pi)) := by
  simp only [tanPi, hvalue, if_neg hpole]
  exact ComparisonRounding.roundSigned_eq_real format _ _ (prepareTanPi_eq_real q _)

/-- Every half-integer pi-scaled tangent input produces NaR. -/
theorem tanPi_eq_nar_of_pole (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hpole : Int.fract q = 1 / 2) :
    tanPi value = nar format := by
  simp [tanPi, hvalue, hpole]

/-- The inverse sine is divided by pi before its one rounding. -/
theorem arcSinPi_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q)
    (hlower : -1 ≤ q) (hupper : q ≤ 1) :
    arcSinPi value = RealRounding.round format (Real.arcsin (q : ℝ) / Real.pi) :=
  Trigonometric.evaluateUnit_eq_real prepareArcsinPi (fun x => Real.arcsin x / Real.pi)
    prepareArcsinPi_eq_real value hvalue hlower hupper

/-- The inverse cosine is divided by pi before its one rounding. -/
theorem arcCosPi_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q)
    (hlower : -1 ≤ q) (hupper : q ≤ 1) :
    arcCosPi value = RealRounding.round format (Real.arccos (q : ℝ) / Real.pi) :=
  Trigonometric.evaluateUnit_eq_real prepareArccosPi (fun x => Real.arccos x / Real.pi)
    prepareArccosPi_eq_real value hvalue hlower hupper

/-- The inverse tangent is divided by pi before its one rounding. -/
theorem arcTanPi_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q) :
    arcTanPi value = RealRounding.round format (Real.arctan (q : ℝ) / Real.pi) :=
  Trigonometric.evaluate_eq_real prepareArctanPi (fun x => Real.arctan x / Real.pi)
    prepareArctanPi_eq_real value hvalue

/-- NaR propagates through `sinPi`. -/
@[simp] theorem sinPi_nar : sinPi (nar format) = nar format :=
  Trigonometric.evaluate_nar _

/-- NaR propagates through `cosPi`. -/
@[simp] theorem cosPi_nar : cosPi (nar format) = nar format :=
  Trigonometric.evaluate_nar _

/-- NaR propagates through `arcSinPi`. -/
@[simp] theorem arcSinPi_nar : arcSinPi (nar format) = nar format :=
  Trigonometric.evaluateUnit_nar _

/-- NaR propagates through `arcCosPi`. -/
@[simp] theorem arcCosPi_nar : arcCosPi (nar format) = nar format :=
  Trigonometric.evaluateUnit_nar _

/-- NaR propagates through `arcTanPi`. -/
@[simp] theorem arcTanPi_nar : arcTanPi (nar format) = nar format :=
  Trigonometric.evaluate_nar _

/-- NaR propagates through pi-scaled tangent. -/
@[simp] theorem tanPi_nar : tanPi (nar format) = nar format := by simp [tanPi]

/-- `arcSinPi` rejects finite inputs outside its real domain. -/
theorem arcSinPi_eq_nar_of_outside (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (houtside : q < -1 ∨ 1 < q) :
    arcSinPi value = nar format :=
  Trigonometric.evaluateUnit_eq_nar _ value hvalue houtside

/-- `arcCosPi` rejects finite inputs outside its real domain. -/
theorem arcCosPi_eq_nar_of_outside (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (houtside : q < -1 ∨ 1 < q) :
    arcCosPi value = nar format :=
  Trigonometric.evaluateUnit_eq_nar _ value hvalue houtside

end FloatLib.Floats.Formats.Posit.Model
