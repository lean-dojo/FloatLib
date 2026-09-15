/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Hyperbolic.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof
public import FloatLib.Numerics.Exact.Hyperbolic.Proof

/-!
# Real rounding and domains of posit hyperbolic functions

Finite inputs in the real domain round the mathematical function once, using the standard
posit saturation and appended-bit tie rule. Invalid inputs and NaR are covered separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

namespace Hyperbolic

open FloatLib.Numerics.HyperbolicComparison

/-- Rational hyperbolic tangent rounds its exact real value. -/
theorem tanhRat_eq_real (format : Format) (argument : Rat) :
    tanhRat format argument = RealRounding.round format (Real.tanh (argument : ℝ)) :=
  ComparisonRounding.roundSigned_eq_real format _ _ (compareTanh_eq_real argument)

/-- Rational inverse hyperbolic tangent rounds its exact value on the open real domain. -/
theorem artanhRat_eq_real (format : Format) (argument : Rat)
    (hlower : -1 < argument) (hupper : argument < 1) :
    artanhRat format argument = RealRounding.round format (Real.artanh (argument : ℝ)) := by
  rw [artanhRat, dif_pos hlower, dif_pos hupper]
  exact ComparisonRounding.roundSigned_eq_real format _ _
    (prepareArtanh_eq_real argument _ hlower hupper)

/-- Inverse hyperbolic tangent rejects the endpoints and exterior of its real domain. -/
theorem artanhRat_eq_nar (format : Format) (argument : Rat)
    (houtside : argument ≤ -1 ∨ 1 ≤ argument) :
    artanhRat format argument = nar format := by
  rcases houtside with h | h
  · simp [artanhRat, not_lt_of_ge h]
  · simp [artanhRat, not_lt_of_ge h]

/-- Rational operation lifting propagates NaR independently of the operation. -/
@[simp] theorem applyRat_nar {format : Format} (operation : Rat → Model format) :
    applyRat operation (nar format) = nar format := by
  simp [applyRat]

/-- Rational hyperbolic sine rounds its exact real value. -/
theorem sinhRat_eq_real (format : Format) (argument : Rat) :
    sinhRat format argument = RealRounding.round format (Real.sinh (argument : ℝ)) :=
  ComparisonRounding.roundSigned_eq_real format _ _ (compareSinh_eq_real argument)

/-- Rational hyperbolic cosine rounds its exact real value. -/
theorem coshRat_eq_real (format : Format) (argument : Rat) :
    coshRat format argument = RealRounding.round format (Real.cosh (argument : ℝ)) :=
  ComparisonRounding.roundSigned_eq_real format _ _ (compareCosh_eq_real argument)

/-- Rational inverse hyperbolic sine rounds its exact real value. -/
theorem arsinhRat_eq_real (format : Format) (argument : Rat) :
    arsinhRat format argument = RealRounding.round format (Real.arsinh (argument : ℝ)) :=
  ComparisonRounding.roundSigned_eq_real format _ _ (prepareArsinh_eq_real argument _)

/-- Rational inverse hyperbolic cosine rounds its nonnegative real branch. -/
theorem arcoshRat_eq_real (format : Format) (argument : Rat) (hdomain : 1 ≤ argument) :
    arcoshRat format argument = RealRounding.round format (Real.arcosh (argument : ℝ)) := by
  rw [arcoshRat, if_pos hdomain]
  exact ComparisonRounding.roundSigned_eq_real format _ _
    (fun boundary => prepareArcosh_eq_real argument _ boundary hdomain)

/-- Inverse hyperbolic cosine rejects arguments below one. -/
theorem arcoshRat_eq_nar (format : Format) (argument : Rat) (houtside : argument < 1) :
    arcoshRat format argument = nar format := by
  simp [arcoshRat, not_le_of_gt houtside]

end Hyperbolic

variable {format : Format}

/-- Every finite hyperbolic tangent has one final rounding of its exact real value. -/
theorem tanH_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q) :
    tanH value = RealRounding.round format (Real.tanh (q : ℝ)) := by
  simp only [tanH, Hyperbolic.applyRat, hvalue]
  exact Hyperbolic.tanhRat_eq_real format q

/--
Inverse hyperbolic tangent rounds its exact real value for inputs strictly between `-1` and `1`.
-/
theorem arcTanH_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q)
    (hlower : -1 < q) (hupper : q < 1) :
    arcTanH value = RealRounding.round format (Real.artanh (q : ℝ)) := by
  simp only [arcTanH, Hyperbolic.applyRat, hvalue]
  exact Hyperbolic.artanhRat_eq_real format q hlower hupper

/-- Hyperbolic tangent propagates NaR. -/
@[simp] theorem tanH_nar : tanH (nar format) = nar format := Hyperbolic.applyRat_nar _

/-- Inverse hyperbolic tangent propagates NaR. -/
@[simp] theorem arcTanH_nar : arcTanH (nar format) = nar format := Hyperbolic.applyRat_nar _

/-- Inverse hyperbolic tangent returns NaR at and beyond either endpoint. -/
theorem arcTanH_eq_nar_of_outside (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (houtside : q ≤ -1 ∨ 1 ≤ q) :
    arcTanH value = nar format := by
  simp only [arcTanH, Hyperbolic.applyRat, hvalue]
  exact Hyperbolic.artanhRat_eq_nar format q houtside

/-- Finite hyperbolic sine rounds its exact real value on its real domain. -/
theorem sinH_eq_real (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) :
    sinH value = RealRounding.round format (Real.sinh (q : ℝ)) := by
  simp only [sinH, Hyperbolic.applyRat, hvalue]
  exact Hyperbolic.sinhRat_eq_real format q

/-- Hyperbolic sine propagates NaR. -/
@[simp] theorem sinH_nar : sinH (nar format) = nar format := Hyperbolic.applyRat_nar _

/-- Finite hyperbolic cosine rounds its exact real value on its real domain. -/
theorem cosH_eq_real (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) :
    cosH value = RealRounding.round format (Real.cosh (q : ℝ)) := by
  simp only [cosH, Hyperbolic.applyRat, hvalue]
  exact Hyperbolic.coshRat_eq_real format q

/-- Hyperbolic cosine propagates NaR. -/
@[simp] theorem cosH_nar : cosH (nar format) = nar format := Hyperbolic.applyRat_nar _

/-- Finite inverse hyperbolic sine rounds its exact real value on its real domain. -/
theorem arcSinH_eq_real (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) :
    arcSinH value = RealRounding.round format (Real.arsinh (q : ℝ)) := by
  simp only [arcSinH, Hyperbolic.applyRat, hvalue]
  exact Hyperbolic.arsinhRat_eq_real format q

/-- Inverse hyperbolic sine propagates NaR. -/
@[simp] theorem arcSinH_nar : arcSinH (nar format) = nar format := Hyperbolic.applyRat_nar _

/-- Finite inverse hyperbolic cosine rounds its exact real value on its real domain. -/
theorem arcCosH_eq_real (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hdomain : 1 ≤ q) :
    arcCosH value = RealRounding.round format (Real.arcosh (q : ℝ)) := by
  simp only [arcCosH, Hyperbolic.applyRat, hvalue]
  exact Hyperbolic.arcoshRat_eq_real format q hdomain

/-- Inverse hyperbolic cosine propagates NaR. -/
@[simp] theorem arcCosH_nar : arcCosH (nar format) = nar format := Hyperbolic.applyRat_nar _

/-- Inverse hyperbolic cosine rejects finite inputs below one. -/
theorem arcCosH_eq_nar_of_lt_one (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (houtside : q < 1) :
    arcCosH value = nar format := by
  simp only [arcCosH, Hyperbolic.applyRat, hvalue]
  exact Hyperbolic.arcoshRat_eq_nar format q houtside

end FloatLib.Floats.Formats.Posit.Model
