/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Trigonometric.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Proof

/-!
# Real semantics of posit trigonometric operations

The operation proofs compose exact comparator semantics with the standard posit rounding
algorithm. They cover all finite inputs in the real domain, including exact zero results,
domain endpoints, and nonzero saturation. NaR propagation and invalid inverse domains are
stated separately.
-/

public section

namespace FloatLib.Floats.Formats.Posit.Model

namespace Trigonometric

open FloatLib.Numerics.Enclosure.Comparison

/-- Exact comparison followed by signed posit rounding gives the required real result. -/
theorem evaluate_eq_real (prepare : Rat → Nat → Prepared) (function : ℝ → ℝ)
    (hprepare : ∀ argument levels boundary,
      (prepare argument levels).compare boundary = cmp (function argument) (boundary : ℝ))
    {format : Format} (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) :
    evaluate prepare value = RealRounding.round format (function q) := by
  simp only [evaluate, hvalue]
  exact ComparisonRounding.roundSigned_eq_real format _ _ (hprepare q _)

/-- The same composition applies to a comparator whose contract is restricted to `[-1, 1]`. -/
theorem evaluateUnit_eq_real (prepare : Rat → Nat → Prepared) (function : ℝ → ℝ)
    (hprepare : ∀ argument levels boundary, -1 ≤ argument → argument ≤ 1 →
      (prepare argument levels).compare boundary = cmp (function argument) (boundary : ℝ))
    {format : Format} (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hlower : -1 ≤ q) (hupper : q ≤ 1) :
    evaluateUnit prepare value = RealRounding.round format (function q) := by
  simp only [evaluateUnit, hvalue, if_pos (And.intro hlower hupper)]
  exact ComparisonRounding.roundSigned_eq_real format _ _
    (fun boundary => hprepare q _ boundary hlower hupper)

/-- Evaluation propagates NaR without preparing a comparison search. -/
@[simp] theorem evaluate_nar (prepare : Rat → Nat → Prepared) {format : Format} :
    evaluate prepare (nar format) = nar format := by
  simp [evaluate]

/-- The closed-domain adapter also propagates NaR. -/
@[simp] theorem evaluateUnit_nar (prepare : Rat → Nat → Prepared) {format : Format} :
    evaluateUnit prepare (nar format) = nar format := by
  simp [evaluateUnit]

/-- A finite input outside the closed unit interval produces NaR before evaluation. -/
theorem evaluateUnit_eq_nar (prepare : Rat → Nat → Prepared) {format : Format}
    (value : Model format) {q : Rat} (hvalue : value.toRat? = some q)
    (houtside : q < -1 ∨ 1 < q) : evaluateUnit prepare value = nar format := by
  have hdomain : ¬ (-1 ≤ q ∧ q ≤ 1) := by
    rintro ⟨hlower, hupper⟩
    rcases houtside with h | h <;> linarith
  simp [evaluateUnit, hvalue, hdomain]

end Trigonometric

open FloatLib.Numerics.TrigonometricComparison

variable {format : Format}

/-- Sine rounds its exact real value at every finite radian input. -/
theorem sin_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q) :
    sin value = RealRounding.round format (Real.sin (q : ℝ)) :=
  Trigonometric.evaluate_eq_real _ _ prepareSin_eq_real value hvalue

/-- Cosine rounds its exact real value at every finite radian input. -/
theorem cos_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q) :
    cos value = RealRounding.round format (Real.cos (q : ℝ)) :=
  Trigonometric.evaluate_eq_real _ _ prepareCos_eq_real value hvalue

/-- Tangent is correctly rounded at every finite posit input. -/
theorem tan_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q) :
    tan value = RealRounding.round format (Real.tan (q : ℝ)) :=
  Trigonometric.evaluate_eq_real _ _ prepareTan_eq_real value hvalue

/-- Inverse sine includes both endpoints of its real domain. -/
theorem arcSin_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q)
    (hlower : -1 ≤ q) (hupper : q ≤ 1) :
    arcSin value = RealRounding.round format (Real.arcsin (q : ℝ)) :=
  Trigonometric.evaluateUnit_eq_real _ _ prepareArcsin_eq_real value hvalue hlower hupper

/-- Inverse cosine includes both endpoints of its real domain. -/
theorem arcCos_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q)
    (hlower : -1 ≤ q) (hupper : q ≤ 1) :
    arcCos value = RealRounding.round format (Real.arccos (q : ℝ)) :=
  Trigonometric.evaluateUnit_eq_real _ _ prepareArccos_eq_real value hvalue hlower hupper

/-- Inverse tangent rounds its principal real value at every finite input. -/
theorem arcTan_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q) :
    arcTan value = RealRounding.round format (Real.arctan (q : ℝ)) :=
  Trigonometric.evaluate_eq_real _ _ prepareArctan_eq_real value hvalue

/-- Sine propagates NaR. -/
@[simp] theorem sin_nar : sin (nar format) = nar format := Trigonometric.evaluate_nar _
/-- Cosine propagates NaR. -/
@[simp] theorem cos_nar : cos (nar format) = nar format := Trigonometric.evaluate_nar _
/-- Tangent propagates NaR. -/
@[simp] theorem tan_nar : tan (nar format) = nar format := Trigonometric.evaluate_nar _
/-- Inverse sine propagates NaR. -/
@[simp] theorem arcSin_nar : arcSin (nar format) = nar format := Trigonometric.evaluateUnit_nar _
/-- Inverse cosine propagates NaR. -/
@[simp] theorem arcCos_nar : arcCos (nar format) = nar format := Trigonometric.evaluateUnit_nar _
/-- Inverse tangent propagates NaR. -/
@[simp] theorem arcTan_nar : arcTan (nar format) = nar format := Trigonometric.evaluate_nar _

/-- Inverse sine rejects real inputs outside `[-1, 1]`. -/
theorem arcSin_eq_nar_of_outside (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (houtside : q < -1 ∨ 1 < q) :
    arcSin value = nar format :=
  Trigonometric.evaluateUnit_eq_nar _ value hvalue houtside

/-- Inverse cosine rejects real inputs outside `[-1, 1]`. -/
theorem arcCos_eq_nar_of_outside (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (houtside : q < -1 ∨ 1 < q) :
    arcCos value = nar format :=
  Trigonometric.evaluateUnit_eq_nar _ value hvalue houtside

end FloatLib.Floats.Formats.Posit.Model
