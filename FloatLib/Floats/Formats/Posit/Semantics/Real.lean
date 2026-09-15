/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof
public import Mathlib.Basic.Real.Basic

/-!
# Optional real-valued semantics of posits

The exact rational meaning of every ordinary posit embeds into mathlib's `Real`. NaR remains
`ExceptionalValue.notAReal` in the complete view and `none` in the partial view.

`Posit.Semantics.Exact.Runtime` provides the executable rational denotation. This module adds
real coordinates for proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit

open FloatLib.Numerics

namespace Model.ExactValue

/-- Canonically embed finite rational meanings into mathlib reals. -/
@[inline] noncomputable def toRealValue {format : Format}
    (value : Model.ExactValue format) : NumericalValue ℝ :=
  value.forget.map fun rational : Rat => (rational : ℝ)

end Model.ExactValue

namespace Model

variable {format : Format}

/-- Complete real-valued view, obtained only by mapping finite rational values. -/
@[inline] noncomputable def decodeReal (value : Model format) : NumericalValue ℝ :=
  value.decodeExact.toRealValue

/-- Exact real value of an ordinary posit, or `none` exactly for NaR. -/
@[inline] noncomputable def toReal? (value : Model format) : Option ℝ :=
  value.toRat?.map fun rational : Rat => (rational : ℝ)

/-- The canonical posit zero denotes real zero. -/
@[simp] theorem toReal?_zero (format : Format) :
    toReal? (zero format) = some 0 := by
  simp [toReal?]

/-- Posit NaR has no ordinary real interpretation. -/
@[simp] theorem toReal?_nar (format : Format) :
    toReal? (nar format) = none := by
  simp [toReal?]

/-- The optional real view is unavailable precisely for the unique NaR word. -/
theorem toReal?_eq_none_iff (value : Model format) :
    value.toReal? = none ↔ value.isNaR = true := by
  rw [toReal?]
  simp [toRat?_eq_none_iff]

end Model
end FloatLib.Floats.Formats.Posit
