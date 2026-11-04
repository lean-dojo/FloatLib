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

Every ordinary posit has an exact rational meaning, and this module embeds it into mathlib's
`Real` so that proofs can work with real coordinates. NaR keeps both of its forms,
`ExceptionalValue.notAReal` in the complete view and `none` in the partial one. For the
executable rational denotation, see `Posit.Semantics.Exact.Runtime`.
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

/-- Exact real value of an ordinary posit. The result is `none` on NaR and on no other word. -/
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

/-- Only the unique NaR word has no optional real view. -/
theorem toReal?_eq_none_iff (value : Model format) :
    value.toReal? = none ↔ value.isNaR = true := by
  rw [toReal?]
  simp [toRat?_eq_none_iff]

end Model
end FloatLib.Floats.Formats.Posit
