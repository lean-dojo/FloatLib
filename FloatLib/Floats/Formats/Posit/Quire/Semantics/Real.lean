/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Semantics.Proof
public import Mathlib.Data.Real.Basic

/-!
# Real-valued views of posit quires

These adapters embed ordinary exact rational quire values into mathlib's `Real`. They are separate
from executable semantics so quire arithmetic does not import real-analysis infrastructure.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Quire.Model

open FloatLib.Numerics

variable {format : Format}

/-- Complete real semantics obtained by mapping only ordinary exact rational values. -/
@[inline] noncomputable def decodeReal (value : Model format) : NumericalValue ℝ :=
  value.decode.map fun rational : Rat => (rational : ℝ)

/-- Optional real value of a quire, unavailable exactly for quire NaR. -/
@[inline] noncomputable def toReal? (value : Model format) : Option ℝ :=
  value.toRat?.map fun rational : Rat => (rational : ℝ)

/-- The zero quire denotes the real number zero. -/
@[simp] theorem toReal?_zero (format : Format) :
    (zero format).toReal? = some 0 := by
  simp [toReal?]

/-- The NaR quire has no ordinary real interpretation. -/
@[simp] theorem toReal?_nar (format : Format) :
    (nar format).toReal? = none := by
  simp [toReal?]

/-- The optional real view is unavailable precisely for quire NaR. -/
theorem toReal?_eq_none_iff (value : Model format) :
    value.toReal? = none ↔ value.isNaR = true := by
  simp [toReal?, toRat?_eq_none_iff]

end FloatLib.Floats.Formats.Posit.Quire.Model
