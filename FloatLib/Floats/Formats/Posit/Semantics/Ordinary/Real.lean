/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Semantics.Ordinary
public import FloatLib.Floats.Formats.Posit.Semantics.Real

/-!
# Real coordinates for ordinary posits

An ordinary posit excludes NaR and therefore has a total exact rational coordinate. This module
canonically embeds that coordinate into mathlib's `Real` for use in proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.Ordinary

variable {format : Format}

/-- Canonical exact-real coordinate obtained from the ordinary rational semantics. -/
@[inline] noncomputable def toReal (value : Ordinary format) : ℝ :=
  (value.toRat : ℝ)

/-- The model's optional real view agrees with the total ordinary real coordinate. -/
@[simp] theorem model_toReal?_eq_some (value : Ordinary format) :
    value.1.toReal? = some value.toReal := by
  simp [Model.toReal?, toReal]

/-- Ordinary posit zero denotes real zero. -/
@[simp] theorem toReal_zero (format : Format) :
    (zero format).toReal = 0 := by
  simp [toReal]

end FloatLib.Floats.Formats.Posit.Model.Ordinary
