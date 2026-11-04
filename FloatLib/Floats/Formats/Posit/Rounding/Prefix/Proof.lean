/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Prefix.Runtime

import FloatLib.Numerics.ShiftRightJam.Proof

/-!
# Shared finite-prefix proof helpers

These lemmas describe sticky-bit jamming without caring which operation produced the prefix, and
that is why the quotient and square-root kernels can share them.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.StickyPrefix

/-- Jamming leaves an exact prefix alone, and otherwise it sets the low bit and nothing else. -/
theorem jamRemainder_eq (value remainder : Nat) :
    jamRemainder value remainder =
      if remainder = 0 then
        value
      else if value % 2 = 0 then
        value + 1
      else
        value := by
  unfold jamRemainder
  by_cases hremainder : remainder = 0
  · simp [hremainder]
  · simp [hremainder, FloatLib.Numerics.or_one_eq]

/--
Jamming either keeps the value or adds one to an even value. `jamRemainder_eq` says which case
happens for a given remainder.
-/
theorem jamRemainder_eq_or (value remainder : Nat) :
    jamRemainder value remainder = value ∨
      (jamRemainder value remainder = value + 1 ∧ value % 2 = 0) := by
  rw [jamRemainder_eq]
  split_ifs <;> simp_all

/-- Jamming never decreases a prefix. -/
theorem le_jamRemainder (value remainder : Nat) :
    value ≤ jamRemainder value remainder := by
  rcases jamRemainder_eq_or value remainder with hjam | ⟨hjam, -⟩ <;> omega

/-- Jamming depends only on whether the remainder is zero. -/
theorem jamRemainder_congr
    (value first second : Nat)
    (hzero : first = 0 ↔ second = 0) :
    jamRemainder value first = jamRemainder value second := by
  unfold jamRemainder
  by_cases hfirst : first = 0
  · simp [hfirst, hzero.mp hfirst]
  · have hsecond : second ≠ 0 := mt hzero.mpr hfirst
    simp [hfirst, hsecond]

end FloatLib.Floats.Formats.Posit.Model.StickyPrefix
