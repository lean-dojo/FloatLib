/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Prefix.Runtime

import Mathlib.Data.Nat.Bitwise

/-!
# Shared finite-prefix proof helpers

These lemmas describe sticky-bit jamming independently of the operation that generated the
prefix. Quotient and square-root kernels share this proof layer.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.StickyPrefix

/-- Setting the low bit either preserves an odd value or increments an even value. -/
theorem lor_one_eq (value : Nat) :
    value ||| 1 =
      if value % 2 = 0 then value + 1 else value := by
  conv_lhs =>
    lhs
    rw [← Nat.bit_bodd_div2 value]
  rw [show (1 : Nat) = Nat.bit true 0 by rfl, Nat.lor_bit]
  cases hodd : value.bodd with
  | false =>
      have hvalue := Nat.bit_bodd_div2 value
      rw [hodd] at hvalue
      simpa [hodd, Nat.mod_two_of_bodd] using hvalue
  | true =>
      have hvalue := Nat.bit_bodd_div2 value
      rw [hodd] at hvalue
      simpa [hodd, Nat.mod_two_of_bodd] using hvalue

/-- Jamming preserves an exact prefix and otherwise sets precisely its low bit. -/
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
  · simp [hremainder, lor_one_eq]

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
