/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Enclosure.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Real
public import FloatLib.Numerics.Enclosure.Elementary.Proof

/-!
# Certified rounding from rational enclosures

Real posit rounding is monotone, so the rounded target lies between the rounded endpoints, and
when the endpoints agree the target rounds to that same code
(`eq_roundPositive_of_roundPositive?_eq_some`). For the exponential this means an accepted result of
the enclosure algorithm carries its own analytic justification inside the library.

These theorems are about results that were accepted. They don't say that any fixed Taylor degree
settles every input.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.Enclosure

open FloatLib.Numerics

/-- Equal endpoint codes determine the rounded code of every enclosed real value. -/
theorem roundPositiveCode_eq_of_contains (format : Format)
    {interval : RationalInterval} {x : ℝ} (hx : interval.Contains x)
    (hequal : Model.roundPositiveCode format interval.lo =
      Model.roundPositiveCode format interval.hi) :
    RealRounding.roundPositiveCode format x =
      Model.roundPositiveCode format interval.lo := by
  have hlower := RealRounding.roundPositiveCode_mono format hx.1
  have hupper := RealRounding.roundPositiveCode_mono format hx.2
  rw [RealRounding.roundPositiveCode_ratCast] at hlower hupper
  apply le_antisymm _ hlower
  rw [hequal]
  exact hupper

/-- Every accepted enclosure result equals rounding the enclosed real target. -/
theorem eq_roundPositive_of_roundPositive?_eq_some (format : Format)
    {interval : RationalInterval} {x : ℝ} {result : Model format}
    (hx : interval.Contains x) (hresult : roundPositive? format interval = some result) :
    result = RealRounding.roundPositive format x := by
  unfold roundPositive? at hresult
  dsimp only at hresult
  split at hresult
  · rename_i hequal
    have hcode := roundPositiveCode_eq_of_contains format hx hequal
    have hmodel := Option.some.inj hresult
    rw [← hmodel, RealRounding.roundPositive, hcode]
  · simp at hresult

/-- An accepted rational exponential enclosure is correctly rounded to the posit format. -/
theorem eq_roundPositive_exp_of_roundPositive?_eq_some (format : Format)
    (x : ℚ) (degree : Nat) {result : Model format}
    (hresult :
      roundPositive? format (FloatLib.Numerics.Enclosure.exp x degree) = some result) :
    result = RealRounding.roundPositive format (Real.exp (x : ℝ)) :=
  eq_roundPositive_of_roundPositive?_eq_some format
    (FloatLib.Numerics.Enclosure.contains_exp x degree) hresult

end FloatLib.Floats.Formats.Posit.Model.Enclosure
