/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime
public import FloatLib.Numerics.Enclosure.Interval.Runtime

/-!
# Posit interval endpoints

`intervalRounding` brackets an exact rational using adjacent posit words for any supported
width. It reuses the existing monotone-code bisection, rather than assuming the nearest posit
rounder rounds outward. Negative bounds are obtained by reversing and negating the positive
bounds. An exactly represented input receives a point enclosure.

The distinction from ordinary posit rounding matters at the extremes: a small positive value
is bracketed by zero and minPos, while a magnitude beyond maxPos cannot have a finite posit
enclosure and returns `none`. The exact endpoint check rejects NaR and any failed bracket.
The common `Numerics.Interval` arithmetic uses this same checked rounding operation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit

/-- An interval with exact-width posit words as endpoints. -/
abbrev Interval (format : Format) := Numerics.Interval (Model format)

/-- Adjacent positive-code candidates, mirrored when the input is negative. -/
def intervalCandidates (format : Format) (x : ℚ) : Interval format :=
  let magnitude := |x|
  let lowerCode := Model.lowerCodeForPositive format magnitude
  let lower : Model format := Model.ofNatBits lowerCode
  let upper : Model format :=
    if Model.nonnegativeRatAt format lowerCode = magnitude then lower
    else Model.ofNatBits (lowerCode + 1)
  if x < 0 then ⟨Model.neg upper, Model.neg lower⟩ else ⟨lower, upper⟩

/--
Checked outward rounding for arbitrary posit widths.

Overflow is reported as `none`; the standard's saturated maxPos output is not an upper bound
for values beyond the format's range. No infinity is introduced into the posit representation.
-/
def intervalRounding (format : Format) : Numerics.OutwardRounding (Model format) ℚ :=
  Numerics.OutwardRounding.ofCandidates Model.toRat? (intervalCandidates format)

end FloatLib.Floats.Formats.Posit
