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

`intervalRounding` brackets an exact rational between two adjacent posit words, at any supported
width. It gets the bracket from the monotone-code bisection, because nothing promises that the
nearest posit rounder rounds outward. A negative input reuses the positive bounds, reversed and
negated, and an input that a posit represents gets a point enclosure.

At the extremes this differs from ordinary posit rounding. A small positive value is
bracketed by zero and minPos. A magnitude beyond maxPos can't have a finite posit enclosure, so the
result is `none`. An endpoint check rejects NaR and any failed bracket, and the common
`Numerics.Interval` arithmetic uses this same checked rounding operation.
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

Overflow comes back as `none`, because the standard's saturated maxPos output is not an upper
bound for values beyond the format's range. The posit representation gains no infinity.
-/
def intervalRounding (format : Format) : Numerics.OutwardRounding (Model format) ℚ :=
  Numerics.OutwardRounding.ofCandidates Model.toRat? (intervalCandidates format)

end FloatLib.Floats.Formats.Posit
