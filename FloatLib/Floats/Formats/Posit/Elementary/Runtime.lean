/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime
public import FloatLib.Numerics.Exact.Elementary.Runtime

/-!
# Natural exponential and logarithm for posits

Each operation compares its exact mathematical result with the posit rounding boundaries.
Adaptive rational enclosures resolve the comparisons, with termination proved in the
format-independent numerics layer. No intermediate posit rounding occurs in `expMinus1`
or `logPlus1`.

The operation and domain rules follow the Posit Standard (2022), §§5.1 and 5.5.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

namespace Elementary

/-- Round the exponential of a rational, optionally subtracting an exact offset first. -/
def expRat (format : Format) (argument offset : Rat) : Model format :=
  let compareTarget :=
    FloatLib.Numerics.ElementaryComparison.prepareExp argument (format.bits.log2 + 2)
  ComparisonRounding.roundSigned format
    (fun boundary => compareTarget.compare (boundary + offset))

/-- Round the natural logarithm of a positive rational; reject other arguments. -/
def logRat (format : Format) (argument : Rat) : Model format :=
  if hpositive : 0 < argument then
    ComparisonRounding.roundSigned format
      (FloatLib.Numerics.ElementaryComparison.prepareLog
        argument (format.bits.log2 + 2) hpositive).compare
  else nar format

/-- Lift exponential evaluation and exact output subtraction, propagating NaR. -/
def applyExp {format : Format} (offset : Rat) (value : Model format) : Model format :=
  match value.toRat? with
  | none => nar format
  | some argument => expRat format argument offset

/-- Form the logarithm argument exactly before evaluation and one final rounding. -/
def applyLog {format : Format} (offset : Rat) (value : Model format) : Model format :=
  match value.toRat? with
  | none => nar format
  | some argument => logRat format (argument + offset)

end Elementary

/-- Correctly rounded natural exponential. NaR propagates. -/
def exp {format : Format} (value : Model format) : Model format :=
  Elementary.applyExp 0 value

/-- Correctly rounded `exp x - 1`, with no intermediate rounding of the exponential. -/
def expMinus1 {format : Format} (value : Model format) : Model format :=
  Elementary.applyExp 1 value

/-- Correctly rounded natural logarithm. Nonpositive inputs and NaR produce NaR. -/
def log {format : Format} (value : Model format) : Model format :=
  Elementary.applyLog 0 value

/-- Correctly rounded `log (1 + x)`, with no intermediate rounding of the addition. -/
def logPlus1 {format : Format} (value : Model format) : Model format :=
  Elementary.applyLog 1 value

end FloatLib.Floats.Formats.Posit.Model
