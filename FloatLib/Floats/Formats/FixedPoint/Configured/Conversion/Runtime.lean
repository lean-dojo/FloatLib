/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Configured.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Core

/-!
# Exact fixed-point conversion runtime

An unbounded configured fixed-point destination has no overflow and no exceptional values. Every
finite rational is rounded once to the nearest grid coefficient, with ties to even. Infinity and
exceptional observations are rejected because the representation has no corresponding code.

Proofs of the reduction equations live in `Conversion.Proof`; destination capability instances
live in `Conversion.Instances`.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.FixedPoint
namespace Conversion

variable {radix : Radix} {fractionalDigits : Nat}

/-- Quantize one complete rational observation into an unbounded fixed-point grid. -/
@[inline] def run (_context : Unit) :
    NumericalValue Rat →
      FloatLib.Floats.ExecFloat.ConversionOutcome
        (ExecFloat.FixedPoint radix fractionalDigits)
  | .finite exact =>
      let rounded : ExecFloat.FixedPoint radix fractionalDigits :=
        ExecFloat.FixedPoint.roundRat exact
      .success rounded
        { inexact := ExecFloat.FixedPoint.toRat rounded != exact }
  | .infinity negative =>
      .failure (.infinity .source negative)
  | .exceptional exceptional =>
      .failure (.exceptional .source exceptional)

/--
The stored coefficient is nearest-even on the scaled integer grid, with exact status.

The half-unit bound and even-tie rule are numerical predicates on the delivered coefficient.
The coefficient equality also retains the unique complete code chosen by the integer rounder.
Infinity and exceptional observations retain their complete rejection reasons.
-/
def spec :
    Quantization.Spec Unit (NumericalValue Rat)
      (FloatLib.Floats.ExecFloat.ConversionOutcome
        (ExecFloat.FixedPoint radix fractionalDigits)) :=
  fun _ input outcome =>
    match input, outcome with
    | .finite exact, .success rounded indicators =>
        let scaled := exact * scale radix fractionalDigits
        let stored := coefficient rounded
        stored = roundRatEven scaled ∧
          |(stored : Rat) - scaled| ≤ (1 : Rat) / 2 ∧
          (|(stored : Rat) - scaled| = (1 : Rat) / 2 → stored % 2 = 0) ∧
          indicators = { inexact := ExecFloat.FixedPoint.toRat rounded != exact }
    | .infinity negative, .failure reason =>
        reason = .infinity .source negative
    | .exceptional exceptional, .failure reason =>
        reason = .exceptional .source exceptional
    | _, _ => False

/-- Exact fixed-point values decode canonically to rational observations. -/
instance exactDecoder :
    FloatLib.Floats.ExecFloat.ExactDecoder
      (ExecFloat.FixedPoint radix fractionalDigits) Rat where
  decode value := .finite (ExecFloat.FixedPoint.toRat value)

end Conversion
end ExecFloat.FixedPoint
end FloatLib.Floats
