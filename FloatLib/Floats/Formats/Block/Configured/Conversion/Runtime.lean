/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Configured.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Core

/-!
# Shared-scale block conversion runtime

Conversion takes the common binary exponent as an explicit `Int` context and rounds each lane
to the corresponding grid. `Conversion.Instances` installs this contextual quantizer without a
`DefaultQuantizer` instance.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.SharedScale
namespace Conversion

variable {lanes : Nat}

/-- Conversion status records whether any lane changed at the selected shared scale. -/
@[inline] def status (exact : Vector Rat lanes) (rounded : ExecFloat.SharedScale lanes) :
    FloatLib.Floats.ExecFloat.ConversionStatus :=
  { inexact := decide (ExecFloat.SharedScale.decode rounded ≠ exact) }

/-- Quantize a complete block observation at an explicitly supplied shared exponent. -/
@[inline] def run (exponent : Int) :
    NumericalValue (Vector Rat lanes) →
      FloatLib.Floats.ExecFloat.ConversionOutcome (ExecFloat.SharedScale lanes)
  | .finite exact =>
      let rounded := ExecFloat.SharedScale.quantizeAt exponent exact
      .success rounded (status exact rounded)
  | .infinity negative =>
      .failure (.infinity .source negative)
  | .exceptional exceptional =>
      .failure (.exceptional .source exceptional)

/--
Relational shared-scale conversion contract.

Finite success must satisfy the lane-wise nearest-even `QuantizesAt` relation. Non-finite inputs
are rejected because this unbounded block family has no corresponding codes.
-/
def spec (exponent : Int)
    (input : NumericalValue (Vector Rat lanes))
    (outcome : FloatLib.Floats.ExecFloat.ConversionOutcome
      (ExecFloat.SharedScale lanes)) : Prop :=
  match input with
  | .finite exact =>
      ∃ rounded,
        outcome = .success rounded (status exact rounded) ∧
          Formats.Block.QuantizesAt exponent exact rounded.toCode
  | .infinity negative =>
      outcome = .failure (.infinity .source negative)
  | .exceptional exceptional =>
      outcome = .failure (.exceptional .source exceptional)

/-- Shared-scale values decode to their exact rational vector. -/
instance exactDecoder :
    FloatLib.Floats.ExecFloat.ExactDecoder
      (ExecFloat.SharedScale lanes) (Vector Rat lanes) where
  decode value := .finite (ExecFloat.SharedScale.decode value)

end Conversion
end ExecFloat.SharedScale
end FloatLib.Floats
