/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Conversion.Proof

/-!
# Bounded fixed-point conversion instances

Bounded fixed-point destinations support exact-rational quantization under an explicit overflow
policy. The context-free instance chooses checked conversion and therefore rejects overflow.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.BoundedFixedPoint
namespace Conversion

variable {radix : Radix} {fractionalDigits width : Nat}

/-- Bounded fixed-point conversion requires an explicit overflow policy. -/
instance quantizer :
    FloatLib.Floats.ExecFloat.Quantizer
      (ExecFloat.BoundedFixedPoint radix fractionalDigits width) Rat where
  Context := OverflowPolicy
  run := run
  spec := spec
  correct := implements_run

/-- Context-free bounded conversion is checked and rejects overflow. -/
instance defaultQuantizer :
    FloatLib.Floats.ExecFloat.DefaultQuantizer
      (ExecFloat.BoundedFixedPoint radix fractionalDigits width) Rat where
  defaultContext := .reject

end Conversion
end ExecFloat.BoundedFixedPoint
end FloatLib.Floats
