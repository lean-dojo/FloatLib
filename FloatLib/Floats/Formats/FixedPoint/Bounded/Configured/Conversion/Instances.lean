/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Conversion.Proof

/-!
# Bounded fixed-point conversion instances

Converting an exact rational into bounded fixed point needs an overflow policy, and the caller
picks it. When there's no context to pick from, the instance here uses `.reject`, the same default
the arithmetic uses.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.BoundedFixedPoint
namespace Conversion

variable {radix : Radix} {fractionalDigits width : Nat}

/-- Bounded fixed-point conversion, with the overflow policy as its context. -/
instance quantizer :
    FloatLib.Floats.ExecFloat.Quantizer
      (ExecFloat.BoundedFixedPoint radix fractionalDigits width) Rat where
  Context := OverflowPolicy
  run := run
  spec := spec
  correct := implements_run

/-- Context-free bounded conversion rejects overflow. -/
instance defaultQuantizer :
    FloatLib.Floats.ExecFloat.DefaultQuantizer
      (ExecFloat.BoundedFixedPoint radix fractionalDigits width) Rat where
  defaultContext := .reject

end Conversion
end ExecFloat.BoundedFixedPoint
end FloatLib.Floats
