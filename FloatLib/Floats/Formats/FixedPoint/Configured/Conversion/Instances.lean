/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Configured.Conversion.Proof

/-!
# Exact fixed-point conversion instances

Unbounded configured fixed point supports exact-rational destination quantization with a
canonical context.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.FixedPoint
namespace Conversion

variable {radix : Radix} {fractionalDigits : Nat}

/-- Every exact fixed-point grid quantizes finite rationals with ties to even. -/
instance quantizer :
    FloatLib.Floats.ExecFloat.Quantizer
      (ExecFloat.FixedPoint radix fractionalDigits) Rat where
  Context := Unit
  run := run
  spec := spec
  correct := implements_run

/-- Exact fixed-point conversion has one canonical context. -/
instance defaultQuantizer :
    FloatLib.Floats.ExecFloat.DefaultQuantizer
      (ExecFloat.FixedPoint radix fractionalDigits) Rat where
  defaultContext := ()

end Conversion
end ExecFloat.FixedPoint
end FloatLib.Floats
