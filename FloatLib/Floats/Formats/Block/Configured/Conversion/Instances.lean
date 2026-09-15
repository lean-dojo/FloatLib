/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Configured.Conversion.Proof

/-!
# Shared-scale block conversion instances

Shared-scale block quantization requires an explicit shared exponent. No `DefaultQuantizer`
instance is installed.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.SharedScale
namespace Conversion

variable {lanes : Nat}

/--
Shared-scale destinations support quantization only with an explicit exponent context.

There is intentionally no `DefaultQuantizer` instance.
-/
instance quantizer :
    FloatLib.Floats.ExecFloat.Quantizer
      (ExecFloat.SharedScale lanes) (Vector Rat lanes) where
  Context := Int
  run := run
  spec := spec
  correct := implements_run

end Conversion
end ExecFloat.SharedScale
end FloatLib.Floats
