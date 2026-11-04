/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Configured.Conversion.Proof

/-!
# Shared-scale block conversion instances

Quantizing into a shared-scale block takes the shared exponent from the caller. This module
installs that contextual quantizer and on purpose installs no `DefaultQuantizer`, because a default
would hide a scale-selection policy such as maximum magnitude.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.SharedScale
namespace Conversion

variable {lanes : Nat}

/--
Shared-scale destinations quantize only when the caller supplies the exponent context.

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
