/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Configured.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Core

/-!
# Runtime conversion sources for configured OCP MX values

You can convert from an E8M0 scale or a complete MX block, because both have exact observations.
Converting into them is another matter. Building a block means choosing a scale, an element
rounding, a length, and a policy for exceptional values, so no destination quantizer is installed.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.OCP.MX

namespace E8M0.Conversion

/-- Decode a configured E8M0 scale to its exact dyadic or exceptional observation. -/
instance exactDecoder :
    FloatLib.Floats.ExecFloat.ExactDecoder
      ExecFloat.OCP.MX.E8M0 Numerics.Dyadic where
  decode value :=
    Formats.OCP.MX.E8M0.numericalSystem.denote value.toCode

end E8M0.Conversion

namespace Block.Conversion

variable {format : FloatFormat}

/-- Decode a complete configured MX block to exact scaled dyadics or an exceptional observation. -/
instance exactDecoder :
    FloatLib.Floats.ExecFloat.ExactDecoder
      (ExecFloat.OCP.MX.Block format) (Array Numerics.Dyadic) where
  decode value :=
    (Formats.OCP.MX.blockSystem format).denote value.toCode

end Block.Conversion

end ExecFloat.OCP.MX
end FloatLib.Floats
