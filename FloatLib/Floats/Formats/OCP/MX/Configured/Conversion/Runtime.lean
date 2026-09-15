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

E8M0 scales and complete MX blocks expose their exact observations as conversion sources.
No destination quantizer is installed because construction requires explicit scale-selection,
element-rounding, length, and exceptional-value policies.
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
