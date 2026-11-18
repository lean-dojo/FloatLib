/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Executable.Conversion.Core
public import FloatLib.Floats.Formats.OCP.MX.Configured.Runtime

/-!
# Runtime conversion source for configured E8M0 values

You can convert from an E8M0 scale, because it has an exact observation. No destination quantizer
is installed for a bare scale: a scale is selected for a block of elements, by the scale level of a
block format (`E8M0.codec` with `Block.CodedFormat.quantize`).
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

end ExecFloat.OCP.MX
end FloatLib.Floats
