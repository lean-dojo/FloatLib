/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Logarithmic.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.Logarithmic.Exact.Proof
public import FloatLib.Floats.ExecFloat.Conversion.Runtime

/-!
# Proof contracts for configured logarithmic decoding

The runtime decoder exposes an exact rational through the common `ExactDecoder` interface, and
`exactDecoder_run` identifies it with the configured reading `toRat`. `cast_toRat` relates that
reading to the real-valued specification.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.Logarithmic
namespace Conversion

variable {radix : Radix}

/-- The installed logarithmic source capability uses the exact rational reading `toRat`. -/
@[simp, grind =] theorem exactDecoder_run (value : ExecFloat.Logarithmic radix) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value =
      .finite value.toRat :=
  rfl

end Conversion
end ExecFloat.Logarithmic
end FloatLib.Floats
