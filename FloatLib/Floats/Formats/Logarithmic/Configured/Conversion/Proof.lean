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

The runtime decoder exposes an exact rational through the common `ExactDecoder` interface. These
lemmas connect that interface both to the logarithmic code's executable rational denotation and to
its real-valued specification.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.Logarithmic
namespace Conversion

variable {radix : Radix}

/-- The installed logarithmic source capability uses the executable exact rational decoder. -/
@[simp, grind =] theorem exactDecoder_run (value : ExecFloat.Logarithmic radix) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value =
      .finite value.toCode.toRat :=
  rfl

/-- Exact rational decoding agrees with the configured format's real semantics. -/
@[grind =, norm_cast] theorem cast_toCode_toRat
    (value : ExecFloat.Logarithmic radix) :
    (value.toCode.toRat : ℝ) = value.toReal :=
  Formats.Logarithmic.Code.cast_toRat value.toCode

end Conversion
end ExecFloat.Logarithmic
end FloatLib.Floats
