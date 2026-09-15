/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Logarithmic.Configured.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Core

/-!
# Runtime conversion source for configured logarithmic values

Every exact logarithmic value is zero or a signed integral power of its radix and therefore has an
exact rational observation. This module supplies source decoding only; no destination quantizer
or rounding policy is installed.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.Logarithmic
namespace Conversion

variable {radix : Radix}

/-- Decode a configured logarithmic value to its exact rational meaning. -/
instance exactDecoder :
    FloatLib.Floats.ExecFloat.ExactDecoder
      (ExecFloat.Logarithmic radix) Rat where
  decode value := .finite value.toCode.toRat

end Conversion
end ExecFloat.Logarithmic
end FloatLib.Floats
