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

Every exact logarithmic value is zero or a signed integral power of its radix, so it always has an
exact rational reading, and `2^-3` reads as `1/8`. That makes logarithmic values good conversion
sources. This module supplies only that source decoding, with no destination quantizer and no
rounding policy.
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
  decode value := .finite value.toRat

end Conversion
end ExecFloat.Logarithmic
end FloatLib.Floats
