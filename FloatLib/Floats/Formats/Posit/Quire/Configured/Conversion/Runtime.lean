/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Configured.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Core

/-!
# Runtime conversion source for configured posit quires

A quire is an exact accumulator rather than another rounded floating-point destination. Ordinary
words decode to rationals and the reserved word decodes to NaR, so configured quires participate
as exact conversion sources. No destination quantizer is installed without an explicit grid and
overflow policy.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit.Quire
namespace Conversion

variable {format : Format}

/-- A configured quire exposes its complete exact rational or NaR observation. -/
instance exactDecoder :
    FloatLib.Floats.ExecFloat.ExactDecoder
      (Formats.Posit.Quire.Model format) Rat where
  decode := ExecFloat.Posit.Quire.decode

end Conversion
end ExecFloat.Posit.Quire
end FloatLib.Floats
