/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Conversion.Proof

/-!
# P3109 conversion capabilities

The destination quantizer uses the exact rational scalar domain and the `ProjectionPolicy`
context. Context-free conversion selects FloatLib's nearest-even, no-saturation policy. A
conversion's `(mode := ...)` option takes a P3109 `RoundingMode`, as in
`x.cast (target := ExecFloat.P3109 .binary8p4se) (mode := .up)`.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats
namespace ExecFloat.P3109
namespace Conversion

variable {format : Formats.P3109.Format}

/-- Every valid P3109 descriptor supports policy-aware exact-rational quantization. -/
instance quantizer :
    FloatLib.Floats.ExecFloat.Quantizer
      (ExecFloat.P3109 format) Rat where
  Context := Formats.P3109.ProjectionPolicy
  run := run
  spec := spec
  correct := implements_run

/-- Context-free P3109 conversion uses nearest-even rounding and no saturation request. -/
instance defaultQuantizer :
    FloatLib.Floats.ExecFloat.DefaultQuantizer
      (ExecFloat.P3109 format) Rat where
  defaultContext := {}

/-- Conversions into a P3109 destination take a P3109 `RoundingMode`, nearest-even by default. -/
instance roundingModes :
    FloatLib.Floats.ExecFloat.RoundingModes (ExecFloat.P3109 format)
      Formats.P3109.RoundingMode where
  default := .nearest

/--
A conversion's `(mode := m)` selects rounding `m` with no saturation request. Passing
`(context := { rounding := m, saturation := s })` also chooses the saturation.
-/
@[inline] instance modeContext (mode : Formats.P3109.RoundingMode) :
    FloatLib.Floats.ExecFloat.ModeContext (ExecFloat.P3109 format) Rat mode where
  context := { rounding := mode }

/-- The context a P3109 conversion's `(mode := m)` selects is `{ rounding := m }`. -/
@[simp] theorem context_modeContext (mode : Formats.P3109.RoundingMode) :
    (FloatLib.Floats.ExecFloat.ModeContext.context :
        FloatLib.Floats.ExecFloat.ContextFor (ExecFloat.P3109 format) mode) =
      ({ rounding := mode } : Formats.P3109.ProjectionPolicy) :=
  rfl

end Conversion
end ExecFloat.P3109
end FloatLib.Floats
