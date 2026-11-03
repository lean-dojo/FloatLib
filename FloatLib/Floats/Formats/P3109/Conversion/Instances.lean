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
context. A conversion's `(mode := ...)` option takes a P3109 `RoundingMode` and its
`(context := ...)` option a `SaturationMode`, as in
`x.cast (target := ExecFloat.P3109 .binary8p4se) (mode := .up) (context := .finite)`, and the two
make the projection policy. Context-free conversion selects FloatLib's nearest-even,
no-saturation policy.
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

/--
Conversions into a P3109 destination take a P3109 `RoundingMode`, nearest-even by default, and a
`SaturationMode`: `(mode := m) (context := s)` projects under `{ rounding := m, saturation := s }`.
-/
instance roundingModes :
    FloatLib.Floats.ExecFloat.RoundingModes (ExecFloat.P3109 format) Rat
      Formats.P3109.RoundingMode where
  Policy := Formats.P3109.SaturationMode
  default := .nearest
  withMode rounding saturation := { rounding, saturation }

/--
Context-free P3109 conversion makes no saturation request, so with the default mode it projects
under the default policy `{}`.
-/
instance defaultQuantizer :
    FloatLib.Floats.ExecFloat.DefaultQuantizer
      (ExecFloat.P3109 format) Rat where
  defaultContext := .none

/-- A P3109 conversion with `(mode := m) (context := s)` rounds by `m` and saturates by `s`. -/
@[simp] theorem withMode_eq (mode : Formats.P3109.RoundingMode)
    (saturation : Formats.P3109.SaturationMode) :
    FloatLib.Floats.ExecFloat.RoundingModes.withMode (Destination := ExecFloat.P3109 format)
        mode saturation =
      ({ rounding := mode, saturation } : Formats.P3109.ProjectionPolicy) :=
  rfl

end Conversion
end ExecFloat.P3109
end FloatLib.Floats
