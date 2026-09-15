/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Conversion.Proof

/-!
# P3109 conversion capabilities

The destination quantizer uses the exact rational scalar domain and the existing
`ProjectionPolicy` context. Context-free conversion selects FloatLib's nearest-even,
no-saturation policy explicitly.
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
  defaultContext := Formats.P3109.ProjectionPolicy.nearestEven

end Conversion
end ExecFloat.P3109
end FloatLib.Floats
