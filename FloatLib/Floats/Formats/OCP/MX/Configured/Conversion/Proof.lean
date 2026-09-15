/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Configured.Conversion.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Runtime

/-!
# Proof contracts for configured OCP MX decoding

OCP MX values reach generic algorithms through the shared `ExactDecoder` capability. The bridge
lemmas below show that decoding an E8M0 scale or a shared-scale block is exactly the corresponding
numerical-system denotation.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.OCP.MX

namespace E8M0.Conversion

/-- The installed decoder is the E8M0 numerical-system denotation. -/
@[simp, grind =] theorem exactDecoder_run (value : ExecFloat.OCP.MX.E8M0) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value =
      Formats.OCP.MX.E8M0.numericalSystem.denote value.toCode :=
  rfl

end E8M0.Conversion

namespace Block.Conversion

variable {format : FloatFormat}

/-- The installed block decoder is the joint block denotation. -/
@[simp, grind =] theorem exactDecoder_run (value : ExecFloat.OCP.MX.Block format) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value =
      (Formats.OCP.MX.blockSystem format).denote value.toCode :=
  rfl

end Block.Conversion

end ExecFloat.OCP.MX
end FloatLib.Floats
