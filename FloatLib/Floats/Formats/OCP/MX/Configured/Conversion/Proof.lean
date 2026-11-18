/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Executable.Conversion.Runtime
public import FloatLib.Floats.Formats.OCP.MX.Configured.Conversion.Runtime

/-!
# Proof contract for configured E8M0 decoding

Generic algorithms see an E8M0 scale through the shared `ExactDecoder` capability. The bridge lemma
below shows that decoding it gives the same result as its numerical-system denotation.
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

end ExecFloat.OCP.MX
end FloatLib.Floats
