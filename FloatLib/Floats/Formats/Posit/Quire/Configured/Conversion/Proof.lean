/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Configured.Conversion.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Runtime

/-!
# Proof contract for configured posit quire decoding

Quire-backed algorithms use the same `ExactDecoder` capability as the other configured formats.
This bridge identifies that generic operation with the quire's complete public decoder; the
equality is definitional and adds no second decoding path.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit.Quire
namespace Conversion

variable {format : Format}

/-- The installed quire source capability is its public complete decoder. -/
@[simp, grind =] theorem exactDecoder_run
    (value : Formats.Posit.Quire.Model format) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value =
      ExecFloat.Posit.Quire.decode value :=
  rfl

end Conversion
end ExecFloat.Posit.Quire
end FloatLib.Floats
