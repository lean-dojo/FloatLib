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

Quire-backed algorithms reach the quire through the same `ExactDecoder` capability that the other
configured formats use. This bridge shows that the generic operation is the quire's full public
decoder, and since that equality is definitional there is no second decoding path.
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
