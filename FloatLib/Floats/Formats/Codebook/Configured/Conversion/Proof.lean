/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Configured.Conversion.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Runtime

/-!
# Proof contract for configured codebook decoding

The installed `ExactDecoder` returns the selected codebook's table entry, including exceptional
entries.
-/

@[expose] public section

namespace FloatLib.Floats

namespace ExecFloat.Codebook
namespace Conversion

universe u

variable {width : Nat} {α : Type u} {book : Formats.Codebook width α}

/-- The installed source capability returns the codebook's public decoding result. -/
@[simp, grind =] theorem exactDecoder_run (value : ExecFloat.Codebook book) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value =
      ExecFloat.Codebook.decode value :=
  rfl

end Conversion
end ExecFloat.Codebook
end FloatLib.Floats
