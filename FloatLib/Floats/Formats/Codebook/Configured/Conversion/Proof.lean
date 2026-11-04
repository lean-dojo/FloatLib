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

Decoding a configured codebook value is a table lookup. The installed `ExactDecoder` returns the
selected codebook's entry for the word, exceptional entries included.
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
