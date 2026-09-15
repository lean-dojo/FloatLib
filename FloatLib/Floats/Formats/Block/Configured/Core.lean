/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.Formats.Block.SharedScale.Core

/-!
# Configured shared-scale block identity

The universal carrier stores one complete vector-valued block. Its lane count remains in the type,
and scale selection remains an explicit operation rather than an inferred scalar policy.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat

/-- A whole rational block with one caller-selected binary exponent. -/
abbrev SharedScale (lanes : Nat) :=
  FloatLib.Floats.ExecFloat (Formats.Block.SharedScale lanes)

end FloatLib.Floats.ExecFloat
