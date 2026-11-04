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

Here the universal carrier holds one whole block, a vector of values with its lane count in the
type. Choosing the scale is an operation you call with an exponent, so the library never infers a
scalar policy for you.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat

/-- A whole rational block with one caller-selected binary exponent. -/
abbrev SharedScale (lanes : Nat) :=
  FloatLib.Floats.ExecFloat (Formats.Block.SharedScale lanes)

end FloatLib.Floats.ExecFloat
