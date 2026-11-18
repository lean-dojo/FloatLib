/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Codecs
public import FloatLib.Numerics.Quantization.Block.Reduction
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Nearest
public import FloatLib.Tactic.ReferencePaths

/-!
# Reduction states for stored block dot products

OCP MX v1.0, §§6.1–6.2, permits implementation choices for intermediate
precision. `Reduction` makes the state, step and final decoder explicit.
Its exact and finite binary instances share the same ordered fold.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Numerics FloatLib.Floats.Formats.BinaryInterchange

namespace Reduction

/--
OCP MX v1.0, §6.1: binary word accumulation with an independently supplied
product projection. Every addition uses the descriptor's nearest-even arithmetic.
-/
def binary (fmt : FloatFormat) (project : NumericalValue Rat → Model fmt) : Reduction where
  State := Model fmt
  initial := Model.zero fmt false
  step sum value := Model.add sum (project value)
  finish sum := (Codec.decodeModel sum).map SignedRat.value

reference_paths run

attribute [kernel_optimize unfold] fold exact binary

end Reduction

end FloatLib.Floats.Formats.Block
