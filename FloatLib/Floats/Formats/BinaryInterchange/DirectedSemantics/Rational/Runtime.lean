/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Deterministic.MagnitudeRounding

/-!
# Low-level rational rounding primitives

Format-independent executable quotient operations support nearest-even and directed rational
rounding. The quotient layer stays below `Model.Arithmetic`, so native arithmetic kernels can
reuse its proofs without an import cycle through the public dispatcher. The ceiling
of a quotient is `Numerics.roundQuotient .up`, shared with every other quotient rounder.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Round a nonnegative quotient to an integer, selecting floor or ceiling. -/
@[inline] def roundQuotDirected (roundUp : Bool) (numerator denominator : Nat) : Nat :=
  if roundUp then Numerics.roundQuotient .up numerator denominator else numerator / denominator

end Model
end FloatLib.Floats.Formats.BinaryInterchange
