/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Boundary.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Decode.Runtime

/-!
# Direct packed-pair posit square-root runtime

The packed-pair square-root kernel returns posit codes for configured values stored in two
native limbs. Range and semantic refinement proofs live in `Sqrt.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked

open FloatLib.Numerics

variable {format : Format}

/-- Decode one packed operand, take its exact rounded square root, and return the result code. -/
@[noinline] def sqrtCode
    (value : FloatLib.Numerics.FixedWord.UInt128) : Nat :=
  Boundary.unaryCode format.signMaskNat
    (fun radicand =>
      if radicand.isLess FloatLib.Numerics.Dyadic.zero then
        format.signMaskNat
      else
        DirectDyadicSquareRoot.roundCode format radicand)
    (NativeLimb.toDyadic? format value)

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked
