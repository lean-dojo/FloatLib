/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.SignedSum.Runtime

/-!
# Direct packed-pair posit subtraction runtime

Subtraction flips the sign of the right operand and then runs the shared signed-sum kernel. From
there on it is addition. Significands stay in `UInt128` when alignment and accumulation fit,
larger intermediates use exact dyadic arithmetic, and the result is a two-limb code. `Sub.Proof` has
the range and refinement proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked

open FloatLib.Numerics

variable {format : Format}

/-- Decode two packed operands, subtract exactly, and return the complete two-limb encoding. -/
@[noinline] def subCode
    (heligible : NativeLimb.Eligible format)
    (left right : FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  SignedSum.subWordsCodeWord heligible left right

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked
