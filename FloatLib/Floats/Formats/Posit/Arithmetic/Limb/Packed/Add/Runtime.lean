/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.SignedSum.Runtime

/-!
# Direct packed-pair posit addition runtime

Addition uses the shared signed-sum kernel for posits stored in two native limbs. Significands
stay in `UInt128` when alignment and addition fit; larger intermediates use exact dyadic
arithmetic. The result is a two-limb code. Range and refinement proofs are in `Add.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked

open FloatLib.Numerics

variable {format : Format}

/-- Decode two packed operands, add exactly, and return the complete two-limb encoding. -/
@[noinline] def addCode
    (heligible : NativeLimb.Eligible format)
    (left right : FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  SignedSum.addWordsCodeWord heligible left right

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked
