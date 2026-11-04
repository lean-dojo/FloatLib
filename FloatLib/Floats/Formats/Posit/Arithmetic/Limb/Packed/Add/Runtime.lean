/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.SignedSum.Runtime

/-!
# Direct packed-pair posit addition runtime

For posits stored in two native limbs, addition goes through the shared signed-sum kernel and
returns a two-limb code. Significands stay in `UInt128` as long as alignment and addition fit
there, and larger intermediates switch to exact dyadic arithmetic. Range and refinement proofs are
in `Add.Proof`.
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
