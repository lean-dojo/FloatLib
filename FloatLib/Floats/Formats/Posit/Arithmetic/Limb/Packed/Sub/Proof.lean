/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.SignedSum.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Sub.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Arithmetic.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Boundary.Proof
public import Mathlib.Analysis.Real.Sqrt

/-!
# Refinement of direct packed-pair posit subtraction

The results below prove encoding range and equality with the representation-independent
two-limb arithmetic kernel.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked

open FloatLib.Numerics

variable {format : Format}

/-- Every direct packed-subtraction result is a valid complete posit encoding. -/
theorem subCode_lt_modulus
    (heligible : NativeLimb.Eligible format)
    (left right : FloatLib.Numerics.FixedWord.UInt128) :
    (subCode heligible left right).toNat < format.modulus := by
  unfold subCode
  rw [SignedSum.subWordsCodeWord_toNat]
  apply Boundary.binaryCode_lt
  · exact format.signMaskNat_lt_modulus
  · intro leftValue rightValue
    exact NativeLimbRounding.roundCodeNat_lt_modulus
      format heligible
      (FloatLib.Numerics.Dyadic.sub leftValue rightValue)

/-- Direct packed subtraction re-encodes to the model-valued two-limb kernel. -/
theorem ofNatBits_subCode_eq_sub
    (heligible : NativeLimb.Eligible format)
    (left right : FloatLib.Numerics.FixedWord.UInt128)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    Model.ofNatBits (subCode heligible left right).toNat =
      NativeLimbArithmetic.sub heligible
        (Model.ofNatBits (format := format) left.toNat)
        (Model.ofNatBits (format := format) right.toNat) := by
  unfold subCode NativeLimbArithmetic.sub
  rw [SignedSum.subWordsCodeWord_toNat]
  apply Boundary.ofNatBits_binaryCode_of_eq
  · exact NativeLimb.toDyadic?_eq_model format left
      heligible hleft
  · exact NativeLimb.toDyadic?_eq_model format right
      heligible hright
  · rfl
  · intro leftValue rightValue
    exact NativeLimbRounding.ofNatBits_roundCodeNat
      format heligible
      (FloatLib.Numerics.Dyadic.sub leftValue rightValue)

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked
