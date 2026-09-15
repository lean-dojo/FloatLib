/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Add.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.SignedSum.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Arithmetic.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Boundary.Proof
public import Mathlib.Analysis.Real.Sqrt

/-!
# Refinement of direct packed-pair posit addition

The results below prove encoding range and equality with the representation-independent
two-limb arithmetic kernel.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked

open FloatLib.Numerics

variable {format : Format}

/-- Every direct packed-addition result is a valid complete posit encoding. -/
theorem addCode_lt_modulus
    (heligible : NativeLimb.Eligible format)
    (left right : FloatLib.Numerics.FixedWord.UInt128) :
    (addCode heligible left right).toNat < format.modulus := by
  unfold addCode
  rw [SignedSum.addWordsCodeWord_toNat]
  apply Boundary.binaryCode_lt
  · exact format.signMaskNat_lt_modulus
  · intro leftValue rightValue
    exact NativeLimbRounding.roundCodeNat_lt_modulus
      format heligible
      (FloatLib.Numerics.Dyadic.add leftValue rightValue)

/-- Direct packed addition re-encodes to the model-valued two-limb kernel. -/
theorem ofNatBits_addCode_eq_add
    (heligible : NativeLimb.Eligible format)
    (left right : FloatLib.Numerics.FixedWord.UInt128)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    Model.ofNatBits (addCode heligible left right).toNat =
      NativeLimbArithmetic.add heligible
        (Model.ofNatBits (format := format) left.toNat)
        (Model.ofNatBits (format := format) right.toNat) := by
  unfold addCode NativeLimbArithmetic.add
  rw [SignedSum.addWordsCodeWord_toNat]
  apply Boundary.ofNatBits_binaryCode_of_eq
  · exact NativeLimb.toDyadic?_eq_model format left
      heligible hleft
  · exact NativeLimb.toDyadic?_eq_model format right
      heligible hright
  · rfl
  · intro leftValue rightValue
    exact NativeLimbRounding.ofNatBits_roundCodeNat
      format heligible
      (FloatLib.Numerics.Dyadic.add leftValue rightValue)

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked
