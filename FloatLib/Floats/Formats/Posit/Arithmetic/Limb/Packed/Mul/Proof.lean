/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Mul.Runtime
public import FloatLib.Kernels.FixedWord.Product.Proof
import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Arithmetic.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Boundary.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.Proof
public import Mathlib.Analysis.Real.Sqrt

/-!
# Refinement of direct packed-pair posit multiplication

The packed multiplier forms a four-limb product and normalizes it to two limbs with a sticky
bit. Its output is a valid posit code and re-encodes to the model-valued two-limb multiplication.
The refinement uses exact dyadic multiplication and the shared rounding specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked

open FloatLib.Numerics

variable {format : Format}

private theorem mulCode_toNat_eq_decoded
    (heligible : NativeLimb.Eligible format)
    (left right : FloatLib.Numerics.FixedWord.UInt128) :
    (mulCode heligible left right).toNat =
      Boundary.binaryCode format.signMaskNat
        (fun leftValue rightValue =>
          NativeLimbRounding.roundCodeNat format heligible
            (FloatLib.Numerics.Dyadic.mul leftValue rightValue))
        (NativeLimb.toDyadic? format left)
        (NativeLimb.toDyadic? format right) := by
  unfold mulCode
  rw [NativeLimb.map_withTwoDyadicFields_eq_match_toDyadic?
    FloatLib.Numerics.FixedWord.UInt128.toNat format left right
    (NativeLimb.signMaskWord format)
    (fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      let product :=
        FloatLib.Numerics.FixedWord.mul128
          leftSignificand rightSignificand
      NativeLimbRounding.GuardSticky.roundCodeWord format
        (Bool.xor leftNegative rightNegative)
        product.normalizeJam128
        (leftExponent + rightExponent +
          Int.ofNat product.normalizationShift128))
    (fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      NativeLimbRounding.roundCodeNat format heligible
        (FloatLib.Numerics.Dyadic.mulFields
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent))
    (by
      intro leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent
      let product :=
        FloatLib.Numerics.FixedWord.mul128
          leftSignificand rightSignificand
      rw [NativeLimbRounding.GuardSticky.roundCodeWord_normalizeJam128_toNat
        format heligible
        (Bool.xor leftNegative rightNegative) product
        (leftExponent + rightExponent)]
      simp only [product, FloatLib.Numerics.FixedWord.mul128_toNat,
        FloatLib.Numerics.Dyadic.mulFields]),
    NativeLimb.signMaskWord_toNat format heligible]
  unfold Boundary.binaryCode Boundary.binaryResult
  cases NativeLimb.toDyadic? format left with
  | none => rfl
  | some leftValue =>
      cases NativeLimb.toDyadic? format right with
      | none => rfl
      | some rightValue =>
          simp only
          rw [FloatLib.Numerics.Dyadic.mulFields_eq]

/-- Every direct packed-multiplication result is a valid complete posit encoding. -/
theorem mulCode_lt_modulus
    (heligible : NativeLimb.Eligible format)
    (left right : FloatLib.Numerics.FixedWord.UInt128) :
    (mulCode heligible left right).toNat < format.modulus := by
  rw [mulCode_toNat_eq_decoded]
  apply Boundary.binaryCode_lt
  · exact format.signMaskNat_lt_modulus
  · intro leftValue rightValue
    exact NativeLimbRounding.roundCodeNat_lt_modulus
      format heligible
      (FloatLib.Numerics.Dyadic.mul leftValue rightValue)

/-- Direct packed multiplication re-encodes to the model-valued two-limb kernel. -/
theorem ofNatBits_mulCode_eq_mul
    (heligible : NativeLimb.Eligible format)
    (left right : FloatLib.Numerics.FixedWord.UInt128)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    Model.ofNatBits (mulCode heligible left right).toNat =
      NativeLimbArithmetic.mul heligible
        (Model.ofNatBits (format := format) left.toNat)
        (Model.ofNatBits (format := format) right.toNat) := by
  rw [mulCode_toNat_eq_decoded]
  unfold NativeLimbArithmetic.mul
  apply Boundary.ofNatBits_binaryCode_of_eq
  · exact NativeLimb.toDyadic?_eq_model format left
      heligible hleft
  · exact NativeLimb.toDyadic?_eq_model format right
      heligible hright
  · rfl
  · intro leftValue rightValue
    exact NativeLimbRounding.ofNatBits_roundCodeNat
      format heligible
      (FloatLib.Numerics.Dyadic.mul leftValue rightValue)

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked
