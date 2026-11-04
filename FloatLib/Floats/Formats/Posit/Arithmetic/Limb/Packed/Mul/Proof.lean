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

The packed multiplier forms a four-limb product, then normalizes it to two limbs and a sticky
bit. Here we show that its output is a valid posit code that re-encodes to the model-valued
two-limb multiplication. The refinement goes through exact dyadic multiplication and the shared
rounding specification.
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
  refine Boundary.withTwoDyadicFields_toNat_eq_binaryCode heligible left right _ _ ?_
  intro leftNegative leftSignificand leftExponent
    rightNegative rightSignificand rightExponent
  let product :=
    FloatLib.Numerics.FixedWord.mul128
      leftSignificand rightSignificand
  rw [NativeLimbRounding.GuardSticky.roundCodeWord_normalizeJam128_toNat
    format heligible
    (Bool.xor leftNegative rightNegative) product
    (leftExponent + rightExponent),
    ← FloatLib.Numerics.Dyadic.mulFields_eq]
  simp only [product, FloatLib.Numerics.FixedWord.mul128_toNat,
    FloatLib.Numerics.Dyadic.mulFields]

/-- Every direct packed-multiplication result is a valid complete posit encoding. -/
theorem mulCode_lt_modulus
    (heligible : NativeLimb.Eligible format)
    (left right : FloatLib.Numerics.FixedWord.UInt128) :
    (mulCode heligible left right).toNat < format.modulus := by
  rw [mulCode_toNat_eq_decoded]
  exact Boundary.binaryCode_roundCodeNat_lt_modulus heligible
    FloatLib.Numerics.Dyadic.mul _ _

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
  exact Boundary.ofNatBits_binaryCode_roundCodeNat heligible
    FloatLib.Numerics.Dyadic.mul left right hleft hright

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked
