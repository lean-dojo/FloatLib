/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Fma.Runtime
public import FloatLib.Kernels.FixedWord.Product.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Arithmetic.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Boundary.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.Proof
public import Mathlib.Analysis.Real.Sqrt

/-!
# Refinement of direct packed-pair posit fused multiply-add

The packed FMA reads three pair-limb codes, forms the exact product plus addend, and rounds once
without first constructing model wrappers. This file proves the generated code is in range and
re-encodes to the already verified two-limb model operation.

That two-stage argument keeps packed field extraction and carry arithmetic out of the public Posit
specification while retaining the one-rounding FMA guarantee. NaR handling follows the common
packed boundary rather than a private fallback.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked

open FloatLib.Numerics

variable {format : Format}

private theorem fmaCode_eq_decoded
    (heligible : NativeLimb.Eligible format)
    (left right addend : FloatLib.Numerics.FixedWord.UInt128) :
    fmaCode heligible left right addend =
      Boundary.ternaryCode format.signMaskNat
        (fun leftValue rightValue addendValue =>
          NativeLimbRounding.roundCodeNat format heligible
            (FloatLib.Numerics.Dyadic.add
              (FloatLib.Numerics.Dyadic.mul leftValue rightValue)
              addendValue))
        (NativeLimb.toDyadic? format left)
        (NativeLimb.toDyadic? format right)
        (NativeLimb.toDyadic? format addend) := by
  unfold fmaCode Boundary.ternaryCode Boundary.ternaryResult
  simp only [FloatLib.Numerics.FixedWord.mul128_toNat]
  calc
    _ =
        match NativeLimb.toDyadic? format left with
        | none => format.signMaskNat
        | some leftValue =>
            match NativeLimb.toDyadic? format right with
            | none => format.signMaskNat
            | some rightValue =>
                match NativeLimb.toDyadic? format addend with
                | none => format.signMaskNat
                | some addendValue =>
                    NativeLimbRounding.roundCodeNat format heligible
                      (FloatLib.Numerics.Dyadic.addFields
                        (Bool.xor leftValue.negative rightValue.negative)
                        (leftValue.significand * rightValue.significand)
                        (leftValue.exponent + rightValue.exponent)
                        addendValue.negative addendValue.significand addendValue.exponent) :=
      NativeLimb.withThreeDyadicFields_eq_match_toDyadic?
        format left right addend format.signMaskNat
        (fun leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent
            addendNegative addendSignificand addendExponent =>
          NativeLimbRounding.roundCodeNat format heligible
            (FloatLib.Numerics.Dyadic.addFields
              (Bool.xor leftNegative rightNegative)
              (leftSignificand * rightSignificand)
              (leftExponent + rightExponent)
              addendNegative addendSignificand addendExponent))
    _ = _ := by
      cases NativeLimb.toDyadic? format left <;>
        cases NativeLimb.toDyadic? format right <;>
        cases NativeLimb.toDyadic? format addend <;>
        rfl

/-- Every direct packed fused result is a valid complete posit encoding. -/
theorem fmaCode_lt_modulus
    (heligible : NativeLimb.Eligible format)
    (left right addend : FloatLib.Numerics.FixedWord.UInt128) :
    fmaCode heligible left right addend < format.modulus := by
  rw [fmaCode_eq_decoded]
  apply Boundary.ternaryCode_lt
  · exact format.signMaskNat_lt_modulus
  · intro leftValue rightValue addendValue
    exact NativeLimbRounding.roundCodeNat_lt_modulus
      format heligible
      (FloatLib.Numerics.Dyadic.add
        (FloatLib.Numerics.Dyadic.mul leftValue rightValue)
        addendValue)

/-- Direct packed FMA re-encodes to the model-valued two-limb kernel. -/
theorem ofNatBits_fmaCode_eq_fma
    (heligible : NativeLimb.Eligible format)
    (left right addend : FloatLib.Numerics.FixedWord.UInt128)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus)
    (haddend : addend.toNat < format.modulus) :
    Model.ofNatBits (fmaCode heligible left right addend) =
      NativeLimbArithmetic.fma heligible
        (Model.ofNatBits (format := format) left.toNat)
        (Model.ofNatBits (format := format) right.toNat)
        (Model.ofNatBits (format := format) addend.toNat) := by
  rw [fmaCode_eq_decoded]
  unfold NativeLimbArithmetic.fma
  apply Boundary.ofNatBits_ternaryCode_of_eq
  · exact NativeLimb.toDyadic?_eq_model format left
      heligible hleft
  · exact NativeLimb.toDyadic?_eq_model format right
      heligible hright
  · exact NativeLimb.toDyadic?_eq_model format addend
      heligible haddend
  · rfl
  · intro leftValue rightValue addendValue
    exact NativeLimbRounding.ofNatBits_roundCodeNat
      format heligible
      (FloatLib.Numerics.Dyadic.add
        (FloatLib.Numerics.Dyadic.mul leftValue rightValue)
        addendValue)

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked
