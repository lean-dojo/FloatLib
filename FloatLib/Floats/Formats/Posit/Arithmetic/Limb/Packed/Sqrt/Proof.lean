/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Sqrt.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Decode.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Boundary.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Direct.Proof

/-!
# Refinement of direct packed-pair posit square root

The packed square-root adapter returns an in-range code and agrees with the shared
width-generic root-prefix kernel after decoding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked

open FloatLib.Numerics

variable {format : Format}

/-- Every direct packed square-root result is a valid complete posit encoding. -/
theorem sqrtCode_lt_modulus
    (value : FloatLib.Numerics.FixedWord.UInt128) :
    sqrtCode (format := format) value < format.modulus := by
  unfold sqrtCode
  apply Boundary.unaryCode_lt
  · exact format.signMaskNat_lt_modulus
  · intro radicand
    by_cases hnegative :
        radicand.isLess FloatLib.Numerics.Dyadic.zero = true
    · rw [if_pos hnegative]
      exact format.signMaskNat_lt_modulus
    · rw [if_neg hnegative]
      exact DirectDyadicSquareRoot.roundCode_lt_modulus
        format radicand

/-- The width-generic square root is the unary boundary shell around the root-prefix rounder. -/
private theorem directSqrt_eq_unaryResult (value : Model format) :
    DirectDyadicArithmetic.sqrt value =
      Boundary.unaryResult (nar format)
        (fun radicand =>
          if radicand.isLess FloatLib.Numerics.Dyadic.zero then
            nar format
          else
            DirectDyadicSquareRoot.round format radicand)
        value.toDyadic? := by
  unfold DirectDyadicArithmetic.sqrt Boundary.unaryResult
  cases value.toDyadic? <;> rfl

/-- Direct packed square root re-encodes to the width-generic root-prefix kernel. -/
theorem ofNatBits_sqrtCode_eq_sqrt
    (heligible : NativeLimb.Eligible format)
    (value : FloatLib.Numerics.FixedWord.UInt128)
    (hvalue : value.toNat < format.modulus) :
    Model.ofNatBits (sqrtCode (format := format) value) =
      DirectDyadicArithmetic.sqrt
        (Model.ofNatBits (format := format) value.toNat) := by
  rw [directSqrt_eq_unaryResult]
  unfold sqrtCode
  apply Boundary.ofNatBits_unaryCode_of_eq
  · exact NativeLimb.toDyadic?_eq_model format value
      heligible hvalue
  · rfl
  · intro radicand
    by_cases hnegative :
        radicand.isLess FloatLib.Numerics.Dyadic.zero = true <;>
      simp [hnegative, DirectDyadicSquareRoot.ofNatBits_roundCode, Model.nar]

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked
