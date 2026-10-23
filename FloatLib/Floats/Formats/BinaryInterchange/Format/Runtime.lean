/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Format.Properties

/-!
# Compiled binary format constants

Layout proofs are easiest to read with powers such as `2 ^ fmt.expWidth`, but compiled code is
better served by left shifts. Frequently used format values therefore have shift-based
implementations, with proved equalities registered for compiler substitution.

Theorems use the mathematical definitions, and compiled code runs the proved shift formulas.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace FloatFormat

/-- Shift-based compiled implementation of `bias`. -/
@[inline] def Internal.bias (fmt : FloatFormat) : Nat :=
  Nat.shiftLeft 1 (fmt.expWidth - 1) - 1

/-- Shift-based compiled implementation of `ieeeMinSubnormalExponent`. -/
@[inline] def Internal.ieeeMinSubnormalExponent (fmt : FloatFormat) : Int :=
  (1 : Int) - Int.ofNat (Internal.bias fmt) - Int.ofNat fmt.fracWidth

/-- Compiled implementation of `normalMantissaExpOffset`. -/
@[inline] def Internal.normalMantissaExpOffset (fmt : FloatFormat) : Nat :=
  fmt.exponentBias + fmt.fracWidth

/-- Shift-based compiled implementation of `ieeeMaxNormalExponent`. -/
@[inline] def Internal.ieeeMaxNormalExponent (fmt : FloatFormat) : Nat :=
  Internal.bias fmt

/-- Shift-based compiled implementation of `ieeeMinNormalExponent`. -/
@[inline] def Internal.ieeeMinNormalExponent (fmt : FloatFormat) : Int :=
  (1 : Int) - Int.ofNat (Internal.bias fmt)

/-- Compiled implementation of `subnormalAlignExp`. -/
@[inline] def Internal.subnormalAlignExp (fmt : FloatFormat) : Nat :=
  fmt.exponentBias + fmt.fracWidth - 1

/-- Shift-based compiled implementation of `expAllOnesNat`. -/
@[inline] def Internal.expAllOnesNat (fmt : FloatFormat) : Nat :=
  Nat.shiftLeft 1 fmt.expWidth - 1

/-- Shift-based compiled implementation of `fracMaskNat`. -/
@[inline] def Internal.fracMaskNat (fmt : FloatFormat) : Nat :=
  Nat.shiftLeft 1 fmt.fracWidth - 1

/-- Shift-based compiled implementation of `expMaskNat`. -/
@[inline] def Internal.expMaskNat (fmt : FloatFormat) : Nat :=
  Nat.shiftLeft (FloatFormat.expAllOnesNat fmt) fmt.fracWidth

/-- Shift-based compiled implementation of `signMaskNat`. -/
@[inline] def Internal.signMaskNat (fmt : FloatFormat) : Nat :=
  Nat.shiftLeft 1 (signBitIndex fmt)

/-- Shift-based compiled implementation of `quietBitNat`. -/
@[inline] def Internal.quietBitNat (fmt : FloatFormat) : Nat :=
  Nat.shiftLeft 1 (fmt.fracWidth - 1)

/-- Compiler substitution of exponent-bias exponentiation by the equivalent shift kernel. -/
@[csimp] theorem bias_eq_internal :
    bias = Internal.bias := by
  funext fmt
  simp [bias, Internal.bias, Nat.shiftLeft_eq]

/-- Compiler substitution for the least-subnormal dyadic exponent. -/
@[csimp] theorem ieeeMinSubnormalExponent_eq_internal :
    ieeeMinSubnormalExponent = Internal.ieeeMinSubnormalExponent := by
  funext fmt
  simp [ieeeMinSubnormalExponent, Internal.ieeeMinSubnormalExponent, bias, Internal.bias,
    Nat.shiftLeft_eq]

/-- Compiler substitution for the normal-significand exponent offset. -/
@[csimp] theorem normalMantissaExpOffset_eq_internal :
    normalMantissaExpOffset = Internal.normalMantissaExpOffset := by
  funext fmt
  rfl

/-- Compiler substitution for the greatest normal unbiased exponent. -/
@[csimp] theorem ieeeMaxNormalExponent_eq_internal :
    ieeeMaxNormalExponent = Internal.ieeeMaxNormalExponent := by
  funext fmt
  simp [ieeeMaxNormalExponent, Internal.ieeeMaxNormalExponent, bias, Internal.bias,
    Nat.shiftLeft_eq]

/-- Compiler substitution for the least normal unbiased exponent. -/
@[csimp] theorem ieeeMinNormalExponent_eq_internal :
    ieeeMinNormalExponent = Internal.ieeeMinNormalExponent := by
  funext fmt
  simp [ieeeMinNormalExponent, Internal.ieeeMinNormalExponent, bias, Internal.bias,
    Nat.shiftLeft_eq]

/-- Compiler substitution for the subnormal alignment exponent. -/
@[csimp] theorem subnormalAlignExp_eq_internal :
    subnormalAlignExp = Internal.subnormalAlignExp := by
  funext fmt
  rfl

/-- Compiler substitution of the all-ones exponent mask by the equivalent shift kernel. -/
@[csimp] theorem expAllOnesNat_eq_internal :
    expAllOnesNat = Internal.expAllOnesNat := by
  funext fmt
  simp [expAllOnesNat, Internal.expAllOnesNat, Nat.shiftLeft_eq]

/-- Compiler substitution of the fraction mask by the equivalent shift kernel. -/
@[csimp] theorem fracMaskNat_eq_internal :
    fracMaskNat = Internal.fracMaskNat := by
  funext fmt
  simp [fracMaskNat, Internal.fracMaskNat, Nat.shiftLeft_eq]

/-- Compiler substitution of the shifted exponent mask by the equivalent shift kernel. -/
@[csimp] theorem expMaskNat_eq_internal :
    expMaskNat = Internal.expMaskNat := by
  funext fmt
  simp [expMaskNat, Internal.expMaskNat, Nat.shiftLeft_eq]

/-- Compiler substitution of the sign mask by the equivalent shift kernel. -/
@[csimp] theorem signMaskNat_eq_internal :
    signMaskNat = Internal.signMaskNat := by
  funext fmt
  simp [signMaskNat, Internal.signMaskNat, Nat.shiftLeft_eq]

/-- Compiler substitution of the quiet-NaN bit by the equivalent shift kernel. -/
@[csimp] theorem quietBitNat_eq_internal :
    quietBitNat = Internal.quietBitNat := by
  funext fmt
  simp [quietBitNat, Internal.quietBitNat, Nat.shiftLeft_eq]

end FloatFormat
end FloatLib.Floats.Formats.BinaryInterchange
