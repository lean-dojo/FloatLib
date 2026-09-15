/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.WordLimb.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.GuardSticky.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Proof

/-!
# Correctness of one-word to two-limb Posit adapters

These lemmas are needed only by operations that cross from `UInt64` storage to a `UInt128`
intermediate. They live at that boundary so the ordinary one-word rounding proof remains
independent of the complete two-limb proof stack.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordLimb

open FloatLib.Numerics

/-- Zero extension preserves the mathematical significand. -/
@[simp] theorem widen_toNat (significand : UInt64) :
    (widen significand).toNat = significand.toNat := by
  simp [widen, FixedWord.UInt128.toNat]

/--
Project a complete two-limb rounding result into the storage word of an eligible one-word format.

The significand may use both input limbs. Eligibility constrains only the final Posit code, so the
result is represented entirely by the low output limb.
-/
theorem roundCodeWordLow_toNat_eq_direct
    (format : Format) (heligible : NativeWord.Eligible format)
    (negative : Bool)
    (significand : FixedWord.UInt128)
    (exponent : Int) :
    (NativeLimbRounding.GuardSticky.roundCodeWord
      format negative significand exponent).lo.toNat =
      DirectDyadicPacking.roundCode format
        { negative
          significand := significand.toNat
          exponent } := by
  let hlimb : NativeLimb.Eligible format :=
    limbEligible format heligible
  let result :=
    NativeLimbRounding.GuardSticky.roundCodeWord
      format negative significand exponent
  have hmodulus :
      format.modulus ≤ 2 ^ 64 :=
    NativeWord.modulus_le_two_pow_64 format heligible
  have hresultModulus :
      result.toNat < format.modulus := by
    rw [NativeLimbRounding.GuardSticky.roundCodeWord_toNat_eq_direct
      format hlimb]
    exact DirectDyadicPacking.roundCode_lt_modulus format _
  have hresult : result.toNat < 2 ^ 64 :=
    hresultModulus.trans_le hmodulus
  change result.lo.toNat =
    DirectDyadicPacking.roundCode format
      { negative
        significand := significand.toNat
        exponent }
  calc
    result.lo.toNat = result.toNat :=
      FixedWord.UInt128.lo_toNat_eq_toNat_of_lt_two_pow result hresult
    _ = DirectDyadicPacking.roundCode format
          { negative
            significand := significand.toNat
            exponent } :=
      NativeLimbRounding.GuardSticky.roundCodeWord_toNat_eq_direct
        format hlimb negative significand exponent

end FloatLib.Floats.Formats.Posit.Model.NativeWordLimb
