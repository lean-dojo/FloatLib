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

Some one-word operations carry an intermediate from `UInt64` storage into a `UInt128`, and these
lemmas cover that crossing and nothing else. Keeping them at the boundary means the ordinary
one-word rounding proof never depends on the complete two-limb proof stack.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordLimb

open FloatLib.Numerics

/-- Zero extension preserves the mathematical significand. -/
@[simp] theorem widen_toNat (significand : UInt64) :
    (widen significand).toNat = significand.toNat := by
  simp [widen, FixedWord.UInt128.toNat]

/-- A two-limb value below an eligible one-word format's modulus lies entirely in its low limb. -/
theorem lo_toNat_eq_toNat_of_lt_modulus
    (format : Format) (heligible : NativeWord.Eligible format)
    {value : FixedWord.UInt128} (hvalue : value.toNat < format.modulus) :
    value.lo.toNat = value.toNat :=
  FixedWord.UInt128.lo_toNat_eq_toNat_of_lt_two_pow value
    (hvalue.trans_le (NativeWord.modulus_le_two_pow_64 format heligible))

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
  have hresult :
      (NativeLimbRounding.GuardSticky.roundCodeWord
        format negative significand exponent).toNat < format.modulus := by
    rw [NativeLimbRounding.GuardSticky.roundCodeWord_toNat_eq_direct
      format (limbEligible format heligible)]
    exact DirectDyadicPacking.roundCode_lt_modulus format _
  rw [lo_toNat_eq_toNat_of_lt_modulus format heligible hresult]
  exact NativeLimbRounding.GuardSticky.roundCodeWord_toNat_eq_direct
    format (limbEligible format heligible) negative significand exponent

end FloatLib.Floats.Formats.Posit.Model.NativeWordLimb
