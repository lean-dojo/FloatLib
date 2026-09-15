/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Core.Runtime
public import FloatLib.Kernels.FixedWord.Core.Proof

/-!
# Refinement laws for two-limb posit capacity primitives

The results in this module relate the native two-limb search endpoint to the exact natural-number
encoding used by the posit model.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimb

/-- Conversion of the positive-code endpoint to two native limbs is exact. -/
theorem signMaskWord_toNat (format : Format)
    (heligible : Eligible format) :
    (signMaskWord format).toNat = format.signMaskNat := by
  apply FloatLib.Numerics.FixedWord.UInt128.toNat_ofNat
  unfold Format.signMaskNat Format.signIndex
  apply Nat.pow_lt_pow_right (by decide)
  unfold Eligible at heligible
  omega

/-- Every eligible positive-code endpoint lies at or below bit 127. -/
theorem signMaskNat_le_two_pow_127 (format : Format)
    (heligible : Eligible format) :
    format.signMaskNat ≤ 2 ^ 127 := by
  unfold Format.signMaskNat Format.signIndex
  apply Nat.pow_le_pow_right (by decide)
  unfold Eligible at heligible
  omega

end FloatLib.Floats.Formats.Posit.Model.NativeLimb
