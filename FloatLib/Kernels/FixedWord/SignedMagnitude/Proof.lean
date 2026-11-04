/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.SignedMagnitude.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof

/-!
# Exactness of shared native signed-magnitude arithmetic

Under its capacity hypotheses, the `UInt64` signed-magnitude primitive implements exact dyadic
addition, and it does so for any format. Equal signs need a no-overflow hypothesis. Opposite signs
reduce to an exact difference. The two-limb refinement is in `SignedMagnitude.UInt128.Proof`.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/--
Interpret a native signed magnitude as the canonical exact dyadic used after addition.

Exact cancellation is normalized to positive zero with exponent zero. Nonzero results retain the
common exponent at which their magnitudes were added.
-/
def signedMagnitudeDyadic
    (negative : Bool) (magnitude : UInt64) (exponent : Int) : Dyadic :=
  if magnitude == 0 then
    { negative := false, significand := 0, exponent := 0 }
  else
    { negative, significand := magnitude.toNat, exponent }

/-- Subtracting a strictly smaller native word leaves a nonzero word. -/
private theorem sub_ne_zero_of_lt {small large : UInt64} (h : small < large) :
    large - small ≠ 0 := by
  intro hzero
  have hzeroNat := congrArg UInt64.toNat hzero
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h), UInt64.toNat_zero] at hzeroNat
  have hnatLt := UInt64.lt_iff_toNat_lt.mp h
  omega

/-- A native sum below the word capacity with a nonzero operand is a nonzero word. -/
private theorem add_ne_zero_of_lt {left right : UInt64} (hleft : left.toNat ≠ 0)
    (hsum : left.toNat + right.toNat < 2 ^ 64) :
    left + right ≠ 0 := by
  intro hzero
  have hzeroNat := congrArg UInt64.toNat hzero
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum, UInt64.toNat_zero] at hzeroNat
  omega

/-- Of two distinct native words, the one that is not smaller is larger. -/
private theorem lt_of_not_lt_of_ne {left right : UInt64}
    (hlt : ¬left < right) (hne : left ≠ right) :
    right < left := by
  have hnatNotLt : ¬left.toNat < right.toNat := fun h =>
    hlt (UInt64.lt_iff_toNat_lt.mpr h)
  have hnatNe : left.toNat ≠ right.toNat := fun h =>
    hne (UInt64.toNat_inj.mp h)
  exact UInt64.lt_iff_toNat_lt.mpr (by omega)

/--
A zero magnitude returned by native signed-magnitude addition always has a positive sign.

The no-overflow premise rules out a wrapped same-sign sum. With a nonzero left input, the
remaining zero case is exact cancellation of opposite, equal magnitudes. Some input must be
nonzero: two negative zeros add to a negative zero.
-/
theorem addSignedMagnitudes_sign_eq_false_of_magnitude_eq_zero
    (leftNegative rightNegative : Bool)
    (leftMagnitude rightMagnitude : UInt64)
    (hleft : leftMagnitude ≠ 0)
    (hsum :
      leftNegative = rightNegative →
        leftMagnitude.toNat + rightMagnitude.toNat < 2 ^ 64)
    (hzero :
      (addSignedMagnitudes
        leftNegative rightNegative leftMagnitude rightMagnitude).2 = 0) :
    (addSignedMagnitudes
      leftNegative rightNegative leftMagnitude rightMagnitude).1 = false := by
  have hleftNat : leftMagnitude.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hleft
  cases leftNegative <;> cases rightNegative
  · simp [addSignedMagnitudes]
  · by_cases heq : leftMagnitude = rightMagnitude
    · simp [addSignedMagnitudes, heq]
    · by_cases hlt : leftMagnitude < rightMagnitude
      · exfalso
        exact sub_ne_zero_of_lt hlt
          (by simpa [addSignedMagnitudes, heq, hlt] using hzero)
      · simp [addSignedMagnitudes, heq, hlt]
  · by_cases heq : leftMagnitude = rightMagnitude
    · simp [addSignedMagnitudes, heq]
    · by_cases hlt : leftMagnitude < rightMagnitude
      · simp [addSignedMagnitudes, heq, hlt]
      · exfalso
        exact sub_ne_zero_of_lt (lt_of_not_lt_of_ne hlt heq)
          (by simpa [addSignedMagnitudes, heq, hlt] using hzero)
  · exfalso
    exact add_ne_zero_of_lt hleftNat (hsum rfl)
      (by simpa [addSignedMagnitudes] using hzero)

/--
Native signed-magnitude addition denotes exact dyadic addition at a common exponent.

Only same-sign addition needs the capacity hypothesis, because opposite-sign subtraction can't
overflow. The nonzero hypotheses exclude the input-zero branches, which the format-specific kernels
handle themselves.
-/
theorem signedMagnitudeDyadic_addSignedMagnitudes_eq_addFields
    (leftNegative rightNegative : Bool)
    (leftMagnitude rightMagnitude : UInt64) (exponent : Int)
    (hleft : leftMagnitude ≠ 0) (hright : rightMagnitude ≠ 0)
    (hsum :
      leftNegative = rightNegative →
        leftMagnitude.toNat + rightMagnitude.toNat < 2 ^ 64) :
    signedMagnitudeDyadic
        (addSignedMagnitudes
          leftNegative rightNegative leftMagnitude rightMagnitude).1
        (addSignedMagnitudes
          leftNegative rightNegative leftMagnitude rightMagnitude).2
        exponent =
      Dyadic.addFields
        leftNegative leftMagnitude.toNat exponent
        rightNegative rightMagnitude.toNat exponent := by
  have hleftNat : leftMagnitude.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hleft
  have hrightNat : rightMagnitude.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hright
  rw [Dyadic.addFields_eq]
  by_cases hsign : leftNegative = rightNegative
  · subst rightNegative
    have hadd :
        (leftMagnitude + rightMagnitude).toNat =
          leftMagnitude.toNat + rightMagnitude.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (hsum rfl)]
    rw [Dyadic.add_same_sign_same_exponent _ _ _ _ hleftNat hrightNat]
    simp [addSignedMagnitudes, signedMagnitudeDyadic, hadd, add_ne_zero_of_lt hleftNat (hsum rfl)]
  · by_cases heq : leftMagnitude = rightMagnitude
    · subst rightMagnitude
      rw [Dyadic.add_opposite_sign_same_exponent_eq_zero _ _ _ _ hsign]
      simp [addSignedMagnitudes, signedMagnitudeDyadic, hsign]
    · by_cases hlt : leftMagnitude < rightMagnitude
      · rw [Dyadic.add_opposite_sign_same_exponent_large_right _ _ _ _ _ hsign
          (UInt64.lt_iff_toNat_lt.mp hlt)]
        simp [addSignedMagnitudes, signedMagnitudeDyadic, hsign, heq, hlt,
          sub_ne_zero_of_lt hlt, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hlt)]
      · have hgt := lt_of_not_lt_of_ne hlt heq
        rw [Dyadic.add_opposite_sign_same_exponent_large_left _ _ _ _ _ hsign
          (UInt64.lt_iff_toNat_lt.mp hgt)]
        simp [addSignedMagnitudes, signedMagnitudeDyadic, hsign, heq, hlt,
          sub_ne_zero_of_lt hgt, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hgt)]

end FloatLib.Numerics.FixedWord
