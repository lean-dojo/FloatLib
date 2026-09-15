/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Difference.Proof
public import FloatLib.Kernels.FixedWord.Product.Proof
public import FloatLib.Kernels.FixedWord.SignedMagnitude.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof

/-!
# Exactness of two-limb signed-magnitude arithmetic

Two-limb signed-magnitude addition has an exact-dyadic refinement through `UInt128`. The proof
factors execution through a signed integer coefficient, so carrier arithmetic and exact-dyadic
semantics meet at one small, representation-independent boundary.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/-- Convert a sign and natural magnitude into its signed integer coefficient. -/
private def signedCoefficient (negative : Bool) (magnitude : Nat) : Int :=
  if negative then
    -Int.ofNat magnitude
  else
    Int.ofNat magnitude

/-- Build a common-exponent dyadic while canonicalizing exact cancellation. -/
private def canonicalScaledInt (coefficient : Int) (exponent : Int) : Dyadic :=
  if coefficient == 0 then
    Dyadic.zero
  else
    Dyadic.ofScaledInt coefficient exponent

/--
Interpret a two-limb signed magnitude as the canonical exact dyadic used after addition.

Exact cancellation is normalized to positive zero with exponent zero. Nonzero results retain the
common exponent at which their magnitudes were combined.
-/
def signedMagnitudeDyadic128
    (negative : Bool) (magnitude : UInt128) (exponent : Int) : Dyadic :=
  let coefficient :=
    if negative then
      -Int.ofNat magnitude.toNat
    else
      Int.ofNat magnitude.toNat
  if coefficient == 0 then
    Dyadic.zero
  else
    Dyadic.ofScaledInt coefficient exponent

/-- A nonzero signed natural coefficient has its direct dyadic fields. -/
private theorem canonicalScaledInt_signedCoefficient_eq_of_ne_zero
    (negative : Bool) (magnitude : Nat) (exponent : Int)
    (hnonzero : magnitude ≠ 0) :
    canonicalScaledInt (signedCoefficient negative magnitude) exponent =
      {
        negative
        significand := magnitude
        exponent
      } := by
  cases negative with
  | false =>
      simp [canonicalScaledInt, signedCoefficient, Dyadic.ofScaledInt,
        hnonzero]
  | true =>
      have hpositive : 0 < magnitude :=
        Nat.pos_of_ne_zero hnonzero
      simp [canonicalScaledInt, signedCoefficient, Dyadic.ofScaledInt,
        hnonzero, hpositive]

/--
A nonzero two-limb signed magnitude has the direct dyadic fields expected by downstream
rounding. Keeping this interpretation theorem next to the representation prevents arithmetic
clients from depending on the integer encoding used internally.
-/
theorem signedMagnitudeDyadic128_eq_of_toNat_ne_zero
    (negative : Bool) (magnitude : UInt128) (exponent : Int)
    (hnonzero : magnitude.toNat ≠ 0) :
    signedMagnitudeDyadic128 negative magnitude exponent =
      {
        negative
        significand := magnitude.toNat
        exponent
      } := by
  change
    canonicalScaledInt
        (signedCoefficient negative magnitude.toNat) exponent =
      _
  exact canonicalScaledInt_signedCoefficient_eq_of_ne_zero
    negative magnitude.toNat exponent hnonzero

/-- Same-exponent dyadic addition is canonical signed-integer addition. -/
private theorem addFields_sameExponent_eq_canonicalScaledInt
    (leftNegative rightNegative : Bool)
    (leftMagnitude rightMagnitude : Nat) (exponent : Int)
    (hleft : leftMagnitude ≠ 0) (hright : rightMagnitude ≠ 0) :
    Dyadic.addFields
        leftNegative leftMagnitude exponent
        rightNegative rightMagnitude exponent =
      canonicalScaledInt
        (signedCoefficient leftNegative leftMagnitude +
          signedCoefficient rightNegative rightMagnitude)
        exponent := by
  cases leftNegative <;> cases rightNegative
  · have hpositive :
        0 < (leftMagnitude : Int) + rightMagnitude := by
      exact_mod_cast Nat.add_pos_left (Nat.pos_of_ne_zero hleft) rightMagnitude
    simp [Dyadic.addFields, canonicalScaledInt, signedCoefficient,
      Dyadic.ofScaledInt, hleft, hright, ne_of_gt hpositive,
      Int.not_lt.mpr hpositive.le]
  · simp [Dyadic.addFields, canonicalScaledInt, signedCoefficient,
      Dyadic.ofScaledInt, hleft, hright]
    split <;> rfl
  · simp [Dyadic.addFields, canonicalScaledInt, signedCoefficient,
      Dyadic.ofScaledInt, hleft, hright]
    split <;> rfl
  · have hnegative :
        -(leftMagnitude : Int) + -(rightMagnitude : Int) < 0 := by
      have hpositive : 0 < leftMagnitude + rightMagnitude :=
        Nat.add_pos_left (Nat.pos_of_ne_zero hleft) rightMagnitude
      omega
    simp [Dyadic.addFields, canonicalScaledInt, signedCoefficient,
      Dyadic.ofScaledInt, hleft, hright, ne_of_lt hnegative, hnegative]

/--
The native two-limb operation returns the exact sum of its signed integer coefficients.

Only same-sign addition needs a capacity premise. Opposite-sign subtraction is bounded by the
larger input magnitude.
-/
private theorem addSignedMagnitudes128_signedCoefficient
    (leftNegative rightNegative : Bool)
    (leftMagnitude rightMagnitude : UInt128)
    (hsum :
      leftNegative = rightNegative →
        leftMagnitude.toNat + rightMagnitude.toNat < 2 ^ 128) :
    signedCoefficient
        (addSignedMagnitudes128
          leftNegative rightNegative leftMagnitude rightMagnitude).1
        (addSignedMagnitudes128
          leftNegative rightNegative leftMagnitude rightMagnitude).2.toNat =
      signedCoefficient leftNegative leftMagnitude.toNat +
        signedCoefficient rightNegative rightMagnitude.toNat := by
  cases leftNegative <;> cases rightNegative
  · have hadd :=
      add128_value_toNat_of_lt
        leftMagnitude rightMagnitude (hsum rfl)
    simp [addSignedMagnitudes128, signedCoefficient, hadd]
  · by_cases hequal : leftMagnitude = rightMagnitude
    · subst rightMagnitude
      simp [addSignedMagnitudes128, signedCoefficient,
        UInt128.toNat]
    · by_cases hless :
        UInt128.less leftMagnitude rightMagnitude = true
      · have hnatLess : leftMagnitude.toNat < rightMagnitude.toNat :=
          (UInt128.less_eq_true_iff leftMagnitude rightMagnitude).mp hless
        have hsub :
            (UInt128.sub rightMagnitude leftMagnitude).toNat =
              rightMagnitude.toNat - leftMagnitude.toNat :=
          UInt128.sub_toNat rightMagnitude leftMagnitude hnatLess.le
        simp [addSignedMagnitudes128, signedCoefficient,
          hequal, hless, hsub]
        omega
      · have hnotLess : ¬leftMagnitude.toNat < rightMagnitude.toNat := by
          intro h
          exact hless
            ((UInt128.less_eq_true_iff leftMagnitude rightMagnitude).mpr h)
        have hnatNe : leftMagnitude.toNat ≠ rightMagnitude.toNat := by
          intro h
          exact hequal (UInt128.toNat_injective h)
        have hnatLess : rightMagnitude.toNat < leftMagnitude.toNat := by
          omega
        have hsub :
            (UInt128.sub leftMagnitude rightMagnitude).toNat =
              leftMagnitude.toNat - rightMagnitude.toNat :=
          UInt128.sub_toNat leftMagnitude rightMagnitude hnatLess.le
        simp [addSignedMagnitudes128, signedCoefficient,
          hequal, hless, hsub]
        omega
  · by_cases hequal : leftMagnitude = rightMagnitude
    · subst rightMagnitude
      simp [addSignedMagnitudes128, signedCoefficient,
        UInt128.toNat]
    · by_cases hless :
        UInt128.less leftMagnitude rightMagnitude = true
      · have hnatLess : leftMagnitude.toNat < rightMagnitude.toNat :=
          (UInt128.less_eq_true_iff leftMagnitude rightMagnitude).mp hless
        have hsub :
            (UInt128.sub rightMagnitude leftMagnitude).toNat =
              rightMagnitude.toNat - leftMagnitude.toNat :=
          UInt128.sub_toNat rightMagnitude leftMagnitude hnatLess.le
        simp [addSignedMagnitudes128, signedCoefficient,
          hequal, hless, hsub]
        omega
      · have hnotLess : ¬leftMagnitude.toNat < rightMagnitude.toNat := by
          intro h
          exact hless
            ((UInt128.less_eq_true_iff leftMagnitude rightMagnitude).mpr h)
        have hnatNe : leftMagnitude.toNat ≠ rightMagnitude.toNat := by
          intro h
          exact hequal (UInt128.toNat_injective h)
        have hnatLess : rightMagnitude.toNat < leftMagnitude.toNat := by
          omega
        have hsub :
            (UInt128.sub leftMagnitude rightMagnitude).toNat =
              leftMagnitude.toNat - rightMagnitude.toNat :=
          UInt128.sub_toNat leftMagnitude rightMagnitude hnatLess.le
        simp [addSignedMagnitudes128, signedCoefficient,
          hequal, hless, hsub]
        omega
  · have hadd :=
      add128_value_toNat_of_lt
        leftMagnitude rightMagnitude (hsum rfl)
    simp [addSignedMagnitudes128, signedCoefficient, hadd, add_comm]

/--
Two-limb signed-magnitude addition denotes exact dyadic addition at a common exponent.

The hypotheses use the mathematical carrier view directly, avoiding representation-specific
zero lemmas at every caller.
-/
theorem signedMagnitudeDyadic128_addSignedMagnitudes128_eq_addFields
    (leftNegative rightNegative : Bool)
    (leftMagnitude rightMagnitude : UInt128) (exponent : Int)
    (hleft : leftMagnitude.toNat ≠ 0)
    (hright : rightMagnitude.toNat ≠ 0)
    (hsum :
      leftNegative = rightNegative →
        leftMagnitude.toNat + rightMagnitude.toNat < 2 ^ 128) :
    signedMagnitudeDyadic128
        (addSignedMagnitudes128
          leftNegative rightNegative leftMagnitude rightMagnitude).1
        (addSignedMagnitudes128
          leftNegative rightNegative leftMagnitude rightMagnitude).2
        exponent =
      Dyadic.addFields
        leftNegative leftMagnitude.toNat exponent
        rightNegative rightMagnitude.toNat exponent := by
  change
    canonicalScaledInt
        (signedCoefficient
          (addSignedMagnitudes128
            leftNegative rightNegative leftMagnitude rightMagnitude).1
          (addSignedMagnitudes128
            leftNegative rightNegative leftMagnitude rightMagnitude).2.toNat)
        exponent =
      _
  rw [addSignedMagnitudes128_signedCoefficient
    leftNegative rightNegative leftMagnitude rightMagnitude hsum]
  exact
    (addFields_sameExponent_eq_canonicalScaledInt
      leftNegative rightNegative
      leftMagnitude.toNat rightMagnitude.toNat exponent
      hleft hright).symm

end FloatLib.Numerics.FixedWord
