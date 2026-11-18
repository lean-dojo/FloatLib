/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Special
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Sum
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.RoundToIntegral.Real

import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.NearestAwayAgreement
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.ScaledDyadic

/-!
# Kernel path: conversion to integers

`intMagnitude fmt mode a` is the magnitude of the integer that rounds the finite value encoded by
`a` in the direction `mode`, and `intMagnitude_eq` proves that the reference
`Model.roundDyadicToInt` is that magnitude with the sign of the value, for every format
descriptor and every rounding direction.

`roundToIntegral fmt mode a` is the encoding of the value rounded to an integer and kept in the
format, and `roundToIntegral_eq_spec` proves it equal to the encoding of the reference
`Model.roundToIntegral x mode` for every value: finite values, infinities (returned as they are)
and NaNs (quieted).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The quotient of `value` by `2 ^ shift` rounded to a natural number in the direction `mode`, for
a value with sign `sign` (`shiftRound_eq`).
-/
def shiftRound (mode : Model.IEEERoundingMode) (sign value shift : Nat) : Nat :=
  (fun den =>
    (fun q => Nat.add q (roundUp mode sign q (Nat.mod value den) den)) (Nat.div value den))
    (Nat.pow 2 shift)

/-- The integer with magnitude `magnitude` and the sign `negative`. -/
def signedInt (negative : Bool) (magnitude : Nat) : Int :=
  Bool.casesOn (motive := fun _ => Int) negative (Int.ofNat magnitude)
    (Int.neg (Int.ofNat magnitude))

/--
Magnitude of the integer that rounds the finite value encoded by `a` in the direction `mode`
(`intMagnitude_eq`).
-/
def intMagnitude (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) : Nat :=
  (fun sa ua =>
    (fun ha =>
      Nat.shiftLeft
        (shiftRound mode sa (Nat.sub ua (Nat.shiftLeft ha fmt.fracWidth))
          (Nat.sub (Nat.add fmt.exponentBias fmt.fracWidth) (Nat.succ ha)))
        (Nat.sub (Nat.succ ha) (Nat.add fmt.exponentBias fmt.fracWidth)))
      (Nat.sub (Nat.shiftRight ua fmt.fracWidth) 1))
    (Nat.shiftRight a (signPos fmt)) (Nat.land a (magnitudeMask fmt))

/--
Encoding of the value encoded by `a` rounded to an integer in the direction `mode`, in the same
format (`roundToIntegral_eq_spec`). An infinity is returned as it is and a NaN is quieted.
-/
def roundToIntegral (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) : Nat :=
  (fun sa ua =>
    (fun ha =>
      round fmt mode (Nat.add fmt.fracWidth 2) sa sa
        (shiftRound mode sa (Nat.sub ua (Nat.shiftLeft ha fmt.fracWidth))
          (Nat.sub (Nat.add fmt.exponentBias fmt.fracWidth) (Nat.succ ha)))
        (Nat.add (Nat.sub (Nat.succ ha) (Nat.add fmt.exponentBias fmt.fracWidth))
          (Nat.sub (Nat.add fmt.exponentBias fmt.fracWidth) 1))
        0
        (Nat.add (Nat.sub ua (maxFinite fmt)) (Nat.mul (negZeroNaN fmt) (Nat.sub sa ua)))
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nanFlag fmt sa ua) 0)
          (Nat.lor a (quietMask fmt)) a))
      (Nat.sub (Nat.shiftRight ua fmt.fracWidth) 1))
    (Nat.shiftRight a (signPos fmt)) (Nat.land a (magnitudeMask fmt))

/-- `shiftRound` is the reference quotient rounding by a power of two, in every direction. -/
theorem shiftRound_eq (mode : Model.IEEERoundingMode) (negative : Bool) (value shift : Nat) :
    shiftRound mode (signNat negative) value shift =
      Model.Policy.roundQuot mode.toRoundingMode negative 0 value (2 ^ shift) := by
  unfold shiftRound
  simp only [Nat.add_eq, div_def, mod_def, Nat.pow_eq]
  exact roundUp_eq mode negative 0 value (2 ^ shift) (Nat.two_pow_pos shift)

/-- Rounding a quotient by one leaves the value. -/
theorem shiftRound_zero_shift (mode : Model.IEEERoundingMode) (negative : Bool) (value : Nat) :
    shiftRound mode (signNat negative) value 0 = value := by
  rw [shiftRound_eq]
  unfold Model.Policy.roundQuot
  simp [Nat.mod_one]

/-- Zero rounds to zero. -/
theorem shiftRound_zero (mode : Model.IEEERoundingMode) (negative : Bool) (shift : Nat) :
    shiftRound mode (signNat negative) 0 shift = 0 := by
  rw [shiftRound_eq]
  unfold Model.Policy.roundQuot
  simp

/-- A rounded quotient is at most the value plus one. -/
theorem shiftRound_le (mode : Model.IEEERoundingMode) (negative : Bool) (value shift : Nat) :
    shiftRound mode (signNat negative) value shift ≤ value + 1 := by
  rw [shiftRound_eq]
  have hdiv : value / 2 ^ shift ≤ value := Nat.div_le_self _ _
  rcases roundQuot_cases mode negative 0 value (2 ^ shift) with h | ⟨_, h⟩ <;> omega

/-- `signedInt` is the integer that the reference conversions build from a sign and a magnitude. -/
theorem signedInt_eq (negative : Bool) (magnitude : Nat) :
    signedInt negative magnitude =
      if negative then -Int.ofNat magnitude else Int.ofNat magnitude := by
  cases negative <;> rfl

/-- The integer of a dyadic with a nonnegative exponent: its significand shifted left. -/
theorem roundDyadicToInt_ofNat (mode : Model.IEEERoundingMode) (negative : Bool)
    (significand shift : Nat) :
    Model.roundDyadicToInt mode ⟨negative, significand, Int.ofNat shift⟩ =
      signedInt negative (significand <<< shift) := by
  rw [signedInt_eq]
  unfold Model.roundDyadicToInt
  by_cases h0 : significand = 0
  · subst h0
    cases negative <;> simp
  · simp only [beq_iff_eq, h0, ite_false]
    rfl

/-- The integer of a dyadic with a negative exponent: its significand shifted right and rounded. -/
theorem roundDyadicToInt_negSucc (mode : Model.IEEERoundingMode) (negative : Bool)
    (significand shift : Nat) :
    Model.roundDyadicToInt mode ⟨negative, significand, Int.negSucc shift⟩ =
      signedInt negative (shiftRound mode (signNat negative) significand (shift + 1)) := by
  have hden : (2 : Nat) ^ (shift + 1) ≠ 0 := (Nat.two_pow_pos _).ne'
  rw [signedInt_eq]
  unfold Model.roundDyadicToInt
  by_cases h0 : significand = 0
  · subst h0
    rw [shiftRound_zero]
    cases negative <;> simp
  · simp only [beq_iff_eq, h0, ite_false]
    have hcongr : ∀ m m' : Nat, m = m' →
        (if negative then -Int.ofNat m else Int.ofNat m) =
          (if negative then -Int.ofNat m' else Int.ofNat m') := by
      intro m m' h
      rw [h]
    apply hcongr
    rw [shiftRound_eq]
    cases mode
    · change Numerics.roundShiftRightEven significand (shift + 1) = _
      rw [Numerics.roundShiftRightEven_eq_roundQuotientEven]
      exact (Model.Policy.roundQuot_nearest_eq_roundQuotientEven negative 0 _ _ hden).symm
    · change Numerics.roundShiftRight .nearestAway significand (shift + 1) = _
      rw [Numerics.roundShiftRight_eq_roundQuotient]
      exact (Model.Policy.roundQuot_nearestAway_eq_roundQuotient negative 0 _ _ hden).symm
    · change Nat.shiftRight significand (shift + 1) = _
      unfold Model.Policy.roundQuot
      simp [Model.IEEERoundingMode.toRoundingMode, Nat.shiftRight_eq_div_pow]
    · simp only [Numerics.shiftRightRemainder_eq_mod, Nat.shiftRight_eq',
        Nat.shiftRight_eq_div_pow]
      unfold Model.Policy.roundQuot
      by_cases hr : significand % 2 ^ (shift + 1) = 0 <;> cases negative <;>
        simp [Model.IEEERoundingMode.toRoundingMode, hr]
    · simp only [Numerics.shiftRightRemainder_eq_mod, Nat.shiftRight_eq',
        Nat.shiftRight_eq_div_pow]
      unfold Model.Policy.roundQuot
      by_cases hr : significand % 2 ^ (shift + 1) = 0 <;> cases negative <;>
        simp [Model.IEEERoundingMode.toRoundingMode, hr]
    · change Numerics.roundShiftRight .up significand (shift + 1) = _
      rw [Numerics.roundShiftRight_eq_roundQuotient, Numerics.roundQuotient_up_eq]
      unfold Model.Policy.roundQuot
      by_cases hr : significand % 2 ^ (shift + 1) = 0 <;>
        simp [Model.IEEERoundingMode.toRoundingMode, hr]

/--
`intMagnitude` is the magnitude of the reference integer conversion: the integer that rounds a
finite value in the direction `mode` is `intMagnitude` of its encoding with the sign of the
value, for every format descriptor and every rounding direction.
-/
theorem intMagnitude_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x : Model fmt)
    (d : Numerics.Dyadic) (hd : Model.toDyadic? x = some d) :
    Model.roundDyadicToInt mode d =
      signedInt (Model.signBit x) (intMagnitude fmt mode x.toNatBits) := by
  have hfx := Model.fracField_lt_pow2 x
  have hfinite : Model.isFinite x = true := by
    rw [← Model.toDyadic?_isSome_eq_isFinite, hd]
    rfl
  obtain ⟨d', hd', hn, hs, he⟩ := toDyadic?_of_isFinite x hfinite
  obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
  unfold intMagnitude
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.succ_eq_add_one, sign_toNatBits, magnitude_toNatBits, fields_shiftRight _ _ _ hfx,
    fields_sub_shiftLeft]
  obtain ⟨negative, significand, exponent⟩ := d'
  dsimp only at hn hs he
  rw [← hn, ← hs]
  have hsign : (if negative then 1 else 0 : Nat) = signNat negative := rfl
  rw [hsign]
  by_cases h0 : significand = 0
  · subst h0
    rw [shiftRound_zero, Nat.zero_shiftLeft, signedInt_eq]
    unfold Model.roundDyadicToInt
    cases negative <;> simp
  · have hexponent := he h0
    by_cases hle : fmt.exponentBias + fmt.fracWidth ≤ Model.expField x - 1 + 1
    · obtain ⟨left, hleft⟩ : ∃ left,
          Model.expField x - 1 + 1 = fmt.exponentBias + fmt.fracWidth + left :=
        ⟨_, (Nat.add_sub_cancel' hle).symm⟩
      have hexp : exponent = Int.ofNat left := by
        rw [hexponent]
        simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
          Int.ofNat_eq_natCast]
        omega
      have hright : fmt.exponentBias + fmt.fracWidth - (Model.expField x - 1 + 1) = 0 := by
        omega
      have hleft' : Model.expField x - 1 + 1 - (fmt.exponentBias + fmt.fracWidth) = left := by
        omega
      rw [hexp, hright, hleft', shiftRound_zero_shift]
      exact roundDyadicToInt_ofNat mode negative significand left
    · obtain ⟨right, hright⟩ : ∃ right,
          fmt.exponentBias + fmt.fracWidth = Model.expField x - 1 + 1 + (right + 1) :=
        ⟨fmt.exponentBias + fmt.fracWidth - (Model.expField x - 1 + 1) - 1, by omega⟩
      have hexp : exponent = Int.negSucc right := by
        rw [hexponent, Int.negSucc_eq]
        simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
          Int.ofNat_eq_natCast]
        omega
      have hright' :
          fmt.exponentBias + fmt.fracWidth - (Model.expField x - 1 + 1) = right + 1 := by
        omega
      have hleft : Model.expField x - 1 + 1 - (fmt.exponentBias + fmt.fracWidth) = 0 := by
        omega
      rw [hexp, hright', hleft, Nat.shiftLeft_zero]
      exact roundDyadicToInt_negSucc mode negative significand right

/-- The reference integral rounding of a finite value: one rounding of its integer. -/
theorem roundToIntegral_of_finite {fmt : FloatFormat} (mode : Model.IEEERoundingMode)
    (x : Model fmt) (d : Numerics.Dyadic) (hd : Model.toDyadic? x = some d) :
    Model.roundToIntegral x mode =
      if Model.roundDyadicToInt mode d = 0 then Model.zero fmt d.negative
      else Model.Internal.Directed.roundDyadic fmt mode
        (Numerics.Dyadic.ofScaledInt (Model.roundDyadicToInt mode d) 0) := by
  change (Model.Internal.Status.roundToIntegral x mode).value = _
  unfold Model.Internal.Status.roundToIntegral
  rw [Model.exactValue_eq_finite_of_toDyadic?_eq_some hd]
  simp only [beq_iff_eq]

/-- The reference integral rounding returns an infinity as it is and quiets a NaN. -/
theorem roundToIntegral_of_nonFinite {fmt : FloatFormat} (mode : Model.IEEERoundingMode)
    (x : Model fmt) (hfinite : Model.isFinite x = false) :
    (Model.roundToIntegral x mode).toNatBits =
      if Model.isNaN x then x.toNatBits ||| quietMask fmt else x.toNatBits := by
  change (Model.Internal.Status.roundToIntegral x mode).value.toNatBits = _
  unfold Model.Internal.Status.roundToIntegral Model.exactValue
  rw [toDyadic?_eq_none_of_isFinite_eq_false x hfinite]
  cases hnan : Model.isNaN x
  · have hinf : Model.isInfinite x = true := by
      cases hinf : Model.isInfinite x
      · rw [Model.isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x hnan hinf] at hfinite
        exact absurd hfinite (by decide)
      · rfl
    simp [hinf, Model.outcomeWithInvalid]
  · have hinf : Model.isInfinite x = false := by
      cases hinf : Model.isInfinite x
      · rfl
      · have hclass := isNaN_eq_not_isFinite_and_not_isInfinite x
        rw [hnan, hinf] at hclass
        simp at hclass
    simp only [hinf, Bool.false_eq_true, ite_false, ite_true, Model.outcomeWithInvalid]
    exact quietNaN_bits x hnan

/--
`roundToIntegral` computes the encoding of the reference `Model.roundToIntegral x mode`, for
every format descriptor, every rounding direction and every value.
-/
theorem roundToIntegral_eq_spec {fmt : FloatFormat} (mode : Model.IEEERoundingMode)
    (x : Model fmt) :
    roundToIntegral fmt mode x.toNatBits = (Model.roundToIntegral x mode).toNatBits := by
  have hfx := Model.fracField_lt_pow2 x
  have hmagnitude := fun d hd => intMagnitude_eq mode x d hd
  unfold roundToIntegral
  unfold intMagnitude at hmagnitude
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.succ_eq_add_one, Nat.lor_eq, sign_toNatBits, magnitude_toNatBits,
    fields_shiftRight _ _ _ hfx, fields_sub_shiftLeft, nanFlag_eq] at hmagnitude ⊢
  by_cases hguard :
      Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x - maxFinite fmt +
        negZeroNaN fmt * ((if Model.signBit x then 1 else 0) -
          (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x)) = 0
  · have hfinite := isFinite_of_nonFinite_eq_zero x hguard
    obtain ⟨d, hd, hn, hs, _⟩ := toDyadic?_of_isFinite x hfinite
    have hsig := decoded_significand_lt x
    rw [hguard, roundToIntegral_of_finite mode x d hd, hmagnitude d hd, ← hn]
    have hsign : (if d.negative then 1 else 0 : Nat) = signNat d.negative := rfl
    rw [← hs] at hsig ⊢
    rw [hsign]
    generalize Model.expField x - 1 + 1 - (fmt.exponentBias + fmt.fracWidth) = left
    generalize hrounded : shiftRound mode (signNat d.negative) d.significand
      (fmt.exponentBias + fmt.fracWidth - (Model.expField x - 1 + 1)) = rounded
    have hbound : rounded < 2 ^ (fmt.fracWidth + 2) := by
      have hle := shiftRound_le mode d.negative d.significand
        (fmt.exponentBias + fmt.fracWidth - (Model.expField x - 1 + 1))
      rw [hrounded] at hle
      have hpow : 2 ^ (fmt.fracWidth + 2) = 2 * 2 ^ (fmt.fracWidth + 1) := by
        rw [Nat.pow_succ]
        omega
      omega
    have hbias : 1 ≤ fmt.exponentBias + fmt.fracWidth := by
      have := fmt.fracWidth_pos
      omega
    by_cases h0 : rounded = 0
    · subst h0
      have hint : signedInt d.negative (0 <<< left) = 0 := by
        rw [Nat.zero_shiftLeft]
        cases d.negative <;> rfl
      rw [hint, ite_eq_left rfl, ← roundDyadic_zero fmt mode d.negative 0]
      exact round_eq fmt mode _ _ _ _ _ _ _ ⟨d.negative, 0, 0⟩ hbound rfl rfl
        (fun h => absurd rfl h) (fun _ => rfl)
    · have hshift : rounded <<< left ≠ 0 := by
        rw [Nat.shiftLeft_eq]
        exact Nat.mul_ne_zero h0 (Nat.two_pow_pos left).ne'
      have hint : ∀ M : Nat, M ≠ 0 → signedInt d.negative M ≠ 0 := by
        intro M hM
        rw [signedInt_eq]
        exact (Dyadic.signedSignificand_eq_zero ⟨d.negative, M, 0⟩).not.mpr hM
      have hscaled : ∀ M : Nat, M ≠ 0 →
          Numerics.Dyadic.ofScaledInt (signedInt d.negative M) 0 = ⟨d.negative, M, 0⟩ := by
        intro M hM
        rw [signedInt_eq]
        exact Dyadic.ofScaledInt_signedSignificand ⟨d.negative, M, 0⟩ hM
      have hexponent :
          ((left + (fmt.exponentBias + fmt.fracWidth - 1) - left : Nat) : Int) - (0 : Nat) +
            fmt.minSubnormalExponent = 0 := by
        simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
          Int.ofNat_eq_natCast]
        omega
      have hshiftLeft := roundDyadic_shiftLeft fmt mode d.negative rounded
        (left + (fmt.exponentBias + fmt.fracWidth - 1)) 0 left (by omega)
      rw [hexponent] at hshiftLeft
      rw [ite_eq_right (hint _ hshift), hscaled _ hshift, hshiftLeft]
      exact round_eq fmt mode _ _ _ _ _ _ _ _ hbound rfl rfl (fun _ => rfl) (fun _ => rfl)
  · have hfinite : Model.isFinite x = false := by
      change ¬(nonFinite fmt _ _ = 0) at hguard
      simpa only [nonFinite_eq_zero_iff, Bool.not_eq_true] using hguard
    rw [round_guard _ _ _ _ _ _ _ _ _ _ hguard, roundToIntegral_of_nonFinite mode x hfinite]
    cases Model.isNaN x <;> rfl

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
