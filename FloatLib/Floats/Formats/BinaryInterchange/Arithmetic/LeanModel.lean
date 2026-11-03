/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Special
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Accuracy.Proof

/-!
# Agreement with Lean's floating-point arithmetic

`Model` retains IEEE NaN payloads, while Lean's `UnpackedFloat` has a single canonical NaN.
The bridges in this module therefore compare the real semantics of finite results for descriptors
satisfying `fmt.isIEEE = true`. They connect Lean's arithmetic algorithms to the same independent
`roundAt` specification used for `Model`, without identifying representation policies that
deliberately differ.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model.UnpackedFloat
open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

/--
Packing Lean's rounder on a signed natural magnitude has the nearest-even real semantics of the
signed magnitude whenever the packed result is finite.
-/
private theorem toReal_ofModel_round_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (mantissa : Nat) (exponent : Int)
    (hfinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.round (FloatFormat.toModel fmt) sign mantissa exponent)) =
        true) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.round (FloatFormat.toModel fmt) sign mantissa exponent)) =
      roundAt fmt
        ((if modelSignBit sign then (-1 : Real) else 1) *
          ((mantissa : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent)) := by
  let d : Numerics.Dyadic :=
    { negative := modelSignBit sign, significand := mantissa, exponent := exponent }
  have hround :
      ofModel fmt
          (Float.Model.UnpackedFloat.round (FloatFormat.toModel fmt) sign mantissa exponent) =
        roundDyadic fmt d := by
    cases sign <;> simp [roundDyadic, hfmt, ieeeRoundDyadic, d, modelSign, modelSignBit]
  rw [hround] at hfinite ⊢
  rw [toReal_roundDyadic_eq_roundAt fmt hfmt d hfinite]
  congr 1
  cases sign <;>
    simp [d, modelSignBit, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
      FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/--
Packing Lean's signed-integer normalizer has the independent nearest-even real semantics.
The zero sign is intentionally absent from the conclusion because both signed zeros denote zero.
-/
theorem toReal_ofModel_normalize_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mantissa : Int) (exponent : Int) (zeroSign : Sign)
    (hfinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.normalize
            (FloatFormat.toModel fmt) mantissa exponent zeroSign)) = true) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.normalize
            (FloatFormat.toModel fmt) mantissa exponent zeroSign)) =
      roundAt fmt
        ((mantissa : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent) := by
  unfold Float.Model.UnpackedFloat.normalize
  split <;> rename_i hcompare
  · have hnegative : mantissa < 0 := Int.compare_eq_lt.mp hcompare
    simp only [Float.Model.UnpackedFloat.normalize, hcompare] at hfinite
    rw [toReal_ofModel_round_eq_roundAt fmt hfmt .negative _ exponent hfinite]
    congr 1
    have hcast : (((-mantissa).toNat : Nat) : Real) = -(mantissa : Real) := by
      exact_mod_cast (Int.toNat_of_nonneg (by omega) : (Int.ofNat (-mantissa).toNat) = -mantissa)
    simp only [modelSignBit, ite_true, hcast]
    ring
  · have hzero : mantissa = 0 := Int.compare_eq_eq.mp hcompare
    subst mantissa
    rw [toReal_ofModel_zero fmt (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt),
      Int.cast_zero, zero_mul, roundAt_zero]
  · have hpositive : 0 < mantissa := Int.compare_eq_gt.mp hcompare
    simp only [Float.Model.UnpackedFloat.normalize, hcompare] at hfinite
    rw [toReal_ofModel_round_eq_roundAt fmt hfmt .positive _ exponent hfinite]
    congr 1
    have hcast : (mantissa.toNat : Real) = (mantissa : Real) := by
      exact_mod_cast (Int.toNat_of_nonneg hpositive.le : (Int.ofNat mantissa.toNat) = mantissa)
    simp only [modelSignBit, Bool.false_eq_true, ite_false, one_mul, hcast]

/-- Casting a left shift to the reals multiplies by the matching power of two. -/
private theorem natCast_shiftLeft_eq_mul_bpow (mantissa shift : Nat) :
    ((mantissa <<< shift : Nat) : Real) =
      (mantissa : Real) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (shift : Int) := by
  rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow]
  simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/--
Lean's exponent-decreasing alignment to a target at most the exponent lands on that target and
changes only the integer representation of the value.
-/
private theorem decreaseExponent_value_of_le
    (mantissa : Nat) {exponent targetExponent : Int} (hle : targetExponent ≤ exponent) :
    ((Float.Model.UnpackedFloat.decreaseExponent mantissa exponent targetExponent).1 : Real) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix targetExponent =
      (mantissa : Real) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent := by
  have hshift : ((exponent - targetExponent).toNat : Int) = exponent - targetExponent :=
    Int.toNat_of_nonneg (by omega)
  simp only [Float.Model.UnpackedFloat.decreaseExponent]
  rw [natCast_shiftLeft_eq_mul_bpow, mul_assoc, ← FloatLib.Floats.Formats.Flocq.bpow.add_exp,
    hshift]
  congr 2
  ring

private theorem cast_sign_apply (sign : Sign) (mantissa : Nat) :
    ((sign.apply mantissa : Int) : Real) =
      (if modelSignBit sign then (-1 : Real) else 1) * mantissa := by
  cases sign <;> simp [Float.Model.UnpackedFloat.Sign.apply]

/-- Lean's remainder classification locates the exact quotient relative to the integer quotient. -/
theorem accuracyRepresents_accuracyOfFraction
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    accuracyRepresents (numerator / denominator)
      (accuracyOfFraction (numerator % denominator) denominator)
      ((numerator : Real) / denominator) := by
  have hdenominatorPos : (0 : Real) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  have hremainderLt : ((numerator % denominator : Nat) : Real) < denominator := by
    exact_mod_cast Nat.mod_lt numerator (Nat.pos_of_ne_zero hdenominator)
  have hsplit :
      (numerator : Real) / denominator =
        ((numerator / denominator : Nat) : Real) +
          ((numerator % denominator : Nat) : Real) / denominator := by
    simpa only [Int.floor_div_natCast, Int.floor_natCast, ← Int.natCast_ediv,
      Int.cast_natCast, Int.fract_div_natCast_eq_div_natCast_mod] using
      (Int.floor_add_fract ((numerator : ℝ) / denominator)).symm
  unfold accuracyOfFraction
  rw [hsplit]
  split_ifs with hremainder
  · simp [accuracyRepresents, hremainder]
  have hremainderPos : (0 : Real) < (numerator % denominator : Nat) := by
    exact_mod_cast Nat.pos_of_ne_zero hremainder
  have hfractionLt : ((numerator % denominator : Nat) : Real) / denominator < 1 :=
    (div_lt_one hdenominatorPos).2 hremainderLt
  rcases hcompare : compare (2 * (numerator % denominator)) denominator with _ | _ | _
  · rw [Nat.compare_eq_lt] at hcompare
    have hcompareReal : (2 : Real) * (numerator % denominator : Nat) < denominator := by
      exact_mod_cast hcompare
    exact ⟨by linarith [div_pos hremainderPos hdenominatorPos],
      by linarith [(div_lt_iff₀ hdenominatorPos).2 (by linarith :
        ((numerator % denominator : Nat) : Real) < 1 / 2 * denominator)]⟩
  · rw [Nat.compare_eq_eq] at hcompare
    have hcompareReal : (2 : Real) * (numerator % denominator : Nat) = denominator := by
      exact_mod_cast hcompare
    show _ = _ + 1 / 2
    rw [← hcompareReal, mul_comm, ← div_div, div_self hremainderPos.ne']
  · rw [Nat.compare_eq_gt] at hcompare
    have hcompareReal : (denominator : Real) < 2 * (numerator % denominator : Nat) := by
      exact_mod_cast hcompare
    exact ⟨by linarith [(lt_div_iff₀ hdenominatorPos).2 (by linarith :
        1 / 2 * (denominator : Real) < (numerator % denominator : Nat))],
      by linarith⟩

/--
For finite operands and a finite result, Lean core's unpacked addition has the same independent
nearest-even real semantics as `Model.add`.
-/
theorem toReal_ofModel_add_finite_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign₁ sign₂ : Sign)
    (mantissa₁ mantissa₂ : Nat)
    (exponent₁ exponent₂ : Int)
    (hmantissa₁ : 0 < mantissa₁)
    (hmantissa₂ : 0 < mantissa₂)
    (hfinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.add (FloatFormat.toModel fmt)
            (.finite sign₁ mantissa₁ exponent₁ hmantissa₁)
            (.finite sign₂ mantissa₂ exponent₂ hmantissa₂))) = true) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.add (FloatFormat.toModel fmt)
            (.finite sign₁ mantissa₁ exponent₁ hmantissa₁)
            (.finite sign₂ mantissa₂ exponent₂ hmantissa₂))) =
      roundAt fmt
        (unpackedToReal (.finite sign₁ mantissa₁ exponent₁ hmantissa₁) +
          unpackedToReal (.finite sign₂ mantissa₂ exponent₂ hmantissa₂)) := by
  let smallerExponent := min exponent₁ exponent₂
  let decreased₁ :=
    Float.Model.UnpackedFloat.decreaseExponent mantissa₁ exponent₁ smallerExponent
  let decreased₂ :=
    Float.Model.UnpackedFloat.decreaseExponent mantissa₂ exponent₂ smallerExponent
  let signedMantissa :=
    sign₁.apply decreased₁.1 + sign₂.apply decreased₂.1
  change
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.normalize
            (FloatFormat.toModel fmt) signedMantissa smallerExponent .positive)) =
      roundAt fmt
        (unpackedToReal (.finite sign₁ mantissa₁ exponent₁ hmantissa₁) +
          unpackedToReal (.finite sign₂ mantissa₂ exponent₂ hmantissa₂))
  rw [toReal_ofModel_normalize_eq_roundAt
    fmt hfmt signedMantissa smallerExponent .positive hfinite]
  congr 1
  have hdecreased₁ :
      (decreased₁.1 : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix smallerExponent =
        (mantissa₁ : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent₁ :=
    decreaseExponent_value_of_le mantissa₁ (min_le_left _ _)
  have hdecreased₂ :
      (decreased₂.1 : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix smallerExponent =
        (mantissa₂ : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent₂ :=
    decreaseExponent_value_of_le mantissa₂ (min_le_right _ _)
  simp only [signedMantissa, Int.cast_add, cast_sign_apply, add_mul,
    unpackedToReal_finite]
  rw [mul_assoc, hdecreased₁, mul_assoc, hdecreased₂]
  ring

/--
For finite operands satisfying Lean core's documented `roundWithAccuracy` precondition, unpacked
multiplication has the same independent nearest-even real semantics as `Model.mul`.
-/
theorem toReal_ofModel_mul_finite_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign₁ sign₂ : Sign)
    (mantissa₁ mantissa₂ : Nat)
    (exponent₁ exponent₂ : Int)
    (hmantissa₁ : 0 < mantissa₁)
    (hmantissa₂ : 0 < mantissa₂)
    (hle : exponent₁ + exponent₂ ≤
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent (mantissa₁ * mantissa₂)
          (exponent₁ + exponent₂)))
    (hfinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.mul (FloatFormat.toModel fmt)
            (.finite sign₁ mantissa₁ exponent₁ hmantissa₁)
            (.finite sign₂ mantissa₂ exponent₂ hmantissa₂))) = true) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.mul (FloatFormat.toModel fmt)
            (.finite sign₁ mantissa₁ exponent₁ hmantissa₁)
            (.finite sign₂ mantissa₂ exponent₂ hmantissa₂))) =
      roundAt fmt
        (unpackedToReal (.finite sign₁ mantissa₁ exponent₁ hmantissa₁) *
          unpackedToReal (.finite sign₂ mantissa₂ exponent₂ hmantissa₂)) := by
  have haccuracy :
      accuracyRepresents (mantissa₁ * mantissa₂) .exact
        ((mantissa₁ : Real) * mantissa₂) := by
    simp [accuracyRepresents]
  have hround :=
    toReal_ofModel_roundWithAccuracy_eq_roundAt
      fmt hfmt (sign₁ * sign₂) (mantissa₁ * mantissa₂)
      (exponent₁ + exponent₂) .exact
      ((mantissa₁ : Real) * mantissa₂)
      haccuracy hle hfinite
  change
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.roundWithAccuracy
            (FloatFormat.toModel fmt) (sign₁ * sign₂)
            (mantissa₁ * mantissa₂) (exponent₁ + exponent₂) .exact)) =
      _
  rw [hround]
  congr 1
  rw [FloatLib.Floats.Formats.Flocq.bpow.add_exp]
  cases sign₁ <;> cases sign₂ <;>
    simp [unpackedToReal_finite, modelSignBit] <;> ring

/--
The real quotient of two finite unpacked values is the value certified by Lean's division kernel:
the numerator shifted to a target exponent at most `exponent₁ - exponent₂`, over the divisor,
scaled back by the target exponent and signed by the quotient sign.
-/
theorem unpackedToReal_div_eq_shifted_quotient
    (sign₁ sign₂ : Sign) (mantissa₁ mantissa₂ : Nat) (exponent₁ exponent₂ targetExponent : Int)
    (hmantissa₁ : 0 < mantissa₁) (hmantissa₂ : 0 < mantissa₂)
    (htargetLe : targetExponent ≤ exponent₁ - exponent₂) :
    unpackedToReal (.finite sign₁ mantissa₁ exponent₁ hmantissa₁) /
        unpackedToReal (.finite sign₂ mantissa₂ exponent₂ hmantissa₂) =
      (if modelSignBit (sign₁ / sign₂) then (-1 : Real) else 1) *
        (((mantissa₁ <<< (exponent₁ - exponent₂ - targetExponent).toNat : Nat) : Real) /
            mantissa₂ *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix targetExponent) := by
  have hshift :
      ((exponent₁ - exponent₂ - targetExponent).toNat : Int) =
        exponent₁ - exponent₂ - targetExponent :=
    Int.toNat_of_nonneg (sub_nonneg.mpr htargetLe)
  have hscale :
      (((mantissa₁ <<< (exponent₁ - exponent₂ - targetExponent).toNat : Nat) : Real) /
            mantissa₂) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix targetExponent =
        ((mantissa₁ : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent₁) /
          ((mantissa₂ : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent₂) := by
    have hmantissa₂Real : (mantissa₂ : Real) ≠ 0 := by
      exact_mod_cast hmantissa₂.ne'
    have hbpow₂ :
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent₂ ≠ 0 :=
      FloatLib.Floats.Formats.Flocq.bpow.ne_zero _ _
    rw [natCast_shiftLeft_eq_mul_bpow, div_mul_eq_mul_div, mul_assoc,
      ← FloatLib.Floats.Formats.Flocq.bpow.add_exp, hshift,
      show exponent₁ - exponent₂ - targetExponent + targetExponent = exponent₁ - exponent₂ by
        ring,
      FloatLib.Floats.Formats.Flocq.bpow.sub_exp]
    field_simp
  rw [hscale]
  cases sign₁ <;> cases sign₂ <;>
    simp [unpackedToReal_finite, modelSignBit, neg_div, div_neg,
      show Sign.negative / Sign.negative = Sign.positive from rfl,
      show Sign.negative / Sign.positive = Sign.negative from rfl,
      show Sign.positive / Sign.negative = Sign.negative from rfl,
      show Sign.positive / Sign.positive = Sign.positive from rfl]

/--
For nonzero mantissas, the provisional quotient and exponent returned by Lean's `divCore` satisfy
the `roundWithAccuracy` precondition. Above the minimum exponent, the numerator is shifted far
enough for the provisional quotient to have at least as many bits as the precision, so a zero
provisional quotient occurs only at or below the minimum exponent.
-/
theorem divCore_exponent_le_targetExponent (spec : Float.Model.Format)
    {mantissa₁ mantissa₂ : Nat} (exponent₁ exponent₂ : Int)
    (hmantissa₁ : 0 < mantissa₁) (hmantissa₂ : 0 < mantissa₂) :
    (Float.Model.UnpackedFloat.divCore spec mantissa₁ exponent₁ mantissa₂ exponent₂).2.1 ≤
      spec.targetExponent
        (Float.Model.totalExponent
          (Float.Model.UnpackedFloat.divCore spec mantissa₁ exponent₁ mantissa₂ exponent₂).1
          (Float.Model.UnpackedFloat.divCore
            spec mantissa₁ exponent₁ mantissa₂ exponent₂).2.1) := by
  rw [le_targetExponent_totalExponent_iff]
  obtain ⟨targetExponent, htarget⟩ : ∃ targetExponent : Int, targetExponent =
      min (exponent₁ - exponent₂)
        (spec.targetExponent
          (Float.Model.totalExponent mantissa₁ exponent₁ -
            Float.Model.totalExponent mantissa₂ exponent₂)) := ⟨_, rfl⟩
  obtain ⟨shiftAmount, hshift⟩ : ∃ shiftAmount : Nat, shiftAmount =
      (exponent₁ - exponent₂ - targetExponent).toNat := ⟨_, rfl⟩
  have hcore :
      Float.Model.UnpackedFloat.divCore spec mantissa₁ exponent₁ mantissa₂ exponent₂ =
        ((mantissa₁ <<< shiftAmount) / mantissa₂, targetExponent,
          accuracyOfFraction ((mantissa₁ <<< shiftAmount) % mantissa₂) mantissa₂) := by
    rw [hshift, htarget]
    rfl
  rw [hcore]
  change targetExponent ≤ spec.minExponent ∨
    2 ^ spec.mantissaBitsWithoutImplicit ≤ (mantissa₁ <<< shiftAmount) / mantissa₂
  by_cases hfloor : targetExponent ≤ spec.minExponent
  · exact Or.inl hfloor
  · refine Or.inr ?_
    simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent,
      Float.Model.Format.mantissaBits] at htarget
    have hlower := Nat.log2_self_le hmantissa₁.ne'
    have hupper := Nat.lt_log2_self (n := mantissa₂)
    rw [Nat.le_div_iff_mul_le hmantissa₂, Nat.shiftLeft_eq]
    calc
      2 ^ spec.mantissaBitsWithoutImplicit * mantissa₂ ≤
          2 ^ spec.mantissaBitsWithoutImplicit * 2 ^ (mantissa₂.log2 + 1) :=
        Nat.mul_le_mul_left _ hupper.le
      _ = 2 ^ (spec.mantissaBitsWithoutImplicit + (mantissa₂.log2 + 1)) :=
        (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ (mantissa₁.log2 + shiftAmount) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _ = 2 ^ mantissa₁.log2 * 2 ^ shiftAmount := Nat.pow_add _ _ _
      _ ≤ mantissa₁ * 2 ^ shiftAmount := Nat.mul_le_mul_right _ hlower

/--
For a conventional IEEE descriptor, finite nonzero operands, and a finite result, Lean core's
unpacked division has the same independent nearest-even real semantics as `Model.div`.

`divCore` always satisfies the `roundWithAccuracy` precondition
(`divCore_exponent_le_targetExponent`). A zero provisional quotient is rounded from its sign,
selected exponent, and remainder accuracy.
-/
theorem toReal_ofModel_div_finite_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign₁ sign₂ : Sign)
    (mantissa₁ mantissa₂ : Nat)
    (exponent₁ exponent₂ : Int)
    (hmantissa₁ : 0 < mantissa₁)
    (hmantissa₂ : 0 < mantissa₂)
    (hfinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
            (.finite sign₁ mantissa₁ exponent₁ hmantissa₁)
            (.finite sign₂ mantissa₂ exponent₂ hmantissa₂))) = true) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
            (.finite sign₁ mantissa₁ exponent₁ hmantissa₁)
            (.finite sign₂ mantissa₂ exponent₂ hmantissa₂))) =
      roundAt fmt
        (unpackedToReal (.finite sign₁ mantissa₁ exponent₁ hmantissa₁) /
          unpackedToReal (.finite sign₂ mantissa₂ exponent₂ hmantissa₂)) := by
  let targetExponent :=
    min (exponent₁ - exponent₂)
      ((FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa₁ exponent₁ -
          Float.Model.totalExponent mantissa₂ exponent₂))
  let shiftAmount := (exponent₁ - exponent₂ - targetExponent).toNat
  let numerator := mantissa₁ <<< shiftAmount
  let quotient := numerator / mantissa₂
  let accuracy := accuracyOfFraction (numerator % mantissa₂) mantissa₂
  have hcore :
      Float.Model.UnpackedFloat.divCore
          (FloatFormat.toModel fmt) mantissa₁ exponent₁ mantissa₂ exponent₂ =
        (quotient, targetExponent, accuracy) := by
    rfl
  have haccuracy :
      accuracyRepresents quotient accuracy
        ((numerator : Real) / mantissa₂) := by
    exact accuracyRepresents_accuracyOfFraction numerator mantissa₂ hmantissa₂.ne'
  have hle :
      targetExponent ≤
        (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent quotient targetExponent) := by
    simpa [hcore] using
      divCore_exponent_le_targetExponent (FloatFormat.toModel fmt) exponent₁ exponent₂
        hmantissa₁ hmantissa₂
  have hround :=
    toReal_ofModel_roundWithAccuracy_eq_roundAt
      fmt hfmt (sign₁ / sign₂) quotient targetExponent accuracy
      ((numerator : Real) / mantissa₂)
      haccuracy hle hfinite
  change
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.roundWithAccuracy
            (FloatFormat.toModel fmt) (sign₁ / sign₂)
            quotient targetExponent accuracy)) =
      _
  rw [hround]
  exact congrArg (roundAt fmt)
    (unpackedToReal_div_eq_shifted_quotient sign₁ sign₂ mantissa₁ mantissa₂ exponent₁ exponent₂
      targetExponent hmantissa₁ hmantissa₂ (min_le_left _ _)).symm

end Model
end FloatLib.Floats.Formats.BinaryInterchange
