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
    let d : Numerics.Dyadic :=
      { negative := true, significand := (-mantissa).toNat, exponent := exponent }
    have hmantissa : d.significand ≠ 0 := by
      dsimp [d]
      omega
    have hround :
        ofModel fmt
            (Float.Model.UnpackedFloat.round
              (FloatFormat.toModel fmt) .negative (-mantissa).toNat exponent) =
          roundDyadic fmt d := by
      simp [roundDyadic, hfmt, ieeeRoundDyadic, d, modelSign]
    rw [hround] at hfinite ⊢
    rw [toReal_roundDyadic_eq_roundAt fmt hfmt d hfinite]
    congr 1
    dsimp [d, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
      FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]
    have htoNat :
        (Int.ofNat (-mantissa).toNat) = -mantissa :=
      Int.toNat_of_nonneg (by omega)
    have hcast : (((-mantissa).toNat : Nat) : Real) = -(mantissa : Real) := by
      exact_mod_cast htoNat
    rw [Int.cast_neg, Int.cast_natCast, hcast]
    ring
  · have hzero : mantissa = 0 := Int.compare_eq_eq.mp hcompare
    subst mantissa
    rw [toReal_ofModel_zero fmt hfmt, Int.cast_zero, zero_mul, roundAt_zero]
  · have hpositive : 0 < mantissa := Int.compare_eq_gt.mp hcompare
    simp only [Float.Model.UnpackedFloat.normalize, hcompare] at hfinite
    let d : Numerics.Dyadic :=
      { negative := false, significand := mantissa.toNat, exponent := exponent }
    have hmantissa : d.significand ≠ 0 := by
      dsimp [d]
      omega
    have hround :
        ofModel fmt
            (Float.Model.UnpackedFloat.round
              (FloatFormat.toModel fmt) .positive mantissa.toNat exponent) =
          roundDyadic fmt d := by
      simp [roundDyadic, hfmt, ieeeRoundDyadic, d, modelSign]
    rw [hround] at hfinite ⊢
    rw [toReal_roundDyadic_eq_roundAt fmt hfmt d hfinite]
    congr 1
    dsimp [d, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
      FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]
    have htoNat :
        (Int.ofNat mantissa.toNat) = mantissa :=
      Int.toNat_of_nonneg hpositive.le
    have hcast : (mantissa.toNat : Real) = (mantissa : Real) := by
      exact_mod_cast htoNat
    rw [Int.cast_natCast, hcast]

/--
Lean's exponent-decreasing alignment changes only the integer representation of a dyadic value.
-/
private theorem decreaseExponent_value
    (mantissa : Nat) (exponent targetExponent : Int) :
    let decreased :=
      Float.Model.UnpackedFloat.decreaseExponent mantissa exponent targetExponent
    (decreased.1 : Real) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix decreased.2 =
      (mantissa : Real) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent := by
  by_cases hle : exponent ≤ targetExponent
  · have hshift : (exponent - targetExponent).toNat = 0 :=
      Int.toNat_eq_zero.mpr (by omega)
    simp [Float.Model.UnpackedFloat.decreaseExponent, hshift]
  · let shift := (exponent - targetExponent).toNat
    have hshiftInt : (shift : Int) = exponent - targetExponent := by
      exact Int.toNat_of_nonneg (by omega)
    have hexponent : exponent - (shift : Int) + (shift : Int) = exponent := by
      omega
    simp only [Float.Model.UnpackedFloat.decreaseExponent]
    change
      ((mantissa <<< shift : Nat) : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (exponent - (shift : Int)) =
        (mantissa : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent
    rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow]
    change
      (mantissa : Real) * 2 ^ shift *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (exponent - (shift : Int)) =
        (mantissa : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent
    have hpow :
        (2 : Real) ^ shift =
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (shift : Int) := by
      simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
        Numerics.Radix.toReal]
    rw [hpow, mul_assoc, ← FloatLib.Floats.Formats.Flocq.bpow.add_exp]
    have hexponent' : (shift : Int) + (exponent - (shift : Int)) = exponent := by
      omega
    rw [hexponent']

private theorem cast_sign_apply (sign : Sign) (mantissa : Nat) :
    ((sign.apply mantissa : Int) : Real) =
      (if modelSignBit sign then (-1 : Real) else 1) * mantissa := by
  cases sign <;> simp [Float.Model.UnpackedFloat.Sign.apply]

/-- Lean's remainder classification locates the exact quotient relative to the integer quotient. -/
private theorem accuracyRepresents_accuracyOfFraction
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
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix decreased₁.2 =
        (mantissa₁ : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent₁ := by
    exact decreaseExponent_value mantissa₁ exponent₁ smallerExponent
  have hdecreased₂ :
      (decreased₂.1 : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix decreased₂.2 =
        (mantissa₂ : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent₂ := by
    exact decreaseExponent_value mantissa₂ exponent₂ smallerExponent
  have hexponent₁ : decreased₁.2 = smallerExponent := by
    dsimp [decreased₁]
    unfold Float.Model.UnpackedFloat.decreaseExponent
    by_cases hle : exponent₁ ≤ smallerExponent
    · have heq : exponent₁ = smallerExponent := by
        exact le_antisymm hle (min_le_left _ _)
      simp [heq]
    · change
        exponent₁ - (Int.ofNat (exponent₁ - smallerExponent).toNat) =
          smallerExponent
      have hshift :
          Int.ofNat (exponent₁ - smallerExponent).toNat =
            exponent₁ - smallerExponent :=
        Int.toNat_of_nonneg (by omega)
      rw [hshift]
      omega
  have hexponent₂ : decreased₂.2 = smallerExponent := by
    dsimp [decreased₂]
    unfold Float.Model.UnpackedFloat.decreaseExponent
    by_cases hle : exponent₂ ≤ smallerExponent
    · have heq : exponent₂ = smallerExponent := by
        exact le_antisymm hle (min_le_right _ _)
      simp [heq]
    · change
        exponent₂ - (Int.ofNat (exponent₂ - smallerExponent).toNat) =
          smallerExponent
      have hshift :
          Int.ofNat (exponent₂ - smallerExponent).toNat =
            exponent₂ - smallerExponent :=
        Int.toNat_of_nonneg (by omega)
      rw [hshift]
      omega
  rw [hexponent₁] at hdecreased₁
  rw [hexponent₂] at hdecreased₂
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
  have hmantissa : mantissa₁ * mantissa₂ ≠ 0 :=
    Nat.mul_ne_zero hmantissa₁.ne' hmantissa₂.ne'
  have haccuracy :
      accuracyRepresents (mantissa₁ * mantissa₂) .exact
        ((mantissa₁ : Real) * mantissa₂) := by
    simp [accuracyRepresents]
  have hround :=
    toReal_ofModel_roundWithAccuracy_eq_roundAt
      fmt hfmt (sign₁ * sign₂) (mantissa₁ * mantissa₂)
      (exponent₁ + exponent₂) .exact
      ((mantissa₁ : Real) * mantissa₂)
      hmantissa haccuracy hle hfinite
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
For finite nonzero operands satisfying Lean core's documented `roundWithAccuracy` precondition,
unpacked division has the same independent nearest-even real semantics as `Model.div`.

The nonzero provisional quotient premise records that `divCore` produced at least one significant
bit. It is the natural domain of the generic accuracy-to-rounding bridge.
-/
theorem toReal_ofModel_div_finite_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign₁ sign₂ : Sign)
    (mantissa₁ mantissa₂ : Nat)
    (exponent₁ exponent₂ : Int)
    (hmantissa₁ : 0 < mantissa₁)
    (hmantissa₂ : 0 < mantissa₂)
    (hquotient :
      (Float.Model.UnpackedFloat.divCore
        (FloatFormat.toModel fmt) mantissa₁ exponent₁ mantissa₂ exponent₂).1 ≠ 0)
    (hle :
      (Float.Model.UnpackedFloat.divCore
        (FloatFormat.toModel fmt) mantissa₁ exponent₁ mantissa₂ exponent₂).2.1 ≤
        (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent
            (Float.Model.UnpackedFloat.divCore
              (FloatFormat.toModel fmt) mantissa₁ exponent₁ mantissa₂ exponent₂).1
            (Float.Model.UnpackedFloat.divCore
              (FloatFormat.toModel fmt) mantissa₁ exponent₁ mantissa₂ exponent₂).2.1))
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
  have hquotient' : quotient ≠ 0 := by
    simpa [hcore] using hquotient
  have hle' :
      targetExponent ≤
        (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent quotient targetExponent) := by
    simpa [hcore] using hle
  have hround :=
    toReal_ofModel_roundWithAccuracy_eq_roundAt
      fmt hfmt (sign₁ / sign₂) quotient targetExponent accuracy
      ((numerator : Real) / mantissa₂)
      hquotient' haccuracy hle' hfinite
  change
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.roundWithAccuracy
            (FloatFormat.toModel fmt) (sign₁ / sign₂)
            quotient targetExponent accuracy)) =
      _
  rw [hround]
  congr 1
  have htargetLe : targetExponent ≤ exponent₁ - exponent₂ :=
    min_le_left _ _
  have hshift :
      (shiftAmount : Int) = exponent₁ - exponent₂ - targetExponent := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr htargetLe)
  have hnumerator :
      (numerator : Real) =
        (mantissa₁ : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (shiftAmount : Int) := by
    dsimp [numerator]
    rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow]
    simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
      Numerics.Radix.toReal]
  have hscale :
      ((numerator : Real) / mantissa₂) *
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
    rw [hnumerator, div_mul_eq_mul_div, mul_assoc,
      ← FloatLib.Floats.Formats.Flocq.bpow.add_exp,
      show (shiftAmount : Int) + targetExponent = exponent₁ - exponent₂ by omega,
      FloatLib.Floats.Formats.Flocq.bpow.sub_exp]
    field_simp
  rw [hscale]
  cases sign₁ <;> cases sign₂ <;>
    simp [unpackedToReal_finite, modelSignBit, neg_div, div_neg,
      show Sign.negative / Sign.negative = Sign.positive from rfl,
      show Sign.negative / Sign.positive = Sign.negative from rfl,
      show Sign.positive / Sign.negative = Sign.negative from rfl,
      show Sign.positive / Sign.positive = Sign.positive from rfl]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
