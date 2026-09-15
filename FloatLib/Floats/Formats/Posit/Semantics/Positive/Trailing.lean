/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import FloatLib.Floats.Formats.Posit.Model.Fields

/-!
# Ordered Posit exponent and fraction tails

The finite exponent/fraction tail is ordered independently of regime encoding, and its value
determines the corresponding part of exact Posit decoding. Separating the trailing fields is
useful because two positive posit words with the same regime should be compared without
reopening the variable-length regime parser.

These lemmas form the local bridge used by the full code-order theorem: regime bits establish the
coarse scale interval, while this module handles exact order inside that interval.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/-! ## Ordered exponent/fraction tails -/

/-- Exact rational injection of a natural field value. -/
@[inline] def natToRat (value : Nat) : Rat :=
  Rat.ofInt (Int.ofNat value)

/-- The exact rational injection agrees with the natural-number cast. -/
theorem natToRat_eq_cast (value : Nat) : natToRat value = (value : Rat) := rfl

private theorem natToRat_nonneg (value : Nat) :
    (0 : Rat) ≤ natToRat value := by
  change (0 : Rat) ≤ (value : Rat)
  exact Nat.cast_nonneg value

private theorem natToRat_pos {value : Nat} (hvalue : 0 < value) :
    (0 : Rat) < natToRat value := by
  change (0 : Rat) < (value : Rat)
  exact Nat.cast_pos.mpr hvalue

private theorem natToRat_lt {left right : Nat} (hlt : left < right) :
    natToRat left < natToRat right := by
  change (left : Rat) < (right : Rat)
  exact Nat.cast_lt.mpr hlt

/--
Normalized binary bucket selected by quotient and remainder at a positive denominator.

For posit tails with two exponent bits, `denominator` is the hidden-bit value and the quotient is
the exponent. This more general helper makes the order proof independent of a particular width.
-/
private def bucketRat (denominator raw : Nat) : Rat :=
  (1 + natToRat (raw % denominator) / natToRat denominator) *
    (2 : Rat) ^ Int.ofNat (raw / denominator)

private theorem normalized_ge_one
    (denominator raw : Nat) (hdenominator : 0 < denominator) :
    (1 : Rat) ≤
      1 + natToRat (raw % denominator) / natToRat denominator := by
  exact le_add_of_nonneg_right
    (div_nonneg
      (natToRat_nonneg _)
      (natToRat_pos hdenominator).le)

private theorem normalized_lt_two
    (denominator raw : Nat) (hdenominator : 0 < denominator) :
    1 + natToRat (raw % denominator) / natToRat denominator < 2 := by
  have hdivision :
      natToRat (raw % denominator) / natToRat denominator < 1 :=
    (div_lt_one (natToRat_pos hdenominator)).2
      (natToRat_lt (Nat.mod_lt raw hdenominator))
  linarith

/--
Moving to the next raw exponent/fraction field strictly increases its binary-bucket value.
-/
private theorem bucketRat_strictMono
    (denominator : Nat) (hdenominator : 0 < denominator) :
    StrictMono (bucketRat denominator) := by
  intro left right hlt
  have hquotient :
      left / denominator ≤ right / denominator :=
    Nat.div_le_div_right hlt.le
  rcases hquotient.eq_or_lt with hquotientEq | hquotientLt
  · have hremainder :
        left % denominator < right % denominator := by
      have hleftDecomposition :=
        Nat.mod_add_div left denominator
      have hrightDecomposition :=
        Nat.mod_add_div right denominator
      have hdecomposed := hlt
      rw [← hleftDecomposition, ← hrightDecomposition,
        hquotientEq] at hdecomposed
      omega
    have hnormalized :
        1 + natToRat (left % denominator) / natToRat denominator <
          1 + natToRat (right % denominator) / natToRat denominator := by
      have hdivision :=
        (div_lt_div_iff_of_pos_right
          (natToRat_pos hdenominator)).2
          (natToRat_lt hremainder)
      linarith
    have hquotientEqInt :
        Int.ofNat (left / denominator) =
          Int.ofNat (right / denominator) :=
      congrArg Int.ofNat hquotientEq
    simp only [bucketRat]
    rw [hquotientEqInt]
    exact mul_lt_mul_of_pos_right hnormalized
      (zpow_pos (by norm_num : (0 : Rat) < 2) _)
  · have hleftUpper :
        bucketRat denominator left <
          (2 : Rat) ^
            (Int.ofNat (left / denominator) + 1) := by
      calc
        bucketRat denominator left =
            (1 + natToRat (left % denominator) / natToRat denominator) *
              (2 : Rat) ^ Int.ofNat (left / denominator) := rfl
        _ < 2 * (2 : Rat) ^ Int.ofNat (left / denominator) :=
          mul_lt_mul_of_pos_right
            (normalized_lt_two denominator left hdenominator)
            (zpow_pos (by norm_num : (0 : Rat) < 2) _)
        _ = (2 : Rat) ^ Int.ofNat (left / denominator) * 2 := by
          ring
        _ = (2 : Rat) ^
            (Int.ofNat (left / denominator) + 1) := by
          rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
          norm_num
    have hexponents :
        Int.ofNat (left / denominator) + 1 ≤
          Int.ofNat (right / denominator) := by
      have hsuccessor :
          left / denominator + 1 ≤ right / denominator :=
        Nat.succ_le_of_lt hquotientLt
      rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]
      exact_mod_cast hsuccessor
    have hpowers :
        (2 : Rat) ^
            (Int.ofNat (left / denominator) + 1) ≤
          (2 : Rat) ^ Int.ofNat (right / denominator) :=
      zpow_le_zpow_right₀
        (by norm_num : (1 : Rat) ≤ 2) hexponents
    have hrightLower :
        (2 : Rat) ^ Int.ofNat (right / denominator) ≤
          bucketRat denominator right := by
      calc
        (2 : Rat) ^ Int.ofNat (right / denominator) =
            1 * (2 : Rat) ^ Int.ofNat (right / denominator) := by
          ring
        _ ≤
            (1 + natToRat (right % denominator) / natToRat denominator) *
              (2 : Rat) ^ Int.ofNat (right / denominator) :=
          mul_le_mul_of_nonneg_right
            (normalized_ge_one denominator right hdenominator)
            (zpow_pos (by norm_num : (0 : Rat) < 2) _).le
        _ = bucketRat denominator right := rfl
    exact hleftUpper.trans_le (hpowers.trans hrightLower)

/--
Exact positive value contributed by `trailing` exponent/fraction bits before applying the regime.

The Posit Standard (2022) takes at most two exponent bits. When fewer are present, they are the high
bits and omitted low exponent bits are restored as zero.
-/
@[inline] def trailingRat (trailing raw : Nat) : Rat :=
  let used := min 2 trailing
  let fraction := trailing - used
  let stored := raw / 2 ^ fraction % 2 ^ used
  let exponent := stored * 2 ^ (2 - used)
  (1 + natToRat (raw % 2 ^ fraction) / natToRat (2 ^ fraction)) *
    (2 : Rat) ^ Int.ofNat exponent

/-- The exact exponent/fraction tail is strictly ordered by its bounded raw field. -/
theorem trailingRat_lt_of_lt
    {trailing left right : Nat}
    (hleft : left < 2 ^ trailing)
    (hright : right < 2 ^ trailing)
    (hlt : left < right) :
    trailingRat trailing left < trailingRat trailing right := by
  cases trailing with
  | zero =>
      norm_num at hleft hright
      omega
  | succ trailing =>
      cases trailing with
      | zero =>
          have hleftZero : left = 0 := by
            norm_num at hleft
            omega
          have hrightOne : right = 1 := by
            norm_num at hright
            omega
          subst left
          subst right
          norm_num [trailingRat, natToRat]
      | succ fractionBits =>
          have hleftQuotient :
              left / 2 ^ fractionBits < 4 := by
            rw [Nat.div_lt_iff_lt_mul
              (Nat.two_pow_pos fractionBits)]
            convert hleft using 1
            ring
          have hrightQuotient :
              right / 2 ^ fractionBits < 4 := by
            rw [Nat.div_lt_iff_lt_mul
              (Nat.two_pow_pos fractionBits)]
            convert hright using 1
            ring
          have hleftMod :
              left / 2 ^ fractionBits % 4 =
                left / 2 ^ fractionBits :=
            Nat.mod_eq_of_lt hleftQuotient
          have hrightMod :
              right / 2 ^ fractionBits % 4 =
                right / 2 ^ fractionBits :=
            Nat.mod_eq_of_lt hrightQuotient
          simpa [trailingRat, bucketRat, hleftMod, hrightMod] using
            bucketRat_strictMono
              (2 ^ fractionBits) (Nat.two_pow_pos _) hlt

/--
Only the low `trailing` bits contribute to an exponent/fraction tail.

This is the modular form used when a complete posit magnitude is split into its regime prefix and
remaining field.
-/
theorem trailingRat_mod_twoPow (trailing raw : Nat) :
    trailingRat trailing (raw % 2 ^ trailing) =
      trailingRat trailing raw := by
  let used := min 2 trailing
  let fraction := trailing - used
  have hused : used ≤ trailing :=
    Nat.min_le_right _ _
  have hsum : fraction + used = trailing := by
    dsimp [fraction]
    omega
  have hpower :
      2 ^ trailing = 2 ^ used * 2 ^ fraction := by
    rw [← Nat.pow_add, Nat.add_comm, hsum]
  have hfractionDvd : 2 ^ fraction ∣ 2 ^ trailing := by
    rw [hpower]
    exact dvd_mul_left _ _
  unfold trailingRat
  change
    (1 +
          natToRat ((raw % 2 ^ trailing) % 2 ^ fraction) /
            natToRat (2 ^ fraction)) *
        (2 : Rat) ^
          Int.ofNat
            (((raw % 2 ^ trailing) / 2 ^ fraction % 2 ^ used) *
              2 ^ (2 - used)) =
      (1 + natToRat (raw % 2 ^ fraction) /
          natToRat (2 ^ fraction)) *
        (2 : Rat) ^
          Int.ofNat
            ((raw / 2 ^ fraction % 2 ^ used) *
              2 ^ (2 - used))
  rw [Nat.mod_mod_of_dvd raw hfractionDvd]
  rw [hpower, Nat.mod_mul_left_div_self]
  simp

/--
Appending a zero bit to an exponent/fraction tail preserves its exact rational value.

For tails shorter than two bits this restores one more standard exponent bit as zero. Thereafter
it appends a zero fraction bit, doubling both the explicit numerator and denominator.
-/
theorem trailingRat_succ_two_mul (trailing raw : Nat) :
    trailingRat (trailing + 1) (2 * raw) =
      trailingRat trailing raw := by
  rcases trailing with _ | _ | fraction
  · simp [trailingRat, natToRat_eq_cast, Nat.mod_one]
  · simp [trailingRat, natToRat_eq_cast, Nat.mod_one]
    omega
  · have hdiv : 2 * raw / 2 ^ (fraction + 1) = raw / 2 ^ fraction := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ fraction), Nat.mul_div_mul_left _ _ two_pos]
    have hmod : 2 * raw % 2 ^ (fraction + 1) = 2 * (raw % 2 ^ fraction) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ fraction), Nat.mul_mod_mul_left]
    simp only [trailingRat, natToRat_eq_cast,
      show min 2 (fraction + 1 + 1 + 1) = 2 by omega,
      show min 2 (fraction + 1 + 1) = 2 by omega,
      show fraction + 1 + 1 + 1 - 2 = fraction + 1 by omega,
      show fraction + 1 + 1 - 2 = fraction by omega, hdiv, hmod]
    push_cast
    field_simp
    ring

/--
Every exponent/fraction tail of a Posit Standard (2022) word lies in `[1, 16)`.

The constant `16 = 2 ^ 4` is the multiplicative change in value at each regime step. Adjacent regime
blocks cannot overlap, independently of the total posit width.
-/
theorem trailingRat_bounds (trailing raw : Nat) :
    (1 : Rat) ≤ trailingRat trailing raw ∧
      trailingRat trailing raw < 16 := by
  simp only [trailingRat, natToRat_eq_cast, Int.ofNat_eq_natCast, zpow_natCast]
  have hused : min 2 trailing ≤ 2 := Nat.min_le_left _ _
  have hexponent :
      raw / 2 ^ (trailing - min 2 trailing) % 2 ^ min 2 trailing *
        2 ^ (2 - min 2 trailing) < 4 := by
    have hstored :=
      Nat.mod_lt (raw / 2 ^ (trailing - min 2 trailing)) (Nat.two_pow_pos (min 2 trailing))
    calc _ < 2 ^ min 2 trailing * 2 ^ (2 - min 2 trailing) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hstored
      _ = 4 := by rw [← Nat.pow_add, Nat.add_sub_of_le hused]
  have hpowerUpper :
      (2 : Rat) ^ (raw / 2 ^ (trailing - min 2 trailing) % 2 ^ min 2 trailing *
        2 ^ (2 - min 2 trailing)) ≤ 8 := by
    calc (2 : Rat) ^ _ ≤ (2 : Rat) ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 8 := by norm_num
  have hpowerLower :
      (1 : Rat) ≤ (2 : Rat) ^ (raw / 2 ^ (trailing - min 2 trailing) % 2 ^ min 2 trailing *
        2 ^ (2 - min 2 trailing)) :=
    one_le_pow₀ (by norm_num)
  have hden : (0 : Rat) < ((2 ^ (trailing - min 2 trailing) : Nat) : Rat) := by
    positivity
  have hfraction :
      ((raw % 2 ^ (trailing - min 2 trailing) : Nat) : Rat) /
        ((2 ^ (trailing - min 2 trailing) : Nat) : Rat) < 1 :=
    (div_lt_one hden).2 (Nat.cast_lt.mpr (Nat.mod_lt _ (Nat.two_pow_pos _)))
  have hfractionNonneg :
      (0 : Rat) ≤ ((raw % 2 ^ (trailing - min 2 trailing) : Nat) : Rat) /
        ((2 ^ (trailing - min 2 trailing) : Nat) : Rat) := by
    positivity
  constructor <;> nlinarith

/--
For decoded fields with a clear sign bit, the rational field value factors into the trailing
field and a regime power. This describes field decoding; zero and NaR are handled separately by
the complete decoder.
-/
theorem decodeFields_toRat_eq_trailingRat_mul_regime
    (value : Model format) (hsign : value.signBit = false) :
    value.decodeFields.toRat =
      trailingRat value.trailingBits value.magnitudeBits *
        (2 : Rat) ^
          (value.regimeValue *
            Int.ofNat format.regimeExponentStep) := by
  simp only [DecodedFields.toRat, DecodedFields.toDyadic]
  rw [show value.decodeFields.negative = false by
    simpa [decodeFields] using hsign]
  change
    ((2 ^ value.fractionBits + value.fractionField : Nat) : Rat) *
        (2 : Rat) ^ value.scale = _
  rw [show value.fractionField =
      value.magnitudeBits % 2 ^ value.fractionBits by rfl]
  rw [show value.scale =
      value.regimeValue * Int.ofNat format.regimeExponentStep +
        Int.ofNat value.exponentField -
          Int.ofNat value.fractionBits by rfl]
  rw [show value.exponentField =
      (value.magnitudeBits / 2 ^ value.fractionBits %
          2 ^ value.usedExponentBits) *
        2 ^ (format.exponentBits - value.usedExponentBits) by rfl]
  simp only [trailingRat]
  rw [show min 2 value.trailingBits =
      value.usedExponentBits by rfl]
  rw [show value.trailingBits - value.usedExponentBits =
      value.fractionBits by rfl]
  simp only [Format.exponentBits]
  let stored :=
    value.magnitudeBits / 2 ^ value.fractionBits %
      2 ^ value.usedExponentBits
  let exponent :=
    stored * 2 ^ (2 - value.usedExponentBits)
  let regimeScale :=
    value.regimeValue *
      Int.ofNat format.regimeExponentStep
  change
    ((2 ^ value.fractionBits +
        value.magnitudeBits % 2 ^ value.fractionBits : Nat) : Rat) *
        (2 : Rat) ^
          (regimeScale + Int.ofNat exponent -
            Int.ofNat value.fractionBits) =
      (1 + natToRat
          (value.magnitudeBits % 2 ^ value.fractionBits) /
          natToRat (2 ^ value.fractionBits)) *
        (2 : Rat) ^ Int.ofNat exponent *
        (2 : Rat) ^ regimeScale
  rw [show
      regimeScale + Int.ofNat exponent -
          Int.ofNat value.fractionBits =
        (Int.ofNat exponent - Int.ofNat value.fractionBits) +
          regimeScale by ring]
  rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
  rw [zpow_sub₀ (by norm_num : (2 : Rat) ≠ 0)]
  simp only [Int.ofNat_eq_natCast, zpow_natCast]
  change
    ((2 ^ value.fractionBits +
        value.magnitudeBits % 2 ^ value.fractionBits : Nat) : Rat) *
        (((2 : Rat) ^ exponent /
          (2 : Rat) ^ value.fractionBits) *
          (2 : Rat) ^ regimeScale) =
      (1 +
          ((value.magnitudeBits % 2 ^ value.fractionBits : Nat) : Rat) /
          ((2 ^ value.fractionBits : Nat) : Rat)) *
        (2 : Rat) ^ exponent *
        (2 : Rat) ^ regimeScale
  field_simp
  push_cast
  ring


end FloatLib.Floats.Formats.Posit.Model
