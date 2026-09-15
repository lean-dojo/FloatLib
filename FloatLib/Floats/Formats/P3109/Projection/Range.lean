/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Order
public import FloatLib.Floats.Formats.P3109.Projection.Rounding
import Mathlib.Tactic.NormNum
public import FloatLib.Floats.Formats.P3109.Projection.Finite

/-!
# Range safety for P3109 encoding

The direct encoder receives a rounded dyadic rather than searching a finite codebook. This module
proves that an in-range value on the descriptor's precision grid produces an in-range code and
decodes to the same numerical datum. The argument is uniform in bit width, precision, signedness,
and finite or extended domain.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109
namespace Format

/-- The largest finite positive code is always inside the descriptor width. -/
theorem maxFiniteBits_lt_modulus (format : Format) :
    format.maxFiniteBits < format.modulus := by
  cases domain : format.domain with
  | finite =>
      simpa [maxFiniteBits, domain] using
        format.positiveInfinityBits_lt_modulus
  | extended =>
      have hcode := format.positiveInfinityBits_lt_modulus
      simp [maxFiniteBits, domain]
      omega

/-- Every valid P3109 descriptor has a nonzero positive finite endpoint. -/
theorem maxFiniteBits_pos (format : Format) :
    0 < format.maxFiniteBits := by
  have hboundary : 2 < format.signBoundary := by
    unfold signBoundary
    have hexponent : 1 < format.bitWidth - 1 := by
      have hwidth := format.bitWidth_gt_two
      omega
    simpa using Nat.pow_lt_pow_right (a := 2) (by decide) hexponent
  have hmodulus : 3 < format.modulus := by
    unfold modulus
    have hpower :
        2 ^ 2 < 2 ^ format.bitWidth :=
      Nat.pow_lt_pow_right (a := 2) (by decide)
        format.bitWidth_gt_two
    norm_num at hpower ⊢
    omega
  cases signedness : format.signedness <;>
    cases domain : format.domain <;>
    simp [maxFiniteBits, positiveInfinityBits,
      signedness, domain] <;>
    omega

/-- Positive finite codes stay below the sign boundary of a signed descriptor. -/
theorem maxFiniteBits_lt_signBoundary_of_signed
    (format : Format) (signed : format.signedness = .signed) :
    format.maxFiniteBits < format.signBoundary := by
  have hboundary := format.one_lt_signBoundary
  cases domain : format.domain <;>
    simp [maxFiniteBits, positiveInfinityBits, signed, domain] <;>
    omega

/--
Encoding a positive grid value no larger than `maxFinite` cannot overflow into a reserved code.
-/
theorem encodePositiveFinite_le_maxFiniteBits
    (format : Format) (value : Numerics.Dyadic)
    (hnegative : value.negative = false)
    (hzero : value.significand ≠ 0)
    (hprecision : value.significand ≤ 2 ^ format.precision)
    (hexponent : format.minimumQuantumExponent ≤ value.exponent)
    (hmax : value.toRat ≤ format.maxFinite.toRat) :
    Internal.encodePositiveFinite format value ≤
      format.maxFiniteBits := by
  apply Nat.le_of_not_gt
  intro hlt
  have hdecode :=
    format.decodePositiveFinite_strictMono hlt
  change
    (format.decodePositiveFinite format.maxFiniteBits).toRat <
      (format.decodePositiveFinite
        (Internal.encodePositiveFinite format value)).toRat at hdecode
  rw [format.decodePositiveFinite_encodePositiveFinite_eq_of_le
    value hnegative hzero hprecision hexponent] at hdecode
  change format.maxFinite.toRat < value.toRat at hdecode
  exact (not_lt_of_ge hmax) hdecode

/-- Every decoded positive finite row lies on the descriptor precision grid. -/
theorem decodePositiveFinite_fitsPrecisionGrid
    (format : Format) (bits : Nat) :
    format.FitsPrecisionGrid
      (format.decodePositiveFinite bits) := by
  by_cases hzero : bits = 0
  · subst bits
    simp [FitsPrecisionGrid]
  let unit := 2 ^ format.trailingBits
  have hunit : 0 < unit := Nat.two_pow_pos _
  have hprecision :
      2 ^ format.precision = 2 * unit := by
    unfold unit
    rw [← format.trailingBits_add_one, Nat.pow_succ]
    omega
  by_cases hrow : bits / unit = 0
  · rw [format.decodePositiveFinite_of_biasedExponent_eq_zero
      bits hzero (by simpa [unit] using hrow)]
    right
    constructor
    · dsimp only
      have hmod := Nat.mod_lt bits hunit
      omega
    · rfl
  · rw [format.decodePositiveFinite_of_biasedExponent_ne_zero
      bits hzero (by simpa [unit] using hrow)]
    right
    constructor
    · dsimp only
      have hmod := Nat.mod_lt bits hunit
      omega
    · dsimp only
      have hrowPositive : 0 < bits / unit :=
        Nat.pos_of_ne_zero hrow
      have hrowPositive' :
          0 < bits / 2 ^ format.trailingBits := by
        simpa [unit] using hrowPositive
      have hrowCast :
          (0 : Int) <
            Int.ofNat (bits / 2 ^ format.trailingBits) := by
        change
          Int.ofNat 0 <
            Int.ofNat (bits / 2 ^ format.trailingBits)
        exact Int.ofNat_lt.mpr hrowPositive'
      unfold minimumQuantumExponent
      omega

/-- The positive finite endpoint lies on the descriptor precision grid. -/
theorem maxFinite_fitsPrecisionGrid (format : Format) :
    format.FitsPrecisionGrid format.maxFinite :=
  format.decodePositiveFinite_fitsPrecisionGrid _

/-- The positive finite endpoint is strictly positive. -/
theorem maxFinite_toRat_pos (format : Format) :
    0 < format.maxFinite.toRat := by
  apply Numerics.Dyadic.toRat_pos_of_significand_ne_zero
  · change
      (format.decodePositiveFinite
        format.maxFiniteBits).significand ≠ 0
    exact
      (format.decodePositiveFinite_significand_eq_zero_iff _).not.mpr
        format.maxFiniteBits_pos.ne'
  · exact format.decodePositiveFinite_negative _

/-- The descriptor's finite interval is nonempty. -/
theorem minFinite_toRat_le_maxFinite (format : Format) :
    format.minFinite.toRat ≤ format.maxFinite.toRat := by
  cases signedness : format.signedness with
  | signed =>
      rw [minFinite, signedness, Numerics.Dyadic.neg_toRat]
      exact le_trans (neg_nonpos.mpr format.maxFinite_toRat_pos.le)
        format.maxFinite_toRat_pos.le
  | unsigned =>
      rw [minFinite, signedness, Numerics.Dyadic.zero_toRat]
      exact format.maxFinite_toRat_pos.le

/-- The negative or zero finite endpoint lies on the descriptor precision grid. -/
theorem minFinite_fitsPrecisionGrid (format : Format) :
    format.FitsPrecisionGrid format.minFinite := by
  cases signedness : format.signedness with
  | signed =>
      simpa [minFinite, signedness, FitsPrecisionGrid] using
        format.maxFinite_fitsPrecisionGrid
  | unsigned =>
      simp [minFinite, signedness, FitsPrecisionGrid]

/-- Codes up to the largest finite code decode as nonnegative finite values. -/
private theorem decodeNat_of_le_maxFiniteBits
    (format : Format) (bits : Nat)
    (hbits : bits ≤ format.maxFiniteBits) :
    format.decodeNat bits =
      .finite (format.decodePositiveFinite bits) := by
  cases signedness : format.signedness with
  | signed =>
      have hboundary := format.one_lt_signBoundary
      cases domain : format.domain with
      | finite =>
          have hlt : bits < format.signBoundary := by
            have hle : bits ≤ format.signBoundary - 1 := by
              simpa [maxFiniteBits, positiveInfinityBits,
                signedness, domain] using hbits
            omega
          simp [decodeNat, signedness, domain,
            ne_of_lt hlt, Nat.not_lt.mpr hlt.le]
      | extended =>
          have hlt : bits < format.positiveInfinityBits := by
            have hle :
                bits ≤ format.positiveInfinityBits - 1 := by
              simpa [maxFiniteBits, domain] using hbits
            exact Nat.lt_of_le_sub_one
              format.positiveInfinityBits_pos hle
          have hpositive :
              format.positiveInfinityBits < format.signBoundary := by
            simp [positiveInfinityBits, signedness]
            omega
          have hnegative :
              bits ≠ format.negativeInfinityBits := by
            have hnegativeCode := format.negativeInfinityBits_lt_modulus
            have hmodulus := format.modulus_eq_two_mul_signBoundary
            simp [negativeInfinityBits] at hnegativeCode ⊢
            omega
          simp [decodeNat, signedness, domain,
            ne_of_lt (lt_trans hlt hpositive),
            ne_of_lt hlt, hnegative,
            Nat.not_lt.mpr (lt_trans hlt hpositive).le]
  | unsigned =>
      have hmodulus := format.two_lt_modulus
      cases domain : format.domain with
      | finite =>
          have hlt : bits < format.nanBits := by
            have hle : bits ≤ format.modulus - 2 := by
              simpa [maxFiniteBits, positiveInfinityBits,
                signedness, domain] using hbits
            have hstep :
                format.modulus - 2 < format.modulus - 1 := by
              omega
            simpa [nanBits, signedness] using
              (lt_of_le_of_lt hle hstep)
          simp [decodeNat, signedness, domain, ne_of_lt hlt]
      | extended =>
          have hlt : bits < format.positiveInfinityBits := by
            have hle :
                bits ≤ format.positiveInfinityBits - 1 := by
              simpa [maxFiniteBits, domain] using hbits
            exact Nat.lt_of_le_sub_one
              format.positiveInfinityBits_pos hle
          have hinfinityNan :
              format.positiveInfinityBits < format.nanBits := by
            simp [positiveInfinityBits, nanBits, signedness]
            omega
          simp [decodeNat, signedness, domain, ne_of_lt hlt,
            ne_of_lt (lt_trans hlt hinfinityNan)]

/-- In a signed descriptor, codes above the sign boundary mirror the positive finite rows. -/
private theorem decodeNat_signBoundary_add_of_signed
    (format : Format) (signed : format.signedness = .signed)
    (magnitude : Nat) (hpositive : 0 < magnitude)
    (hmax : magnitude ≤ format.maxFiniteBits) :
    format.decodeNat (format.signBoundary + magnitude) =
      .finite (format.decodePositiveFinite magnitude).neg := by
  have habove :
      format.signBoundary <
        format.signBoundary + magnitude := by omega
  have hboundary := format.one_lt_signBoundary
  cases domain : format.domain with
  | finite =>
      simp [decodeNat, signed, domain, habove, hpositive.ne']
  | extended =>
      have hmaxBits :
          format.maxFiniteBits =
            format.signBoundary - 2 := by
        simp [maxFiniteBits, positiveInfinityBits, signed, domain]
        omega
      have hmodulus := format.modulus_eq_two_mul_signBoundary
      have hcodeLtNegativeInfinity :
          format.signBoundary + magnitude <
            format.negativeInfinityBits := by
        simp [negativeInfinityBits]
        rw [hmodulus]
        omega
      have hnotPositiveInfinity :
          format.signBoundary + magnitude ≠
            format.positiveInfinityBits := by
        simp [positiveInfinityBits, signed]
        omega
      simp [decodeNat, signed, domain, hnotPositiveInfinity,
        ne_of_lt hcodeLtNegativeInfinity, habove, hpositive.ne']

/-- Direct encoding preserves a positive grid value that lies inside the finite range. -/
private theorem sameDatum_decode_encodePositiveFinite
    (format : Format) (value : Numerics.Dyadic)
    (hnegative : value.negative = false)
    (hzero : value.significand ≠ 0)
    (hprecision : value.significand ≤ 2 ^ format.precision)
    (hexponent : format.minimumQuantumExponent ≤ value.exponent)
    (hmax : value.toRat ≤ format.maxFinite.toRat) :
    SameDatum
      (format.decode
        (BitVec.ofNat format.bitWidth
          (Internal.encodeDatumNat format (.finite value))))
      (.finite value) := by
  let code := Internal.encodePositiveFinite format value
  have hcodeMax : code ≤ format.maxFiniteBits :=
    format.encodePositiveFinite_le_maxFiniteBits
      value hnegative hzero hprecision hexponent hmax
  have hcodeWidth : code < 2 ^ format.bitWidth := by
    apply lt_of_le_of_lt hcodeMax
    simpa [modulus] using format.maxFiniteBits_lt_modulus
  have hdecode :
      format.decode (BitVec.ofNat format.bitWidth code) =
        .finite (format.decodePositiveFinite code) := by
    unfold decode
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcodeWidth]
    exact format.decodeNat_of_le_maxFiniteBits code hcodeMax
  have hpreserve :
      (format.decodePositiveFinite code).toRat =
        value.toRat :=
    format.decodePositiveFinite_encodePositiveFinite_eq_of_le
      value hnegative hzero hprecision hexponent
  have hencoded :
      Internal.encodeDatumNat format (.finite value) = code := by
    simp [Internal.encodeDatumNat, hzero, hnegative, code]
    apply congrArg (Internal.encodePositiveFinite format)
    apply Numerics.Dyadic.ext <;> simp [hnegative]
  rw [hencoded]
  change
    SameDatum
      (format.decode (BitVec.ofNat format.bitWidth code))
      (.finite value)
  rw [hdecode]
  exact hpreserve

/-- Direct encoding preserves a negative grid value that lies inside the finite range. -/
private theorem sameDatum_decode_encodeNegativeFinite
    (format : Format) (value : Numerics.Dyadic)
    (hnegative : value.negative = true)
    (hzero : value.significand ≠ 0)
    (hprecision : value.significand ≤ 2 ^ format.precision)
    (hexponent : format.minimumQuantumExponent ≤ value.exponent)
    (hmin : format.minFinite.toRat ≤ value.toRat) :
    SameDatum
      (format.decode
        (BitVec.ofNat format.bitWidth
          (Internal.encodeDatumNat format (.finite value))))
      (.finite value) := by
  have hmagnitude : ({ value with negative := false } : Numerics.Dyadic) = value.neg :=
    Numerics.Dyadic.ext (by simp [hnegative]) rfl rfl
  have hneg_toRat := Numerics.Dyadic.neg_toRat value
  have hpos : 0 < value.neg.toRat :=
    Numerics.Dyadic.toRat_pos_of_significand_ne_zero _ hzero (by simp [hnegative])
  cases signedness : format.signedness with
  | unsigned =>
      rw [minFinite, signedness, Numerics.Dyadic.zero_toRat] at hmin
      exact absurd hmin (not_le.mpr (by
        rw [← neg_neg value.toRat, ← hneg_toRat]
        exact neg_neg_of_pos hpos))
  | signed =>
      have hmax : value.neg.toRat ≤ format.maxFinite.toRat := by
        rw [minFinite, signedness, Numerics.Dyadic.neg_toRat] at hmin
        rw [hneg_toRat]
        exact neg_le.mp hmin
      have hcode := format.encodePositiveFinite_le_maxFiniteBits value.neg (by simp [hnegative])
        hzero hprecision hexponent hmax
      have hpreserve := format.decodePositiveFinite_encodePositiveFinite_eq_of_le value.neg
        (by simp [hnegative]) hzero hprecision hexponent
      have hcode_pos : 0 < Internal.encodePositiveFinite format value.neg := by
        apply Nat.pos_of_ne_zero
        intro h
        rw [h, decodePositiveFinite_zero, Numerics.Dyadic.zero_toRat] at hpreserve
        exact hpos.ne hpreserve
      have hwidth :
          format.signBoundary + Internal.encodePositiveFinite format value.neg <
            2 ^ format.bitWidth := by
        have := format.maxFiniteBits_lt_signBoundary_of_signed signedness
        have := format.modulus_eq_two_mul_signBoundary
        unfold modulus at this
        omega
      simp only [Internal.encodeDatumNat, beq_iff_eq, hzero, ite_false, hnegative, ite_true,
        hmagnitude]
      unfold decode
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwidth,
        format.decodeNat_signBoundary_add_of_signed signedness _ hcode_pos hcode]
      change (format.decodePositiveFinite _).neg.toRat = value.toRat
      rw [Numerics.Dyadic.neg_toRat, hpreserve, hneg_toRat, neg_neg]

/--
Direct encoding preserves every finite datum on the descriptor grid and inside its finite range.

This theorem is the no-wrap boundary used by projection correctness. It applies to arbitrary valid
descriptors rather than a list of named low-precision formats.
-/
theorem sameDatum_decode_encodeFinite
    (format : Format) (value : Numerics.Dyadic)
    (hgrid : format.FitsPrecisionGrid value)
    (hmin : format.minFinite.toRat ≤ value.toRat)
    (hmax : value.toRat ≤ format.maxFinite.toRat) :
    SameDatum
      (format.decode
        (BitVec.ofNat format.bitWidth
          (Internal.encodeDatumNat format (.finite value))))
      (.finite value) := by
  by_cases hzero : value.significand = 0
  · have hvalueZero : value.toRat = 0 :=
      (Numerics.Dyadic.toRat_eq_zero_iff value).mpr hzero
    simp [Internal.encodeDatumNat, hzero, SameDatum, hvalueZero]
  rcases hgrid with hzero' | ⟨hprecision, hexponent⟩
  · exact (hzero hzero').elim
  cases hnegative : value.negative with
  | false =>
      exact format.sameDatum_decode_encodePositiveFinite
        value hnegative hzero hprecision hexponent hmax
  | true =>
      exact format.sameDatum_decode_encodeNegativeFinite
        value hnegative hzero hprecision hexponent hmin

end Format
end FloatLib.Floats.Formats.P3109
