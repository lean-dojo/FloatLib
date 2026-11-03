/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.ModelRounding.Runtime
import FloatLib.Numerics.Bitwise
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.NearestEven

/-!
# Correctness of normalization through Lean's logical float model

The executable rounding primitives in `ModelRounding.Runtime` agree with Lean 4's
width-parameterized `Float.Model.UnpackedFloat.round`. The normalization theorem is generic in
the model format. Lemmas using `FloatFormat.toModel` use the conventional IEEE bias at the
descriptor's field widths.

The model represents discarded information with a round bit and a sticky bit. `Model` uses an
integer shift followed by nearest-even rounding. The main result,
`round_exact_eq_finishRoundedMantissa`, proves that these two representations compute the same
rounded mantissa and target exponent.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019, Section 4.3.1.
- Lean 4, `Init.Data.Float.Model.Unpacked.Round`.
- S. Boldo and G. Melquiond, "Flocq: A Unified Library for Proving Floating-Point Algorithms
  in Coq," ARITH 2011. https://doi.org/10.1109/ARITH.2011.40
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model.UnpackedFloat
open FloatLib.Numerics

/--
Lean's quotient-plus-accuracy representation makes the same nearest-even choice as
`Numerics.roundQuotientEven`.
-/
theorem roundToNearestEven_accuracyOfFraction_mod
    (num den : Nat) (hden : den ≠ 0) :
    Accuracy.roundToNearestEven (num / den)
        (accuracyOfFraction (num % den) den) =
      roundQuotientEven num den := by
  unfold accuracyOfFraction roundQuotientEven
  have hdenPos : 0 < den := Nat.pos_of_ne_zero hden
  have hmodLt : num % den < den := Nat.mod_lt num hdenPos
  by_cases hrem : num % den = 0
  · simp [hrem, hdenPos, Accuracy.roundToNearestEven]
  · simp only [hrem, ite_false]
    split <;> rename_i hcmp
    · have hcompare : compare (2 * (num % den)) den = .lt :=
        Nat.compare_eq_lt.mpr hcmp
      simp [Accuracy.roundToNearestEven, hcompare]
    · split <;> rename_i hcmp'
      · have hcompare : compare (2 * (num % den)) den = .gt :=
          Nat.compare_eq_gt.mpr hcmp'
        simp [Accuracy.roundToNearestEven, hcompare]
      · have heq : 2 * (num % den) = den := by grind
        have hcompare : compare (2 * (num % den)) den = .eq :=
          Nat.compare_eq_eq.mpr heq
        simp only [Accuracy.roundToNearestEven, hcompare]
        by_cases heven : num / den % 2 = 0
        · simp [heven]
        · have hodd : num / den % 2 = 1 := by grind
          simp [hodd]

/-- Embed a natural mantissa with no discarded rounding information. -/
private abbrev exactExtendedMantissa (n : Nat) : ExtendedMantissa :=
  ExtendedMantissa.ofMantissaAndAccuracy n .exact

/--
The retained mantissa after an exact right shift is division by the corresponding power of two.
-/
private theorem exactExtendedMantissa_shift_mantissa (n shift : Nat) :
    (exactExtendedMantissa n >>> shift).mantissa = n / 2 ^ shift :=
  extendedMantissa_shiftRight_mantissa _ shift

/-- The round bit after a positive exact shift is the highest discarded bit. -/
private theorem exactExtendedMantissa_shift_succ_roundBit (n shift : Nat) :
    (exactExtendedMantissa n >>> (shift + 1)).roundBit =
      (n / 2 ^ shift % 2 != 0) := by
  rw [extendedMantissa_shiftRight_succ]
  simp only [ExtendedMantissa.shiftRightOne]
  rw [exactExtendedMantissa_shift_mantissa]

/-- The sticky bit after a positive exact shift records any lower discarded set bit. -/
private theorem exactExtendedMantissa_shift_succ_stickyBit (n shift : Nat) :
    (exactExtendedMantissa n >>> (shift + 1)).stickyBit =
      (n % 2 ^ shift != 0) := by
  induction shift with
  | zero =>
      simp [HShiftRight.hShiftRight, Nat.repeat, exactExtendedMantissa,
        ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.shiftRightOne, Nat.mod_one]
  | succ shift ih =>
      rw [extendedMantissa_shiftRight_succ]
      simp only [ExtendedMantissa.shiftRightOne]
      rw [exactExtendedMantissa_shift_succ_roundBit, ih]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, bne_iff_ne]
      rw [Nat.mod_pow_succ]
      rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ shift) with hbit | hbit <;>
        simp [hbit]

/-- Closed form for every field of a positively shifted exact extended mantissa. -/
private theorem exactExtendedMantissa_shift_succ (n shift : Nat) :
    exactExtendedMantissa n >>> (shift + 1) =
      { mantissa := n / 2 ^ (shift + 1)
        roundBit := n / 2 ^ shift % 2 != 0
        stickyBit := n % 2 ^ shift != 0 } := by
  generalize hem : exactExtendedMantissa n >>> (shift + 1) = em
  cases em with
  | mk mantissa roundBit stickyBit =>
      have hm := exactExtendedMantissa_shift_mantissa n (shift + 1)
      have hr := exactExtendedMantissa_shift_succ_roundBit n shift
      have hs := exactExtendedMantissa_shift_succ_stickyBit n shift
      simp only [hem] at hm hr hs
      simp_all

/-- Shifted round and sticky bits encode the exact discarded-fraction accuracy. -/
private theorem exactExtendedMantissa_shift_accuracy (n shift : Nat) :
    (exactExtendedMantissa n >>> shift).accuracy =
      accuracyOfFraction (n % 2 ^ shift) (2 ^ shift) := by
  cases shift with
  | zero =>
      simp [HShiftRight.hShiftRight, Nat.repeat, exactExtendedMantissa,
        ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.accuracy,
        accuracyOfFraction, Nat.mod_one]
  | succ shift =>
      rw [exactExtendedMantissa_shift_succ]
      have hp : 0 < 2 ^ shift := Nat.pow_pos (by decide)
      have hlow : n % 2 ^ shift < 2 ^ shift := Nat.mod_lt n hp
      have hmod := Nat.mod_pow_succ (x := n) (b := 2) (k := shift)
      rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ shift) with hbit | hbit
      · by_cases hz : n % 2 ^ shift = 0
        · have htotal : n % 2 ^ (shift + 1) = 0 := by
            rw [hmod]
            simp [hbit, hz]
          simp [ExtendedMantissa.accuracy, accuracyOfFraction, hbit, hz, htotal]
        · have htotal : n % 2 ^ (shift + 1) = n % 2 ^ shift := by
            rw [hmod]
            simp [hbit]
          have hsticky : (n % 2 ^ shift != 0) = true := (bne_iff_ne).2 hz
          have hcompare : compare (2 * (n % 2 ^ shift)) (2 ^ (shift + 1)) = .lt := by
            apply Nat.compare_eq_lt.mpr
            rw [pow_succ]
            grind
          simp [ExtendedMantissa.accuracy, accuracyOfFraction, hbit, hz, hsticky, htotal,
            hcompare]
      · by_cases hz : n % 2 ^ shift = 0
        · have htotal : n % 2 ^ (shift + 1) = 2 ^ shift := by
            rw [hmod]
            simp [hbit, hz]
          have hcompare : compare (2 * 2 ^ shift) (2 ^ (shift + 1)) = .eq := by
            apply Nat.compare_eq_eq.mpr
            rw [pow_succ]
            grind
          simp [ExtendedMantissa.accuracy, accuracyOfFraction, hbit, hz, htotal,
            hcompare]
        · have htotal : n % 2 ^ (shift + 1) = n % 2 ^ shift + 2 ^ shift := by
            rw [hmod]
            simp [hbit]
          have hsticky : (n % 2 ^ shift != 0) = true := (bne_iff_ne).2 hz
          have hcompare :
              compare (2 * (n % 2 ^ shift + 2 ^ shift)) (2 ^ (shift + 1)) = .gt := by
            apply Nat.compare_eq_gt.mpr
            rw [pow_succ]
            grind
          simp [ExtendedMantissa.accuracy, accuracyOfFraction, hbit, hz, hsticky, htotal,
            hcompare]

/--
Shifting an exact mantissa and rounding its discarded bits agrees with the executable
nearest-even shift for every shift distance.
-/
theorem roundedMantissa_shift_exact (n shift : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy n .exact >>> shift).roundedMantissa =
      roundShiftRightEven n shift := by
  unfold ExtendedMantissa.roundedMantissa
  rw [exactExtendedMantissa_shift_accuracy, exactExtendedMantissa_shift_mantissa]
  have hden : 2 ^ shift ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by decide))
  rw [roundToNearestEven_accuracyOfFraction_mod n (2 ^ shift) hden]
  exact (Numerics.roundShiftRightEven_eq_roundQuotientEven n shift).symm

/-- A remainder below half an ulp at `shift` is below the full ulp `2^shift`. -/
private theorem lt_two_pow_of_lt_pow2_pred {remainder shift : Nat}
    (hremainder : remainder < pow2 (shift - 1)) : remainder < 2 ^ shift := by
  have hpow : 2 ^ (shift - 1) ≤ 2 ^ shift :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le shift 1)
  have hremainder' : remainder < 2 ^ (shift - 1) := by
    simpa [pow2_eq_two_pow] using hremainder
  exact hremainder'.trans_le hpow

/--
Nearest-even rounding of `(q <<< shift) + r` for a remainder `r < 2^shift`: below half a unit it
gives `q`, above it `q + 1`, and at the tie the even one of the two.
-/
private theorem roundShiftRightEven_shiftLeft_add (q r shift : Nat) (hshift : shift ≠ 0)
    (hr : r < 2 ^ shift) :
    roundShiftRightEven ((q <<< shift) + r) shift =
      if r < 2 ^ (shift - 1) then q
      else if 2 ^ (shift - 1) < r then q + 1
      else if q % 2 == 0 then q else q + 1 := by
  have hquotient : Nat.shiftRight ((q <<< shift) + r) shift = q := by
    change ((q <<< shift) + r) >>> shift = q
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mul_comm q (2 ^ shift),
      Nat.mul_add_div (Nat.two_pow_pos shift), Nat.div_eq_of_lt hr, Nat.add_zero]
  have hremainder : (q <<< shift) + r - Nat.shiftLeft q shift = r :=
    Nat.add_sub_cancel_left (q <<< shift) r
  rw [Numerics.roundShiftRightEven_def]
  simp only [beq_iff_eq, hshift, ite_false, hquotient, hremainder]

/-- A right shift rounds a value below the half-way point `pow2 (shift - 1)` to zero. -/
theorem roundShiftRightEven_eq_zero_of_lt_half
    (n shift : Nat) (hlt : n < pow2 (shift - 1)) :
    roundShiftRightEven n shift = 0 := by
  rcases Nat.eq_zero_or_pos shift with hshift | hshift
  · subst shift
    have hn : n = 0 := by simpa [pow2_eq_two_pow] using hlt
    subst n
    simp [Numerics.roundShiftRightEven_def]
  have hlt' : n < 2 ^ (shift - 1) := by simpa [pow2_eq_two_pow] using hlt
  rw [Numerics.roundShiftRightEven_of_lt_two_pow n shift hshift.ne'
    (lt_two_pow_of_lt_pow2_pred hlt), ite_eq_right (by omega)]

/--
Adding a remainder below half an ulp to a left-shifted mantissa does not change nearest-even
rounding.
-/
theorem roundShiftRightEven_shiftLeft_add_of_lt_half
    (mantissa remainder shift : Nat)
    (hremainder : remainder < pow2 (shift - 1)) :
    roundShiftRightEven ((mantissa <<< shift) + remainder) shift = mantissa := by
  rcases Nat.eq_zero_or_pos shift with hshift | hshift
  · subst shift
    have hzero : remainder = 0 := by simpa [pow2_eq_two_pow] using hremainder
    subst remainder
    simp [Numerics.roundShiftRightEven_def]
  rw [roundShiftRightEven_shiftLeft_add mantissa remainder shift hshift.ne'
      (lt_two_pow_of_lt_pow2_pred hremainder),
    ite_eq_left (by simpa [pow2_eq_two_pow] using hremainder)]

/--
Subtracting a remainder below half an ulp from a left-shifted mantissa does not change
nearest-even rounding.
-/
theorem roundShiftRightEven_shiftLeft_sub_of_lt_half
    (mantissa remainder shift : Nat) (hremainder : remainder < pow2 (shift - 1)) :
    roundShiftRightEven ((mantissa <<< shift) - remainder) shift = mantissa := by
  by_cases hremainderZero : remainder = 0
  · subst remainder
    simpa using
      roundShiftRightEven_shiftLeft_add_of_lt_half mantissa 0 shift
        (Nat.zero_lt_of_lt hremainder)
  rcases Nat.eq_zero_or_pos shift with hshift | hshift
  · subst shift
    simp [pow2_eq_two_pow] at hremainder
    omega
  rcases Nat.eq_zero_or_pos mantissa with hmantissa | hmantissa
  · subst mantissa
    simpa using roundShiftRightEven_eq_zero_of_lt_half 0 shift (Nat.zero_lt_of_lt hremainder)
  have hremainder' : remainder < 2 ^ (shift - 1) := by
    simpa [pow2_eq_two_pow] using hremainder
  have hpowSplit : 2 ^ shift = 2 * 2 ^ (shift - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hshift.ne'
    simp [pow_succ, Nat.mul_comm]
  -- Borrow one unit: the remainder of `(mantissa - 1) <<< shift` is above half an ulp.
  have hsplit : (mantissa <<< shift) - remainder =
      ((mantissa - 1) <<< shift) + (2 ^ shift - remainder) := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq,
      ← Nat.add_sub_assoc (lt_two_pow_of_lt_pow2_pred hremainder).le, Nat.sub_one_mul,
      Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hmantissa)]
  rw [hsplit, roundShiftRightEven_shiftLeft_add (mantissa - 1) (2 ^ shift - remainder) shift
      hshift.ne' (Nat.sub_lt (Nat.two_pow_pos shift) (Nat.pos_of_ne_zero hremainderZero)),
    ite_eq_right (by omega), ite_eq_left (by omega)]
  omega

/-- A nonzero mantissa rounded to leading position `p` is at least `2^p`. -/
theorem pow2_le_roundMantissaToLeadingBitEven
    (mantissa leadingBit : Nat) (hm : mantissa ≠ 0) :
    pow2 leadingBit ≤ roundMantissaToLeadingBitEven mantissa leadingBit := by
  unfold roundMantissaToLeadingBitEven
  split <;> rename_i hle
  · have hdiv :
        2 ^ leadingBit ≤ mantissa / 2 ^ (mantissa.log2 - leadingBit) := by
      rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))]
      rw [show 2 ^ leadingBit * 2 ^ (mantissa.log2 - leadingBit) =
          2 ^ mantissa.log2 by
        rw [Nat.mul_comm, Nat.pow_sub_mul_pow 2 hle]]
      exact Nat.log2_self_le hm
    rw [← Nat.shiftRight_eq_div_pow] at hdiv
    have hround :=
      shiftRight_le_roundShiftRightEven mantissa (mantissa.log2 - leadingBit)
    simpa [pow2, Nat.shiftLeft_eq] using hdiv.trans hround
  · have hlogLe : 2 ^ mantissa.log2 ≤ mantissa := Nat.log2_self_le hm
    have hmul := Nat.mul_le_mul_right (2 ^ (leadingBit - mantissa.log2)) hlogLe
    rw [show 2 ^ mantissa.log2 * 2 ^ (leadingBit - mantissa.log2) =
        2 ^ leadingBit by
      rw [Nat.mul_comm, Nat.pow_sub_mul_pow 2 (Nat.le_of_not_ge hle)]] at hmul
    simpa [pow2, Nat.shiftLeft_eq] using hmul

/-- Rounding to leading position `p` can produce at most the one-bit carry `2^(p+1)`. -/
theorem roundMantissaToLeadingBitEven_le_pow2_succ
    (mantissa leadingBit : Nat) :
    roundMantissaToLeadingBitEven mantissa leadingBit ≤ pow2 (leadingBit + 1) := by
  unfold roundMantissaToLeadingBitEven
  split <;> rename_i hle
  · have hdiv :
        mantissa / 2 ^ (mantissa.log2 - leadingBit) < 2 ^ (leadingBit + 1) := by
      have hexponent :
          leadingBit + 1 + (mantissa.log2 - leadingBit) = mantissa.log2 + 1 := by
        omega
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
      rw [show 2 ^ (leadingBit + 1) * 2 ^ (mantissa.log2 - leadingBit) =
          2 ^ (mantissa.log2 + 1) by
        rw [← Nat.pow_add, hexponent]]
      exact Nat.lt_log2_self
    rw [← Nat.shiftRight_eq_div_pow] at hdiv
    have hround := roundShiftRightEven_le_shiftRight_add1 mantissa
      (mantissa.log2 - leadingBit)
    simpa [pow2, Nat.shiftLeft_eq] using
      hround.trans (Nat.succ_le_iff.mpr hdiv)
  · have hlt : mantissa < 2 ^ (mantissa.log2 + 1) :=
      Nat.lt_log2_self
    have hpowPos : 0 < 2 ^ (leadingBit - mantissa.log2) := Nat.pow_pos (by decide)
    have hmul := Nat.mul_lt_mul_of_pos_right hlt hpowPos
    have hlogLe : mantissa.log2 ≤ leadingBit := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    have hexponent :
        mantissa.log2 + 1 + (leadingBit - mantissa.log2) = leadingBit + 1 := by
      omega
    rw [show 2 ^ (mantissa.log2 + 1) * 2 ^ (leadingBit - mantissa.log2) =
        2 ^ (leadingBit + 1) by
      rw [← Nat.pow_add, hexponent]] at hmul
    simpa [pow2, Nat.shiftLeft_eq] using hmul.le

/-- Rounding at the exponent that places the leading bit at `leadingBit` is direct shift-round. -/
theorem roundMantissaAtExponentEven_eq_roundMantissaToLeadingBitEven
    (mantissa leadingBit : Nat) (exponent : Int) :
    roundMantissaAtExponentEven mantissa exponent
        ((mantissa.log2 : Int) + exponent - (leadingBit : Int)) =
      roundMantissaToLeadingBitEven mantissa leadingBit := by
  by_cases hle : leadingBit ≤ mantissa.log2
  · have hexponentLe :
        exponent ≤ (mantissa.log2 : Int) + exponent - (leadingBit : Int) := by
      grind
    have hdistance :
        (((mantissa.log2 : Int) + exponent - (leadingBit : Int)) - exponent).toNat =
          mantissa.log2 - leadingBit := by
      rw [show (mantissa.log2 : Int) + exponent - (leadingBit : Int) - exponent =
          ((mantissa.log2 - leadingBit : Nat) : Int) by grind]
      rfl
    simp [roundMantissaAtExponentEven, roundMantissaToLeadingBitEven,
      hexponentLe, hle, hdistance]
  · have hnotExponentLe :
        ¬exponent ≤ (mantissa.log2 : Int) + exponent - (leadingBit : Int) := by
      grind
    have hdistance :
        (exponent - ((mantissa.log2 : Int) + exponent - (leadingBit : Int))).toNat =
          leadingBit - mantissa.log2 := by
      rw [show exponent - ((mantissa.log2 : Int) + exponent - (leadingBit : Int)) =
          ((leadingBit - mantissa.log2 : Nat) : Int) by grind]
      rfl
    simp [roundMantissaAtExponentEven, roundMantissaToLeadingBitEven,
      hnotExponentLe, hle, hdistance]

/-- Lean's logical model and `FloatFormat` compute the same minimum dyadic exponent. -/
@[simp] theorem toModel_minExponent (fmt : FloatFormat) :
    (FloatFormat.toModel fmt).minExponent = FloatFormat.ieeeMinSubnormalExponent fmt := by
  unfold Float.Model.Format.minExponent Float.Model.Format.mantissaBits
    FloatFormat.ieeeMinSubnormalExponent FloatFormat.bias FloatFormat.toModel
  change (3 : Int) - (2 : Int) ^ (fmt.expWidth - 1) - (1 + fmt.fracWidth : Nat) =
    1 - Int.ofNat (2 ^ (fmt.expWidth - 1) - 1) - Int.ofNat fmt.fracWidth
  have hp : 1 ≤ 2 ^ (fmt.expWidth - 1) :=
    Nat.one_le_pow (fmt.expWidth - 1) 2 (by decide)
  have hNat :
      (2 ^ (fmt.expWidth - 1) - 1) + 1 = 2 ^ (fmt.expWidth - 1) :=
    Nat.sub_add_cancel hp
  have hCast :
      Int.ofNat (2 ^ (fmt.expWidth - 1) - 1) + 1 =
        Int.ofNat (2 ^ (fmt.expWidth - 1)) := by
    calc
      Int.ofNat (2 ^ (fmt.expWidth - 1) - 1) + 1 =
          Int.ofNat ((2 ^ (fmt.expWidth - 1) - 1) + 1) := by simp
      _ = Int.ofNat (2 ^ (fmt.expWidth - 1)) := congrArg Int.ofNat hNat
  have hpowCast :
      Int.ofNat (2 ^ (fmt.expWidth - 1)) =
        (2 : Int) ^ (fmt.expWidth - 1) := by
    norm_num
  have hbiasCast :
      Int.ofNat (2 ^ (fmt.expWidth - 1) - 1) =
        (2 : Int) ^ (fmt.expWidth - 1) - 1 := by
    rw [hpowCast] at hCast
    omega
  rw [hbiasCast]
  push_cast
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Removing the model precision from a total exponent leaves the usual normal scale. -/
theorem totalExponent_sub_mantissaBits (fmt : FloatFormat)
    (mantissa : Nat) (exponent : Int) :
    Float.Model.totalExponent mantissa exponent -
        (FloatFormat.toModel fmt).mantissaBits =
      (mantissa.log2 : Int) + exponent - fmt.fracWidth := by
  simp [Float.Model.totalExponent, Float.Model.Format.mantissaBits,
    FloatFormat.toModel]
  omega

/--
Lean's target exponent for a format is the normal scale `log2 mantissa + exponent - fracWidth`,
floored at the least subnormal exponent.
-/
theorem targetExponent_toModel (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) :
    (FloatFormat.toModel fmt).targetExponent (Float.Model.totalExponent mantissa exponent) =
      max ((mantissa.log2 : Int) + exponent - fmt.fracWidth)
        (FloatFormat.ieeeMinSubnormalExponent fmt) := by
  rw [Float.Model.Format.targetExponent, totalExponent_sub_mantissaBits, toModel_minExponent]

/-- A mantissa below `2 ^ (p + 1)` has its leading bit at position `p` or lower. -/
private theorem log2_le_of_lt_pow2_succ {mantissa p : Nat} (h : mantissa < pow2 (p + 1)) :
    mantissa.log2 ≤ p := by
  rcases Nat.eq_zero_or_pos mantissa with hm | hm
  · subst mantissa
    simp
  · exact Nat.lt_succ_iff.mp ((Nat.log2_lt hm.ne').2 (by simpa [pow2_eq_two_pow] using h))

/-- Below the normal range, every exact dyadic is rounded on the subnormal exponent grid. -/
theorem targetExponent_eq_minSubnormal_of_lt_minNormal
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (h : (mantissa.log2 : Int) + exponent < FloatFormat.ieeeMinNormalExponent fmt) :
    (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent) =
      FloatFormat.ieeeMinSubnormalExponent fmt := by
  rw [targetExponent_toModel, max_eq_right]
  unfold FloatFormat.ieeeMinNormalExponent at h
  unfold FloatFormat.ieeeMinSubnormalExponent at ⊢
  simp only [Int.ofNat_eq_natCast] at h ⊢
  omega

/-- In the normal range, the target exponent places the leading bit at `fmt.fracWidth`. -/
theorem targetExponent_eq_normal
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (h : FloatFormat.ieeeMinNormalExponent fmt ≤ (mantissa.log2 : Int) + exponent) :
    (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent) =
      (mantissa.log2 : Int) + exponent - fmt.fracWidth := by
  rw [targetExponent_toModel, max_eq_left]
  unfold FloatFormat.ieeeMinNormalExponent at h
  unfold FloatFormat.ieeeMinSubnormalExponent at ⊢
  simp only [Int.ofNat_eq_natCast] at h ⊢
  omega

/-- A mantissa at most `2^fmt.fracWidth` stays on the minimum-exponent grid. -/
theorem targetExponent_at_minSubnormal
    (fmt : FloatFormat) (mantissa : Nat)
    (hfit : mantissa ≤ pow2 fmt.fracWidth) :
    (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa (FloatFormat.ieeeMinSubnormalExponent fmt)) =
      FloatFormat.ieeeMinSubnormalExponent fmt := by
  rw [targetExponent_toModel]
  apply max_eq_right
  have hlog := log2_le_of_lt_pow2_succ (hfit.trans_lt (show pow2 fmt.fracWidth <
    pow2 (fmt.fracWidth + 1) by simp [pow2_eq_two_pow, Nat.pow_lt_pow_right]))
  omega

/-- No bits move when a fitting mantissa is already represented at the minimum exponent. -/
theorem shiftToTargetExponent_at_minSubnormal
    (fmt : FloatFormat) (mantissa : Nat)
    (hfit : mantissa ≤ pow2 fmt.fracWidth) (accuracy : Accuracy) :
    Float.Model.UnpackedFloat.shiftToTargetExponent
        (FloatFormat.toModel fmt) mantissa (FloatFormat.ieeeMinSubnormalExponent fmt) accuracy =
      (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy,
        FloatFormat.ieeeMinSubnormalExponent fmt) := by
  unfold Float.Model.UnpackedFloat.shiftToTargetExponent
    Float.Model.UnpackedFloat.shiftToExponent
  rw [targetExponent_at_minSubnormal fmt mantissa hfit]
  simp [HShiftRight.hShiftRight, Nat.repeat]

/-- A mantissa between `2^p` and `2^(p+1)` has leading bit exactly at position `p`. -/
theorem log2_eq_fracWidth_of_normalized
    (fmt : FloatFormat) (mantissa : Nat)
    (hlow : pow2 fmt.fracWidth ≤ mantissa)
    (hhigh : mantissa < pow2 (fmt.fracWidth + 1)) :
    mantissa.log2 = fmt.fracWidth := by
  have hm : mantissa ≠ 0 :=
    Nat.ne_of_gt ((show 0 < pow2 fmt.fracWidth by simp [pow2_eq_two_pow]).trans_le hlow)
  apply (Nat.log2_eq_iff hm).2
  simpa [pow2_eq_two_pow] using And.intro hlow hhigh

/--
A mantissa below `2^(fracWidth + 1)` at exponent `k - fracWidth`, with `k` in the normal range,
needs no second normalization shift.
-/
theorem shiftToTargetExponent_normalized
    (fmt : FloatFormat) (mantissa : Nat) (k : Int) (accuracy : Accuracy)
    (hhigh : mantissa < pow2 (fmt.fracWidth + 1))
    (hk : FloatFormat.ieeeMinNormalExponent fmt ≤ k) :
    Float.Model.UnpackedFloat.shiftToTargetExponent
        (FloatFormat.toModel fmt) mantissa (k - fmt.fracWidth) accuracy =
      (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy,
        k - fmt.fracWidth) := by
  have hlog := log2_le_of_lt_pow2_succ hhigh
  have htarget :
      (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent mantissa (k - fmt.fracWidth)) ≤
        k - fmt.fracWidth := by
    rw [targetExponent_toModel]
    unfold FloatFormat.ieeeMinNormalExponent at hk
    unfold FloatFormat.ieeeMinSubnormalExponent
    simp only [Int.ofNat_eq_natCast] at hk ⊢
    omega
  have hshift :
      ((FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent mantissa (k - fmt.fracWidth)) -
        (k - fmt.fracWidth)).toNat = 0 :=
    Int.toNat_eq_zero.mpr (by omega)
  unfold Float.Model.UnpackedFloat.shiftToTargetExponent
    Float.Model.UnpackedFloat.shiftToExponent
  simp only [hshift]
  simp [HShiftRight.hShiftRight, Nat.repeat]

/-- The only extra bit produced by nearest-even normalization is shifted away exactly. -/
theorem shiftToTargetExponent_normalized_carry
    (fmt : FloatFormat) (k : Int)
    (hk : FloatFormat.ieeeMinNormalExponent fmt ≤ k) :
    Float.Model.UnpackedFloat.shiftToTargetExponent
        (FloatFormat.toModel fmt) (pow2 (fmt.fracWidth + 1))
          (k - fmt.fracWidth) .exact =
      (ExtendedMantissa.ofMantissaAndAccuracy (pow2 fmt.fracWidth) .exact,
        k + 1 - fmt.fracWidth) := by
  have hlog : (pow2 (fmt.fracWidth + 1)).log2 = fmt.fracWidth + 1 := by
    simp [pow2_eq_two_pow]
  have htarget :
      (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent (pow2 (fmt.fracWidth + 1))
            (k - fmt.fracWidth)) =
        k + 1 - fmt.fracWidth := by
    rw [targetExponent_eq_normal]
    · rw [hlog]
      push_cast
      omega
    · rw [hlog]
      push_cast
      omega
  unfold Float.Model.UnpackedFloat.shiftToTargetExponent
    Float.Model.UnpackedFloat.shiftToExponent
  rw [htarget]
  have hdistance : (k + 1 - fmt.fracWidth - (k - fmt.fracWidth)).toNat = 1 := by
    omega
  have hexponent : k - fmt.fracWidth + (1 : Nat) = k + 1 - fmt.fracWidth := by
    omega
  simp (config := { zeta := true }) only [hdistance]
  apply Prod.ext
  · simp [HShiftRight.hShiftRight, Nat.repeat,
      ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.shiftRightOne,
      pow2_eq_two_pow, pow_succ]
  · exact hexponent

/--
An exact dyadic below the normal range rounds to at most `2^p` units of the minimum exponent.

Here `p = fmt.fracWidth`; equality is the carry from the largest subnormal neighborhood to the
smallest normal value.
-/
theorem roundMantissaAtExponentEven_minSubnormal_le_pow2
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hk : (mantissa.log2 : Int) + exponent <
      FloatFormat.ieeeMinNormalExponent fmt) :
    roundMantissaAtExponentEven mantissa exponent (FloatFormat.ieeeMinSubnormalExponent fmt) ≤
      pow2 fmt.fracWidth := by
  have hscale :
      FloatFormat.ieeeMinSubnormalExponent fmt + fmt.fracWidth =
        FloatFormat.ieeeMinNormalExponent fmt := by
    unfold FloatFormat.ieeeMinSubnormalExponent FloatFormat.ieeeMinNormalExponent
    simp only [Int.ofNat_eq_natCast]
    ring
  by_cases hle : exponent ≤ FloatFormat.ieeeMinSubnormalExponent fmt
  · let shift := (FloatFormat.ieeeMinSubnormalExponent fmt - exponent).toNat
    have hshiftInt : (shift : Int) = FloatFormat.ieeeMinSubnormalExponent fmt - exponent :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hle)
    have hlogInt :
        (mantissa.log2 : Int) + 1 ≤ (fmt.fracWidth : Int) + shift := by
      rw [hshiftInt]
      omega
    have hlogNat : mantissa.log2 + 1 ≤ fmt.fracWidth + shift := by
      exact_mod_cast hlogInt
    have hmLt : mantissa < 2 ^ (fmt.fracWidth + shift) :=
      (Nat.lt_log2_self (n := mantissa)).trans_le
        (Nat.pow_le_pow_right (by decide) hlogNat)
    have hq : mantissa >>> shift < pow2 fmt.fracWidth := by
      rw [Nat.shiftRight_eq_div_pow]
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
      rw [pow2_eq_two_pow, ← Nat.pow_add]
      exact hmLt
    have hround := roundShiftRightEven_le_shiftRight_add1 mantissa shift
    simp only [roundMantissaAtExponentEven, hle, ite_true]
    change roundShiftRightEven mantissa shift ≤ pow2 fmt.fracWidth
    exact hround.trans (Nat.succ_le_iff.mpr hq)
  · have hlt : FloatFormat.ieeeMinSubnormalExponent fmt < exponent := lt_of_not_ge hle
    let shift := (exponent - FloatFormat.ieeeMinSubnormalExponent fmt).toNat
    have hshiftInt : (shift : Int) = exponent - FloatFormat.ieeeMinSubnormalExponent fmt :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hlt.le)
    have hlogInt :
        (mantissa.log2 : Int) + shift < fmt.fracWidth := by
      rw [hshiftInt]
      omega
    have hlogNat : mantissa.log2 + shift < fmt.fracWidth := by
      exact_mod_cast hlogInt
    have hraw :=
      Nat.shiftLeft_lt (m := shift) (Nat.lt_log2_self (n := mantissa))
    have hexponent : mantissa.log2 + 1 + shift ≤ fmt.fracWidth := by omega
    have hpow : 2 ^ (mantissa.log2 + 1 + shift) ≤ 2 ^ fmt.fracWidth :=
      Nat.pow_le_pow_right (by decide) hexponent
    simp only [roundMantissaAtExponentEven, hle, ite_false]
    change mantissa <<< shift ≤ pow2 fmt.fracWidth
    simpa [pow2_eq_two_pow] using (hraw.trans_le hpow).le

/-- Lean's decrease-then-shift normalization agrees with direct nearest-even rounding. -/
theorem roundedMantissa_decrease_shift_exact
    (mantissa : Nat) (exponent targetExponent : Int) :
    let decreased :=
      Float.Model.UnpackedFloat.decreaseExponent mantissa exponent targetExponent
    let shifted := Float.Model.UnpackedFloat.shiftToExponent
      decreased.1 decreased.2 .exact targetExponent
    (shifted.1.roundedMantissa, shifted.2) =
      (roundMantissaAtExponentEven mantissa exponent targetExponent, targetExponent) := by
  by_cases hle : exponent ≤ targetExponent
  · have hleft : (exponent - targetExponent).toNat = 0 :=
      Int.toNat_eq_zero.mpr (by grind)
    have hdecreased :
        Float.Model.UnpackedFloat.decreaseExponent mantissa exponent targetExponent =
          (mantissa, exponent) := by
      unfold Float.Model.UnpackedFloat.decreaseExponent
      simp [hleft]
    have hrightInt : ((targetExponent - exponent).toNat : Int) =
        targetExponent - exponent := by
      rw [Int.toNat_of_nonneg (by grind)]
    have hshifted :
        Float.Model.UnpackedFloat.shiftToExponent mantissa exponent .exact targetExponent =
          (ExtendedMantissa.ofMantissaAndAccuracy mantissa .exact >>>
            (targetExponent - exponent).toNat, targetExponent) := by
      unfold Float.Model.UnpackedFloat.shiftToExponent
      apply Prod.ext
      · rfl
      · dsimp only [Prod.snd]
        rw [hrightInt]
        grind
    simp only [hdecreased, hshifted]
    apply Prod.ext
    · dsimp only [Prod.fst]
      rw [roundedMantissa_shift_exact]
      simp [roundMantissaAtExponentEven, hle]
    · rfl
  · have hleftInt : ((exponent - targetExponent).toNat : Int) =
        exponent - targetExponent := by
      rw [Int.toNat_of_nonneg (by grind)]
    have hdecreased :
        Float.Model.UnpackedFloat.decreaseExponent mantissa exponent targetExponent =
          (mantissa <<< (exponent - targetExponent).toNat, targetExponent) := by
      unfold Float.Model.UnpackedFloat.decreaseExponent
      apply Prod.ext
      · rfl
      · dsimp only [Prod.snd]
        rw [hleftInt]
        grind
    have hshifted :
        Float.Model.UnpackedFloat.shiftToExponent
            (mantissa <<< (exponent - targetExponent).toNat)
            targetExponent .exact targetExponent =
          (ExtendedMantissa.ofMantissaAndAccuracy
            (mantissa <<< (exponent - targetExponent).toNat) .exact, targetExponent) := by
      unfold Float.Model.UnpackedFloat.shiftToExponent
      simp [HShiftRight.hShiftRight, Nat.repeat,
        ExtendedMantissa.ofMantissaAndAccuracy]
    simp only [hdecreased, hshifted]
    apply Prod.ext
    · dsimp only [Prod.fst]
      simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
        ExtendedMantissa.ofMantissaAndAccuracy, Accuracy.roundToNearestEven,
        roundMantissaAtExponentEven, hle]
    · rfl

/-- Decreasing an exact dyadic exponent preserves the leading binary position. -/
theorem totalExponent_decreaseExponent
    (mantissa : Nat) (exponent targetExponent : Int) (hm : mantissa ≠ 0) :
    let decreased := Float.Model.UnpackedFloat.decreaseExponent
      mantissa exponent targetExponent
    Float.Model.totalExponent decreased.1 decreased.2 =
      Float.Model.totalExponent mantissa exponent := by
  by_cases hle : exponent ≤ targetExponent
  · have hshift : (exponent - targetExponent).toNat = 0 :=
      Int.toNat_eq_zero.mpr (by grind)
    unfold Float.Model.UnpackedFloat.decreaseExponent
    simp [hshift]
  · have hshiftInt : ((exponent - targetExponent).toNat : Int) =
        exponent - targetExponent := by
      rw [Int.toNat_of_nonneg (by grind)]
    unfold Float.Model.UnpackedFloat.decreaseExponent Float.Model.totalExponent
    dsimp only [Prod.fst, Prod.snd]
    rw [Nat.log2_shiftLeft_of_ne_zero mantissa
      (exponent - targetExponent).toNat hm]
    rw [Nat.cast_add, hshiftInt]
    grind

/-- The first exact model-rounding stage uses the original dyadic's target exponent. -/
theorem roundedMantissa_decrease_shiftToTarget_exact
    (spec : Float.Model.Format) (mantissa : Nat) (exponent : Int) :
    let targetExponent := spec.targetExponent (Float.Model.totalExponent mantissa exponent)
    let decreased :=
      Float.Model.UnpackedFloat.decreaseExponent mantissa exponent targetExponent
    let shifted := Float.Model.UnpackedFloat.shiftToTargetExponent
      spec decreased.1 decreased.2 .exact
    (shifted.1.roundedMantissa, shifted.2) =
      (roundMantissaAtExponentEven mantissa exponent targetExponent, targetExponent) := by
  let targetExponent := spec.targetExponent (Float.Model.totalExponent mantissa exponent)
  let decreased :=
    Float.Model.UnpackedFloat.decreaseExponent mantissa exponent targetExponent
  have hshift :
      Float.Model.UnpackedFloat.shiftToTargetExponent
          spec decreased.1 decreased.2 .exact =
        Float.Model.UnpackedFloat.shiftToExponent
          decreased.1 decreased.2 .exact targetExponent := by
    by_cases hm : mantissa = 0
    · subst mantissa
      have hbits : 1 ≤ spec.mantissaBits := by simp [Float.Model.Format.mantissaBits]
      simp only [decreased, targetExponent, Float.Model.UnpackedFloat.decreaseExponent,
        Float.Model.UnpackedFloat.shiftToTargetExponent,
        Float.Model.UnpackedFloat.shiftToExponent, Nat.zero_shiftLeft,
        Float.Model.totalExponent, Float.Model.Format.targetExponent, Nat.log2_zero] at *
      congr 2 <;> omega
    · have htotal :
          Float.Model.totalExponent decreased.1 decreased.2 =
            Float.Model.totalExponent mantissa exponent :=
        totalExponent_decreaseExponent mantissa exponent targetExponent hm
      unfold Float.Model.UnpackedFloat.shiftToTargetExponent
      rw [htotal]
  change
    ((Float.Model.UnpackedFloat.shiftToTargetExponent
        spec decreased.1 decreased.2 .exact).1.roundedMantissa,
      (Float.Model.UnpackedFloat.shiftToTargetExponent
        spec decreased.1 decreased.2 .exact).2) =
      (roundMantissaAtExponentEven mantissa exponent targetExponent, targetExponent)
  rw [hshift]
  exact roundedMantissa_decrease_shift_exact mantissa exponent targetExponent

/-- A zero rounded mantissa remains signed zero, independently of the provisional exponent. -/
@[simp] theorem finishRoundedMantissa_zero
    (spec : Float.Model.Format) (sign : Sign) (exponent : Int) :
    finishRoundedMantissa spec sign (0, exponent) = .zero sign := by
  unfold finishRoundedMantissa Float.Model.UnpackedFloat.shiftToTargetExponent
    Float.Model.UnpackedFloat.shiftToExponent
  simp only [ExtendedMantissa.ofMantissaAndAccuracy,
    zero_extendedMantissa_shiftRight]
  simp

/-- A nonzero rounded mantissa on the minimum-exponent grid, up to the smallest normal
value, needs no second shift. -/
theorem finishRoundedMantissa_at_minSubnormal
    (fmt : FloatFormat) (sign : Sign) (mantissa : Nat)
    (hm : mantissa ≠ 0) (hfit : mantissa ≤ pow2 fmt.fracWidth) :
    finishRoundedMantissa (FloatFormat.toModel fmt) sign
        (mantissa, FloatFormat.ieeeMinSubnormalExponent fmt) =
      .finite sign mantissa (FloatFormat.ieeeMinSubnormalExponent fmt)
        (Nat.pos_of_ne_zero hm) := by
  simp only [finishRoundedMantissa,
    shiftToTargetExponent_at_minSubnormal fmt mantissa hfit .exact,
    ExtendedMantissa.ofMantissaAndAccuracy, hm, ↓reduceDIte]

/-- A normalized rounded mantissa remains unchanged in the second rounding stage. -/
theorem finishRoundedMantissa_normalized
    (fmt : FloatFormat) (sign : Sign) (mantissa : Nat) (k : Int)
    (hlow : pow2 fmt.fracWidth ≤ mantissa)
    (hhigh : mantissa < pow2 (fmt.fracWidth + 1))
    (hk : FloatFormat.ieeeMinNormalExponent fmt ≤ k) :
    finishRoundedMantissa (FloatFormat.toModel fmt) sign
        (mantissa, k - fmt.fracWidth) =
      .finite sign mantissa (k - fmt.fracWidth)
        (Nat.pos_of_ne_zero
          (Nat.ne_of_gt ((show 0 < pow2 fmt.fracWidth by
            simp [pow2_eq_two_pow]).trans_le hlow))) := by
  have hm : mantissa ≠ 0 :=
    Nat.ne_of_gt ((show 0 < pow2 fmt.fracWidth by
      simp [pow2_eq_two_pow]).trans_le hlow)
  unfold finishRoundedMantissa
  dsimp only [Prod.fst, Prod.snd]
  simp only [shiftToTargetExponent_normalized fmt mantissa k .exact hhigh hk]
  simp [ExtendedMantissa.ofMantissaAndAccuracy, hm]

/-- A one-bit normalization carry becomes `2^p` at the next exponent. -/
theorem finishRoundedMantissa_normalized_carry
    (fmt : FloatFormat) (sign : Sign) (k : Int)
    (hk : FloatFormat.ieeeMinNormalExponent fmt ≤ k) :
    finishRoundedMantissa (FloatFormat.toModel fmt) sign
        (pow2 (fmt.fracWidth + 1), k - fmt.fracWidth) =
      .finite sign (pow2 fmt.fracWidth) (k + 1 - fmt.fracWidth)
        (Nat.pos_of_ne_zero (by simp [pow2_eq_two_pow])) := by
  unfold finishRoundedMantissa
  dsimp only [Prod.fst, Prod.snd]
  simp only [shiftToTargetExponent_normalized_carry fmt k hk]
  simp [ExtendedMantissa.ofMantissaAndAccuracy, pow2_eq_two_pow]

/-- The final stage of `roundWithAccuracy` is `finishRoundedMantissa`. -/
theorem roundWithAccuracy_eq_finishRoundedMantissa
    (spec : Float.Model.Format) (sign : Sign) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) :
    Float.Model.UnpackedFloat.roundWithAccuracy spec sign mantissa exponent accuracy =
      finishRoundedMantissa spec sign
        ((Float.Model.UnpackedFloat.shiftToTargetExponent
            spec mantissa exponent accuracy).1.roundedMantissa,
          (Float.Model.UnpackedFloat.shiftToTargetExponent
            spec mantissa exponent accuracy).2) := by
  rfl

/--
`roundWithAccuracy` agrees with unrestricted rounding when no preliminary left shift is needed.
-/
theorem roundWithAccuracy_exact_eq_round_of_le_targetExponent
    (spec : Float.Model.Format) (sign : Sign) (mantissa : Nat) (exponent : Int)
    (h : exponent ≤ spec.targetExponent (Float.Model.totalExponent mantissa exponent)) :
    Float.Model.UnpackedFloat.roundWithAccuracy spec sign mantissa exponent .exact =
      Float.Model.UnpackedFloat.round spec sign mantissa exponent := by
  unfold Float.Model.UnpackedFloat.round Float.Model.UnpackedFloat.decreaseExponent
  have hshift : (exponent - spec.targetExponent
      (Float.Model.totalExponent mantissa exponent)).toNat = 0 :=
    Int.toNat_eq_zero.mpr (by grind)
  simp [hshift]

/-- Exact dyadic model rounding factors through the direct target-exponent rounder. -/
theorem round_exact_eq_finishRoundedMantissa
    (spec : Float.Model.Format) (sign : Sign) (mantissa : Nat) (exponent : Int) :
    Float.Model.UnpackedFloat.round spec sign mantissa exponent =
      finishRoundedMantissa spec sign
        (roundMantissaAtExponentEven mantissa exponent
          (spec.targetExponent (Float.Model.totalExponent mantissa exponent)),
        spec.targetExponent (Float.Model.totalExponent mantissa exponent)) := by
  let targetExponent := spec.targetExponent (Float.Model.totalExponent mantissa exponent)
  let decreased :=
    Float.Model.UnpackedFloat.decreaseExponent mantissa exponent targetExponent
  have hfirst := roundedMantissa_decrease_shiftToTarget_exact spec mantissa exponent
  change finishRoundedMantissa spec sign
      ((Float.Model.UnpackedFloat.shiftToTargetExponent
          spec decreased.1 decreased.2 .exact).1.roundedMantissa,
        (Float.Model.UnpackedFloat.shiftToTargetExponent
          spec decreased.1 decreased.2 .exact).2) =
    finishRoundedMantissa spec sign
      (roundMantissaAtExponentEven mantissa exponent targetExponent, targetExponent)
  exact congrArg (finishRoundedMantissa spec sign) hfirst

end Model
end FloatLib.Floats.Formats.BinaryInterchange
