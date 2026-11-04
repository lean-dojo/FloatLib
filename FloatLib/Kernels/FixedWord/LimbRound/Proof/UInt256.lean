/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.ShiftRightJam
public import FloatLib.Kernels.FixedWord.LimbRound.Proof.UInt128
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic

/-!
# Verified four-limb rounding

Four-limb shifts, sticky-bit normalization, and nearest-even rounding get their natural-number
meanings here, and with them multiplication and fused-operation backends can reuse this layer
without converting compiled arithmetic to `Nat`.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

namespace UInt256

/-- Dividing a bounded low part plus a radix multiple recovers the upper coefficient. -/
private theorem low_add_upper_mul_pow_div
    (low upper width : Nat) (hlow : low < 2 ^ width) :
    (low + upper * 2 ^ width) / 2 ^ width = upper := by
  rw [Nat.mul_comm upper]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos width)]
  rw [Nat.div_eq_of_lt hlow, zero_add]

/-- A four-limb value is its low limb pair plus its high limb pair scaled by `2^128`. -/
private theorem toNat_eq_pairs (value : UInt256) :
    value.toNat =
      (value.limb0.toNat + value.limb1.toNat * 2 ^ 64) +
        (value.limb2.toNat + value.limb3.toNat * 2 ^ 64) * 2 ^ 128 := by
  unfold UInt256.toNat
  rw [show (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 128 by norm_num]
  ring

/-- A pair of native limbs is below `2^128`. -/
private theorem pair_lt (low high : UInt64) :
    low.toNat + high.toNat * 2 ^ 64 < 2 ^ 128 := by
  have hlow := low.toNat_lt
  have hhigh := high.toNat_lt
  omega

/--
Shifting three limbs right by at most one word gives two shifted limb pairs. The low result limb
joins the top of `low` with the bottom bits of `middle`, and the high one joins the rest of `middle`
with `high`.
-/
private theorem three_limbs_div_two_pow (low middle high shift : Nat) (hshift : shift ≤ 64) :
    (low + middle * 2 ^ 64 + high * 2 ^ 128) / 2 ^ shift =
      low / 2 ^ shift + (middle % 2 ^ shift) * 2 ^ (64 - shift) +
        (middle / 2 ^ shift + high * 2 ^ (64 - shift)) * 2 ^ 64 := by
  have hpower : 2 ^ shift * 2 ^ (64 - shift) = 2 ^ 64 := by
    rw [← pow_add, Nat.add_sub_of_le hshift]
  have hlow := Nat.mod_add_div low (2 ^ shift)
  have hmiddle := Nat.mod_add_div middle (2 ^ shift)
  have hvalue :
      low + middle * 2 ^ 64 + high * 2 ^ 128 =
        low % 2 ^ shift +
          (low / 2 ^ shift + (middle % 2 ^ shift) * 2 ^ (64 - shift) +
            (middle / 2 ^ shift + high * 2 ^ (64 - shift)) * 2 ^ 64) * 2 ^ shift := by
    conv_lhs => rw [← hlow, ← hmiddle]
    rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, ← hpower]
    ring
  rw [hvalue, low_add_upper_mul_pow_div _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos shift))]

/-- Modulo at most `2^128`, a four-limb value depends only on its lower two limbs. -/
private theorem mod_two_pow_eq_low_pair
    (value : UInt256) (width : Nat) (hwidth : width ≤ 128) :
    value.toNat % 2 ^ width =
      (value.limb0.toNat + value.limb1.toNat * 2 ^ 64) %
        2 ^ width := by
  let low :=
    value.limb0.toNat + value.limb1.toNat * 2 ^ 64
  let high :=
    value.limb2.toNat + value.limb3.toNat * 2 ^ 64
  have hpower :
      2 ^ 128 = 2 ^ width * 2 ^ (128 - width) := by
    rw [← pow_add, Nat.add_sub_of_le hwidth]
  have hvalue :
      value.toNat =
        low + (high * 2 ^ (128 - width)) * 2 ^ width := by
    unfold low high
    rw [toNat_eq_pairs, hpower]
    ring
  rw [hvalue, Nat.add_mul_mod_self_right]

/-- Modulo at most `2^64`, a two-limb value depends only on its low limb. -/
private theorem low_pair_mod_two_pow_of_le64
    (value : UInt256) (width : Nat) (hwidth : width ≤ 64) :
    (value.limb0.toNat + value.limb1.toNat * 2 ^ 64) %
        2 ^ width =
      value.limb0.toNat % 2 ^ width := by
  have hpower :
      2 ^ 64 = 2 ^ width * 2 ^ (64 - width) := by
    rw [← pow_add, Nat.add_sub_of_le hwidth]
  rw [hpower]
  rw [show
    value.limb1.toNat * (2 ^ width * 2 ^ (64 - width)) =
      (value.limb1.toNat * 2 ^ (64 - width)) * 2 ^ width by ring]
  rw [Nat.add_mul_mod_self_right]

/--
Reducing `low + upper * 2 ^ k` modulo `2 ^ (k + m)`, for `low < 2 ^ k`, truncates only `upper`:
the shared step of the two- and four-limb remainder tests.
-/
private theorem add_mul_two_pow_mod_two_pow_add {low upper k : Nat} (m : Nat)
    (hlow : low < 2 ^ k) :
    (low + upper * 2 ^ k) % 2 ^ (k + m) = low + (upper % 2 ^ m) * 2 ^ k := by
  rw [pow_add, Nat.mod_mul, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlow,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hlow, Nat.zero_add,
    Nat.mul_comm]

/-- Above 64 bits, reducing a two-limb value truncates only its upper limb. -/
private theorem low_pair_mod_two_pow_of_gt64
    (value : UInt256) (width : Nat) (hlarge : 64 < width) :
    (value.limb0.toNat + value.limb1.toNat * 2 ^ 64) %
        2 ^ width =
      value.limb0.toNat +
        (value.limb1.toNat % 2 ^ (width - 64)) * 2 ^ 64 := by
  obtain ⟨inner, rfl⟩ : ∃ inner, width = 64 + inner := ⟨width - 64, by omega⟩
  rw [Nat.add_sub_cancel_left]
  exact add_mul_two_pow_mod_two_pow_add inner value.limb0.toNat_lt

/-- The four-limb low-bit predicate is exact while the inspected window stays in two limbs. -/
private theorem hasNonzeroBelow_eq_of_le128
    (value : UInt256) (width : Nat) (hwidth : width ≤ 128) :
    hasNonzeroBelow value width =
      (value.toNat % 2 ^ width != 0) := by
  rw [mod_two_pow_eq_low_pair value width hwidth]
  by_cases hzero : width = 0
  · subst hzero
    change
      false =
        ((value.limb0.toNat + value.limb1.toNat * 2 ^ 64) % 1 != 0)
    rw [Nat.mod_one]
    decide
  by_cases hsmall : width < 64
  · have hpositive : 0 < width := Nat.pos_of_ne_zero hzero
    unfold hasNonzeroBelow
    simp only [beq_iff_eq, hzero, ite_false, hsmall, ite_true]
    rw [low_pair_mod_two_pow_of_le64 value width hsmall.le]
    have hbits :=
      uint64_lowBits_toNat value.limb0 width hsmall
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne]
    rw [← hbits]
    exact (uint64_toNat_eq_zero _).not.symm
  by_cases hword : width = 64
  · subst hword
    change
      (value.limb0 != 0) =
        ((value.limb0.toNat + value.limb1.toNat * 2 ^ 64) %
          2 ^ 64 != 0)
    rw [low_pair_mod_two_pow_of_le64 value 64 (by omega)]
    rw [Nat.mod_eq_of_lt value.limb0.toNat_lt]
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne]
    exact (uint64_toNat_eq_zero _).not.symm
  by_cases hbelow : width < 128
  · have hlarge : 64 < width := by omega
    let inner := width - 64
    have hinnerPositive : 0 < inner := by omega
    have hinner : inner < 64 := by omega
    unfold hasNonzeroBelow
    simp only [beq_iff_eq, hzero, ite_false, hsmall, hword,
      hbelow, ite_true]
    rw [low_pair_mod_two_pow_of_gt64 value width hlarge]
    have hbits :=
      uint64_lowBits_toNat value.limb1 inner hinner
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, bne_iff_ne]
    rw [← hbits]
    simpa only [UInt128.toNat] using
      (UInt128.toNat_ne_zero_iff
        (⟨value.limb1 &&& ((1 <<< UInt64.ofNat inner) - 1),
          value.limb0⟩ : UInt128)).symm
  · have heq : width = 128 := by omega
    subst heq
    change
      (value.limb0 != 0 || value.limb1 != 0) =
        ((value.limb0.toNat + value.limb1.toNat * 2 ^ 64) %
          2 ^ 128 != 0)
    rw [Nat.mod_eq_of_lt (pair_lt value.limb0 value.limb1)]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, bne_iff_ne]
    simpa only [UInt128.toNat] using
      (UInt128.toNat_ne_zero_iff
        (⟨value.limb1, value.limb0⟩ : UInt128)).symm

/-- Reducing a four-limb value above 128 bits preserves its low half and truncates its high half. -/
private theorem mod_two_pow_eq_halves
    (value : UInt256) (inner : Nat) :
    value.toNat % 2 ^ (128 + inner) =
      value.low128.toNat +
        ((⟨value.limb3, value.limb2⟩ : UInt128).toNat %
          2 ^ inner) * 2 ^ 128 := by
  have hhalves : value.toNat =
      value.low128.toNat + (⟨value.limb3, value.limb2⟩ : UInt128).toNat * 2 ^ 128 := by
    dsimp [UInt256.low128]
    unfold UInt128.toNat
    exact toNat_eq_pairs value
  rw [hhalves]
  exact add_mul_two_pow_mod_two_pow_add inner (UInt128.toNat_lt _)

/--
The fixed-limb low-bit predicate agrees with the natural-number remainder test at every width.

Widths above the four-limb capacity inspect the complete value, matching reduction modulo any
power of two at least `2^256`.
-/
theorem hasNonzeroBelow_eq
    (value : UInt256) (width : Nat) :
    hasNonzeroBelow value width =
      (value.toNat % 2 ^ width != 0) := by
  by_cases hlow : width ≤ 128
  · exact hasNonzeroBelow_eq_of_le128 value width hlow
  by_cases hcapacity : width ≤ 256
  · let inner := width - 128
    let lower := UInt256.ofUInt128 value.low128
    let upper :=
      UInt256.ofUInt128 (⟨value.limb3, value.limb2⟩ : UInt128)
    have hinnerPositive : 0 < inner := by
      unfold inner
      omega
    have hinner : inner ≤ 128 := by
      unfold inner
      omega
    have hruntime :
        hasNonzeroBelow value width =
          (hasNonzeroBelow lower 128 ||
            hasNonzeroBelow upper inner) := by
      by_cases hbelow192 : width < 192
      · have hinnerSmall : inner < 64 := by
          unfold inner
          omega
        simp [hasNonzeroBelow, lower, upper, UInt256.ofUInt128,
          UInt256.low128, inner, Bool.or_assoc,
          show width ≠ 0 by omega,
          show ¬width < 64 by omega,
          show width ≠ 64 by omega,
          show ¬width < 128 by omega,
          show width ≠ 128 by omega,
          hbelow192, hinnerPositive.ne', hinnerSmall]
      · by_cases heq192 : width = 192
        · subst width
          simp [hasNonzeroBelow, lower, upper, UInt256.ofUInt128,
            UInt256.low128, inner, Bool.or_assoc]
        · by_cases hbelow256 : width < 256
          · have hinnerLarge : 64 < inner := by
              unfold inner
              omega
            have hinnerSmall : inner < 128 := by
              unfold inner
              omega
            have hoffset :
                width - 192 = width - 128 - 64 := by
              omega
            simp [hasNonzeroBelow, lower, upper, UInt256.ofUInt128,
              UInt256.low128, inner, Bool.or_assoc,
              show width ≠ 0 by omega,
              show ¬width < 64 by omega,
              show width ≠ 64 by omega,
              show ¬width < 128 by omega,
              show width ≠ 128 by omega,
              show ¬width < 192 by omega,
              show width ≠ 192 by omega,
              hbelow256, hinnerPositive.ne',
              show ¬inner < 64 by omega,
              show inner ≠ 64 by omega, hinnerSmall, hoffset]
          · have heq256 : width = 256 := by omega
            subst width
            simp [hasNonzeroBelow, lower, upper, UInt256.ofUInt128,
              UInt256.low128, inner, Bool.or_assoc]
    have hwidthEq : width = 128 + inner := by
      unfold inner
      omega
    have hlowerNat : lower.toNat = value.low128.toNat := by
      simp [lower]
    have hupperNat :
        upper.toNat =
          (⟨value.limb3, value.limb2⟩ : UInt128).toNat := by
      simp [upper]
    rw [hruntime, hwidthEq,
      mod_two_pow_eq_halves value inner,
      hasNonzeroBelow_eq_of_le128 lower 128 (by omega),
      hasNonzeroBelow_eq_of_le128 upper inner hinner,
      hlowerNat, hupperNat]
    rw [Nat.mod_eq_of_lt (UInt128.toNat_lt value.low128)]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, bne_iff_ne]
    constructor
    · rintro (hlower | hupper) hsum
      · exact hlower (Nat.add_eq_zero_iff.mp hsum).1
      · exact hupper
          ((Nat.mul_eq_zero.mp (Nat.add_eq_zero_iff.mp hsum).2).resolve_right
            (by positivity))
    · intro hsum
      by_contra hparts
      simp only [not_or, not_ne_iff] at hparts
      exact hsum (by simp [hparts.1, hparts.2])
  · have hvalue :
        value.toNat < 2 ^ width := by
      exact lt_of_lt_of_le value.toNat_lt
        (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.mod_eq_of_lt hvalue]
    unfold hasNonzeroBelow
    simp only [beq_iff_eq, show width ≠ 0 by omega, ite_false,
      show ¬width < 64 by omega, show width ≠ 64 by omega,
      show ¬width < 128 by omega, show width ≠ 128 by omega,
      show ¬width < 192 by omega, show width ≠ 192 by omega,
      show ¬width < 256 by omega]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, bne_iff_ne]
    simp [UInt256.toNat, uint64_toNat_eq_zero]
    tauto

/-- Four-limb shifting by less than one word agrees with `>>>` when the quotient fits two limbs. -/
theorem shiftRight128_toNat_of_lt64
    (value : UInt256) (shift : Nat)
    (hshift : shift < 64)
    (htopWord : value.limb3 = 0)
    (htopBits : value.limb2.toNat < 2 ^ shift) :
    (shiftRight128 value shift).toNat = value.toNat >>> shift := by
  rcases Nat.eq_zero_or_pos shift with rfl | hpositive
  · have hlimb2 : value.limb2.toNat = 0 := by simpa using htopBits
    unfold shiftRight128 UInt128.toNat
    simp [UInt256.toNat, htopWord, hlimb2]
  have hlow := FloatLib.Numerics.FixedWord.shiftedPair_toNat
    value.limb0 value.limb1 shift
    hpositive hshift
  have hhigh := FloatLib.Numerics.FixedWord.shiftedPair_toNat
    value.limb1 value.limb2 shift
    hpositive hshift
  have hvalue :
      value.toNat =
        value.limb0.toNat + value.limb1.toNat * 2 ^ 64 +
          value.limb2.toNat * 2 ^ 128 := by
    simp [UInt256.toNat, htopWord]
  unfold shiftRight128 UInt128.toNat
  simp only [beq_iff_eq, Nat.ne_of_gt hpositive, ite_false,
    hshift, ite_true]
  rw [hlow, hhigh, Nat.mod_eq_of_lt htopBits, Nat.shiftRight_eq_div_pow, hvalue,
    three_limbs_div_two_pow _ _ _ _ hshift.le]

/-- When the top limb is zero, a one-word shift selects the middle two limbs. -/
theorem shiftRight128_toNat_of_eq64
    (value : UInt256) (htopWord : value.limb3 = 0) :
    (shiftRight128 value 64).toNat = value.toNat >>> 64 := by
  have hlow : value.limb0.toNat < 2 ^ 64 :=
    value.limb0.toNat_lt
  let upper :=
    value.limb1.toNat + value.limb2.toNat * 2 ^ 64
  have hvalue :
      value.toNat = value.limb0.toNat + upper * 2 ^ 64 := by
    unfold UInt256.toNat upper
    simp only [htopWord, UInt64.toNat_zero, zero_mul, add_zero]
    rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num]
    ring
  unfold shiftRight128 UInt128.toNat
  simp only [OfNat.ofNat, Nat.reduceBEq, ite_false,
    Nat.reduceLT, ite_true, Bool.false_eq_true]
  rw [Nat.shiftRight_eq_div_pow, hvalue]
  exact (low_add_upper_mul_pow_div value.limb0.toNat upper 64 hlow).symm

/-- Four-to-two-limb shifting agrees with `>>>` for every shift at or above the half-width. -/
private theorem shiftRight128_toNat_of_ge128
    (value : UInt256) (inner : Nat) :
    (shiftRight128 value (128 + inner)).toNat =
      value.toNat / 2 ^ (128 + inner) := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, toNat_eq_pairs,
    low_add_upper_mul_pow_div _ _ 128 (pair_lt _ _)]
  by_cases hzero : inner = 0
  · subst inner
    unfold shiftRight128 UInt128.toNat
    norm_num
  by_cases hsmall : inner < 64
  · have hpositive : 0 < inner := Nat.pos_of_ne_zero hzero
    have hlowShift :=
      FloatLib.Numerics.FixedWord.shiftedPair_toNat
        value.limb2 value.limb3 inner
        hpositive hsmall
    have hhighShift :
        (value.limb3 >>> UInt64.ofNat inner).toNat =
          value.limb3.toNat / 2 ^ inner := by
      rw [FloatLib.Numerics.FixedWord.shiftRight_toNat
        value.limb3 inner hsmall,
        Nat.shiftRight_eq_div_pow]
    unfold shiftRight128 UInt128.toNat
    simp only [show 128 + inner ≠ 0 by omega, beq_iff_eq, ite_false,
      show ¬128 + inner < 64 by omega,
      show 128 + inner ≠ 64 by omega,
      show ¬128 + inner < 128 by omega,
      show 128 + inner ≠ 128 by omega,
      show 128 + inner < 192 by omega, ite_true]
    have hinnerSub : 128 + inner - 128 = inner := by omega
    rw [hinnerSub]
    rw [hlowShift, hhighShift]
    have hsplit :=
      three_limbs_div_two_pow value.limb2.toNat value.limb3.toNat 0 inner hsmall.le
    simp only [zero_mul, add_zero] at hsplit
    exact hsplit.symm
  · by_cases hword : inner = 64
    · subst inner
      unfold shiftRight128 UInt128.toNat
      norm_num
      symm
      exact low_add_upper_mul_pow_div
        value.limb2.toNat value.limb3.toNat 64
          value.limb2.toNat_lt
    · by_cases htop : inner < 128
      · have hlarge : 64 < inner := by omega
        let tail := inner - 64
        have htailPositive : 0 < tail := by
          unfold tail
          omega
        have htail : tail < 64 := by
          unfold tail
          omega
        have hinnerEq : inner = 64 + tail := by
          unfold tail
          omega
        have hshifted :
            (value.limb3 >>> UInt64.ofNat tail).toNat =
              value.limb3.toNat / 2 ^ tail := by
          rw [FloatLib.Numerics.FixedWord.shiftRight_toNat
            value.limb3 tail htail,
            Nat.shiftRight_eq_div_pow]
        unfold shiftRight128 UInt128.toNat
        simp only [show 128 + inner ≠ 0 by omega, beq_iff_eq, ite_false,
          show ¬128 + inner < 64 by omega,
          show 128 + inner ≠ 64 by omega,
          show ¬128 + inner < 128 by omega,
          show 128 + inner ≠ 128 by omega,
          show ¬128 + inner < 192 by omega,
          show 128 + inner < 256 by omega, ite_true,
          UInt64.toNat_zero, zero_mul, add_zero]
        rw [show 128 + inner - 192 = tail by omega, hshifted,
          hinnerEq, pow_add, ← Nat.div_div_eq_div_mul]
        have hupperDiv :
            (value.limb2.toNat +
                value.limb3.toNat * 2 ^ 64) / 2 ^ 64 =
              value.limb3.toNat :=
          low_add_upper_mul_pow_div
            value.limb2.toNat value.limb3.toNat 64
              value.limb2.toNat_lt
        rw [hupperDiv]
      · have hlarge : 128 ≤ inner := Nat.le_of_not_gt htop
        have hdivision :
            (value.limb2.toNat + value.limb3.toNat * 2 ^ 64) / 2 ^ inner = 0 := by
          apply Nat.div_eq_of_lt
          exact (pair_lt _ _).trans_le
            (Nat.pow_le_pow_right (by decide) hlarge)
        unfold shiftRight128 UInt128.toNat
        simp only [show 128 + inner ≠ 0 by omega, beq_iff_eq, ite_false,
          show ¬128 + inner < 64 by omega,
          show 128 + inner ≠ 64 by omega,
          show ¬128 + inner < 128 by omega,
          show 128 + inner ≠ 128 by omega,
          show ¬128 + inner < 192 by omega,
          show ¬128 + inner < 256 by omega,
          UInt64.toNat_zero, zero_mul, add_zero]
        exact hdivision.symm

/--
Four-limb shifting agrees with mathematical right shift when the result fits two limbs.

From `shift = 128` on, the top-limb bound always holds and the shift selects at most the upper
two limbs.
-/
theorem shiftRight128_toNat (value : UInt256) (shift : Nat)
    (hlarge : 64 < shift)
    (htop : value.limb3.toNat < 2 ^ (shift - 64)) :
    (shiftRight128 value shift).toNat = value.toNat >>> shift := by
  by_cases hshift : shift < 128
  swap
  · have hshiftEq : shift = 128 + (shift - 128) := by omega
    rw [Nat.shiftRight_eq_div_pow, hshiftEq]
    exact shiftRight128_toNat_of_ge128 value (shift - 128)
  let inner := shift - 64
  have hinnerPositive : 0 < inner := by omega
  have hinner : inner < 64 := by omega
  have hlow := FloatLib.Numerics.FixedWord.shiftedPair_toNat
    value.limb1 value.limb2 inner
    hinnerPositive hinner
  have hhighPair := FloatLib.Numerics.FixedWord.shiftedPair_toNat
    value.limb2 value.limb3 inner
    hinnerPositive hinner
  have htopInner : value.limb3.toNat < 2 ^ inner := by
    simpa [inner] using htop
  have hnonzero : shift ≠ 0 := by omega
  have hnotSmall : ¬shift < 64 := by omega
  have hnotWord : shift ≠ 64 := by omega
  have hvalue :
      value.toNat =
        value.limb0.toNat +
          (value.limb1.toNat + value.limb2.toNat * 2 ^ 64 +
            value.limb3.toNat * 2 ^ 128) * 2 ^ 64 := by
    unfold UInt256.toNat
    rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num,
      show (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 by norm_num]
    ring
  unfold shiftRight128 UInt128.toNat
  simp only [hnonzero, beq_iff_eq, ite_false, hnotSmall, hnotWord,
    hshift, ite_true]
  rw [hlow, hhighPair, Nat.mod_eq_of_lt htopInner, Nat.shiftRight_eq_div_pow,
    show shift = 64 + inner by omega, pow_add, ← Nat.div_div_eq_div_mul, hvalue,
    low_add_upper_mul_pow_div _ _ 64 value.limb0.toNat_lt,
    three_limbs_div_two_pow _ _ _ _ hinner.le]

/-- A two-word shift selects the upper two limbs. -/
theorem shiftRight128_toNat_of_eq128 (value : UInt256) :
    (shiftRight128 value 128).toNat = value.toNat >>> 128 := by
  unfold shiftRight128 UInt128.toNat
  simp only [OfNat.ofNat, Nat.reduceBEq, ite_false,
    Nat.reduceLT, ite_true, Bool.false_eq_true]
  rw [Nat.shiftRight_eq_div_pow, toNat_eq_pairs]
  exact (low_add_upper_mul_pow_div _ _ 128 (pair_lt _ _)).symm

/--
A four-limb shift is floor division whenever its quotient fits in the returned two-limb carrier.

Clients need only this fit condition, never the native word-boundary cases. Normalization and
later fixed-limb kernels use it.
-/
theorem shiftRight128_toNat_of_quotient_lt
    (value : UInt256) (shift : Nat)
    (hfit : value.toNat / 2 ^ shift < 2 ^ 128) :
    (shiftRight128 value shift).toNat =
      value.toNat / 2 ^ shift := by
  by_cases hlarge : 128 ≤ shift
  · have hshiftEq : shift = 128 + (shift - 128) := by omega
    rw [hshiftEq]
    exact shiftRight128_toNat_of_ge128 value (shift - 128)
  have hvalue : value.toNat < 2 ^ (shift + 128) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)] at hfit
    simpa [pow_add, Nat.mul_comm] using hfit
  by_cases hzero : shift = 0
  · subst shift
    have hvalue128 : value.toNat < 2 ^ 128 := by
      simpa using hvalue
    have hlimb2 := limb2_eq_zero_of_toNat_lt value hvalue128
    have hlimb3 :=
      limb3_eq_zero_of_toNat_lt value (hvalue128.trans (by norm_num))
    unfold shiftRight128 UInt128.toNat UInt256.toNat
    simp [hlimb2, hlimb3]
  · by_cases hsmall : shift < 64
    · have hvalue192 : value.toNat < 2 ^ 192 := by
        exact hvalue.trans_le
          (Nat.pow_le_pow_right (by decide) (by omega))
      have hlimb3 := limb3_eq_zero_of_toNat_lt value hvalue192
      have htop : value.limb2.toNat < 2 ^ shift := by
        have hcomponent :
            value.limb2.toNat * 2 ^ 128 ≤ value.toNat := by
          unfold UInt256.toNat
          omega
        rw [show 2 ^ (shift + 128) =
            2 ^ shift * 2 ^ 128 by rw [pow_add]] at hvalue
        nlinarith [Nat.two_pow_pos 128]
      rw [← Nat.shiftRight_eq_div_pow]
      exact shiftRight128_toNat_of_lt64
        value shift hsmall hlimb3 htop
    · by_cases hword : shift = 64
      · subst shift
        have hlimb3 :=
          limb3_eq_zero_of_toNat_lt value (by simpa using hvalue)
        rw [← Nat.shiftRight_eq_div_pow]
        exact shiftRight128_toNat_of_eq64 value hlimb3
      · by_cases htop : shift < 128
        · have hlarge : 64 < shift := by omega
          have hlimb3 :
              value.limb3.toNat < 2 ^ (shift - 64) := by
            have hcomponent :
                value.limb3.toNat * 2 ^ 192 ≤ value.toNat := by
              unfold UInt256.toNat
              omega
            have hexponent :
                shift + 128 = (shift - 64) + 192 := by
              omega
            rw [hexponent, pow_add] at hvalue
            nlinarith [Nat.two_pow_pos 192]
          rw [← Nat.shiftRight_eq_div_pow]
          exact shiftRight128_toNat
            value shift hlarge hlimb3
        · omega

/--
The fixed-limb jam operation refines the representation-independent operation once its quotient
has been established.

The discarded-bit test needs no hypothesis: `hasNonzeroBelow_eq` gives it for every shift.
-/
theorem shiftRightJam128_toNat
    (value : UInt256) (shift : Nat)
    (hquotient :
      (shiftRight128 value shift).toNat =
        value.toNat / 2 ^ shift) :
    (shiftRightJam128 value shift).toNat =
      FloatLib.Numerics.shiftRightJam value.toNat shift := by
  unfold shiftRightJam128 FloatLib.Numerics.shiftRightJam
  dsimp only
  rw [hasNonzeroBelow_eq]
  by_cases hexact : value.toNat % 2 ^ shift = 0
  · simp [hexact, hquotient]
  · simp only [hexact, bne_iff_ne, ne_eq, not_false_eq_true, ite_true]
    rw [UInt128.setLowBit_toNat, hquotient]
    rw [ite_eq_right (by simpa only [beq_iff_eq] using hexact)]

/-- Four-to-two-limb normalization never discards more than 128 bits. -/
theorem normalizationShift128_le (value : UInt256) :
    value.normalizationShift128 ≤ 128 := by
  unfold normalizationShift128
  rw [UInt256.log2_toNat]
  by_cases hzero : value.toNat = 0
  · simp [hzero]
  · have hlog :
        value.toNat.log2 < 256 :=
      (Nat.log2_lt hzero).2 value.toNat_lt
    omega

/-- A four-limb value fits below the normalization window selected from its leading bit. -/
theorem toNat_lt_pow_normalizationShift128_add
    (value : UInt256) :
    value.toNat <
      2 ^ (value.normalizationShift128 + 128) := by
  by_cases hzero : value.toNat = 0
  · simp [hzero]
  · have hupper :
        value.toNat < 2 ^ (value.toNat.log2 + 1) :=
      Nat.lt_log2_self
    by_cases hsmall : value.toNat.log2 ≤ 127
    · have hshift : value.normalizationShift128 = 0 := by
        unfold normalizationShift128
        rw [UInt256.log2_toNat]
        omega
      rw [hshift]
      exact hupper.trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    · have hshift :
          value.normalizationShift128 + 128 =
            value.toNat.log2 + 1 := by
        unfold normalizationShift128
        rw [UInt256.log2_toNat]
        omega
      rw [hshift]
      exact hupper

/-- The quotient selected by four-to-two-limb normalization fits in two limbs. -/
theorem normalizationQuotient128_lt
    (value : UInt256) :
    value.toNat / 2 ^ value.normalizationShift128 <
      2 ^ 128 := by
  rw [Nat.div_lt_iff_lt_mul
    (Nat.two_pow_pos value.normalizationShift128)]
  simpa [pow_add, Nat.mul_comm] using
    value.toNat_lt_pow_normalizationShift128_add

/--
Native four-to-two-limb normalization refines representation-independent shift-with-jam.

The quotient fits in two limbs, and the low bit records the OR of the quotient's low bit and the
discarded suffix's sticky bit.
-/
@[simp, grind =] theorem normalizeJam128_toNat (value : UInt256) :
    value.normalizeJam128.toNat =
      FloatLib.Numerics.shiftRightJam
        value.toNat value.normalizationShift128 := by
  unfold normalizeJam128
  exact shiftRightJam128_toNat _ _
    (shiftRight128_toNat_of_quotient_lt
      value value.normalizationShift128
      value.normalizationQuotient128_lt)

/-- Four-to-two-limb normalization is zero exactly when its input is zero. -/
theorem normalizeJam128_toNat_eq_zero_iff (value : UInt256) :
    value.normalizeJam128.toNat = 0 ↔ value.toNat = 0 := by
  rw [normalizeJam128_toNat]
  constructor
  · intro hjammed
    by_contra hvalue
    have hshiftLe :
        value.normalizationShift128 ≤ value.toNat.log2 := by
      unfold normalizationShift128
      rw [UInt256.log2_toNat]
      omega
    have hpower :
        2 ^ value.normalizationShift128 ≤ value.toNat :=
      (Nat.pow_le_pow_right (by decide) hshiftLe).trans
        (Nat.log2_self_le hvalue)
    have hquotient :
        0 < value.toNat / 2 ^ value.normalizationShift128 :=
      Nat.div_pos hpower
        (Nat.two_pow_pos value.normalizationShift128)
    by_cases hexact :
        value.toNat % 2 ^ value.normalizationShift128 = 0
    · rw [FloatLib.Numerics.shiftRightJam_eq_of_mod_eq_zero
        value.toNat value.normalizationShift128 hexact] at hjammed
      omega
    · have hodd :=
        FloatLib.Numerics.shiftRightJam_mod_two_eq_one
          value.toNat value.normalizationShift128 hexact
      rw [hjammed] at hodd
      have : (0 : Nat) = 1 := by
        simpa only [Nat.zero_mod] using hodd
      omega
  · intro hvalue
    simp [hvalue, FloatLib.Numerics.shiftRightJam]

/-- Four-limb nearest-even rounding agrees with the generic natural-number rounder. -/
theorem roundShiftRightEven128_toNat (value : UInt256) (shift : Nat)
    (hlarge : 64 < shift) (hshift : shift < 128)
    (hincrementFit : (value.toNat >>> shift) + 1 < 2 ^ 128) :
    (roundShiftRightEven128 value shift).toNat =
      FloatLib.Numerics.roundShiftRightEven
        value.toNat shift := by
  let inner := shift - 64
  have hinnerPositive : 0 < inner := by omega
  have hinner : inner < 64 := by omega
  have hshiftEq : shift = 64 + inner := by omega
  have hquotient : (shiftRight128 value shift).toNat = value.toNat >>> shift := by
    rw [Nat.shiftRight_eq_div_pow]
    apply shiftRight128_toNat_of_quotient_lt
    rw [← Nat.shiftRight_eq_div_pow]
    omega
  have hhighRemainder :
      (value.limb1 &&& ((1 <<< UInt64.ofNat inner) - 1)).toNat =
        value.limb1.toNat % 2 ^ inner :=
    uint64_lowBits_toNat value.limb1 inner hinner
  have hhalfHigh :
      (((1 : UInt64) <<< UInt64.ofNat (inner - 1)).toNat) =
        2 ^ (inner - 1) :=
    uint64_powTwo_toNat (inner - 1) (by omega)
  let remainder :=
    value.limb0.toNat +
      (value.limb1.toNat % 2 ^ inner) * 2 ^ 64
  have hremainder :
      value.toNat -
          (value.toNat >>> shift <<< shift) =
        remainder := by
    calc
      value.toNat - (value.toNat >>> shift <<< shift) =
          value.toNat % 2 ^ shift := by
        simpa [FloatLib.Numerics.shiftRightRemainder] using
          FloatLib.Numerics.shiftRightRemainder_eq_mod value.toNat shift
      _ =
          (value.limb0.toNat + value.limb1.toNat * 2 ^ 64) %
            2 ^ shift :=
        mod_two_pow_eq_low_pair value shift hshift.le
      _ = value.limb0.toNat +
          (value.limb1.toNat % 2 ^ (shift - 64)) * 2 ^ 64 :=
        low_pair_mod_two_pow_of_gt64 value shift hlarge
      _ = remainder := by
        rw [show shift - 64 = inner by omega]
  have hincrement :
      (shiftRight128 value shift).increment.toNat =
        (value.toNat >>> shift) + 1 := by
    rw [UInt128.increment_toNat]
    · rw [hquotient]
    · rw [hquotient]
      exact hincrementFit
  have heven :
      (((shiftRight128 value shift).lo &&& 1) == 0) ↔
        value.toNat.shiftRight shift % 2 == 0 := by
    have hlowParity :
        (shiftRight128 value shift).toNat % 2 =
          (shiftRight128 value shift).lo.toNat % 2 := by
      unfold UInt128.toNat
      omega
    simp only [beq_iff_eq]
    constructor
    · intro hevenNative
      have hevenNat := congrArg UInt64.toNat hevenNative
      simp only [UInt64.toNat_and, UInt64.reduceToNat,
        Nat.and_one_is_mod] at hevenNat
      rw [← hlowParity, hquotient] at hevenNat
      exact hevenNat
    · intro hevenNat
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_and]
      simp only [UInt64.reduceToNat, Nat.and_one_is_mod]
      rw [← hlowParity, hquotient]
      exact hevenNat
  have hgeneric :
      FloatLib.Numerics.roundShiftRightEven
        value.toNat shift =
        if remainder < 2 ^ (shift - 1) then
          value.toNat.shiftRight shift
        else if remainder > 2 ^ (shift - 1) then
          value.toNat.shiftRight shift + 1
        else if value.toNat.shiftRight shift % 2 == 0 then
          value.toNat.shiftRight shift
        else
          value.toNat.shiftRight shift + 1 := by
    rw [FloatLib.Numerics.roundShiftRightEven_def]
    simp only [beq_iff_eq]
    rw [ite_eq_right (Nat.ne_of_gt (lt_trans (by norm_num : 0 < 64) hlarge))]
    change
      value.toNat -
          (value.toNat.shiftRight shift).shiftLeft shift = remainder at hremainder
    rw [hremainder]
  rw [hgeneric]
  unfold roundShiftRightEven128
  dsimp only
  change
    (if value.limb1 &&& (((1 : UInt64) <<< UInt64.ofNat inner) - 1) <
          ((1 : UInt64) <<< UInt64.ofNat (inner - 1)) then
        shiftRight128 value shift
      else if
          value.limb1 &&& (((1 : UInt64) <<< UInt64.ofNat inner) - 1) >
              ((1 : UInt64) <<< UInt64.ofNat (inner - 1)) ||
            value.limb0 != 0 then
        (shiftRight128 value shift).increment
      else if ((shiftRight128 value shift).lo &&& 1) == 0 then
        shiftRight128 value shift
      else
        (shiftRight128 value shift).increment).toNat =
      _
  simp only [UInt64.lt_iff_toNat_lt, hhighRemainder, hhalfHigh]
  have hpowHalf :
      2 ^ (shift - 1) = 2 ^ (inner - 1) * 2 ^ 64 := by
    rw [hshiftEq]
    have hexponent : 64 + inner - 1 = (inner - 1) + 64 := by omega
    rw [hexponent, pow_add]
  rw [hpowHalf]
  have hlowBound := value.limb0.toNat_lt
  have hpowPositive : 0 < 2 ^ 64 := by positivity
  by_cases hless :
      value.limb1.toNat % 2 ^ inner < 2 ^ (inner - 1)
  · have hremainderLess :
        remainder < 2 ^ (inner - 1) * 2 ^ 64 := by
      unfold remainder
      nlinarith
    rw [ite_eq_left hless, ite_eq_left hremainderLess]
    simpa using hquotient
  by_cases hgreater :
      value.limb1.toNat % 2 ^ inner > 2 ^ (inner - 1)
  · have hremainderGreater :
        remainder > 2 ^ (inner - 1) * 2 ^ 64 := by
      unfold remainder
      nlinarith
    have hremainderNotLess :
        ¬remainder < 2 ^ (inner - 1) * 2 ^ 64 :=
      Nat.not_lt_of_ge (Nat.le_of_lt hremainderGreater)
    rw [ite_eq_right hless]
    simp only [hgreater, decide_true, Bool.true_or, ite_true]
    rw [ite_eq_right hremainderNotLess, ite_eq_left hremainderGreater]
    simpa using hincrement
  have hequal :
      value.limb1.toNat % 2 ^ inner = 2 ^ (inner - 1) := by
    omega
  by_cases hlowZero : value.limb0 = 0
  · have hlowNat : value.limb0.toNat = 0 := by simp [hlowZero]
    have hremainderEqual :
        remainder = 2 ^ (inner - 1) * 2 ^ 64 := by
      simp [remainder, hlowNat, hequal]
    by_cases hevenNative : ((shiftRight128 value shift).lo &&& 1) == 0
    · have hevenNat := heven.mp hevenNative
      simp [hequal, hlowZero, hremainderEqual,
        hevenNative, hquotient]
      change value.toNat.shiftRight shift % 2 = 0
      simpa only [beq_iff_eq] using hevenNat
    · have hevenNat : ¬value.toNat.shiftRight shift % 2 == 0 := by
        exact fun h => hevenNative (heven.mpr h)
      have hoddNat : value.toNat.shiftRight shift % 2 = 1 := by
        have hlt := Nat.mod_lt (value.toNat.shiftRight shift) (by decide : 0 < 2)
        have hne : value.toNat.shiftRight shift % 2 ≠ 0 := by
          intro hzero
          apply hevenNat
          simpa only [beq_iff_eq] using hzero
        omega
      simp [hequal, hlowZero, hremainderEqual,
        hevenNative, hincrement]
      change value.toNat.shiftRight shift % 2 = 1
      exact hoddNat
  · have hlowPositive : 0 < value.limb0.toNat :=
      Nat.pos_of_ne_zero ((uint64_toNat_eq_zero _).not.mpr hlowZero)
    have hremainderGreater :
        remainder > 2 ^ (inner - 1) * 2 ^ 64 := by
      unfold remainder
      rw [hequal]
      omega
    have hremainderNotLess :
        ¬remainder < 2 ^ (inner - 1) * 2 ^ 64 :=
      Nat.not_lt_of_ge (Nat.le_of_lt hremainderGreater)
    rw [ite_eq_right hless]
    simp only [hgreater, decide_false, Bool.false_or, bne_iff_ne]
    rw [ite_eq_left hlowZero]
    rw [ite_eq_right hremainderNotLess, ite_eq_left hremainderGreater]
    simpa using hincrement

end UInt256

end FloatLib.Numerics.FixedWord
