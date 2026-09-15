/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Difference.Proof
public import FloatLib.Kernels.FixedWord.DyadicCompare.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Order
import Batteries.Data.UInt
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Correctness of native-word dyadic comparison

The runtime comparator avoids materializing shifted arbitrary-precision integers when two
nonnegative dyadics fit the fixed-word preconditions. This module proves its word comparisons,
exponent alignment, and swapped-operand cases equal to the reference `Dyadic` ordering.

The comparison is format-independent, so binary and posit kernels can share these
shift-and-compare theorems.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.DyadicCompare

/--
Reversing the operands of the exact nonnegative dyadic comparator swaps its ordering.

Wide fixed-limb kernels naturally compare their target against a decoded one-word candidate,
whereas the generic posit rounder phrases the same question as candidate against target. Keeping
the direction bridge beside the shared comparator prevents each format backend from reproving
the same order-theoretic fact.
-/
theorem compareNonnegativeFields_swap
    (leftSignificand : Nat) (leftExponent : Int)
    (rightSignificand : Nat) (rightExponent : Int) :
    (Dyadic.compareNonnegativeFields
        leftSignificand leftExponent
        rightSignificand rightExponent).swap =
      Dyadic.compareNonnegativeFields
        rightSignificand rightExponent
        leftSignificand leftExponent := by
  rw [Dyadic.compareNonnegativeFields_eq_compareFields,
    Dyadic.compareNonnegativeFields_eq_compareFields,
    Dyadic.compareFields_eq, Dyadic.compareFields_eq]
  let left : Dyadic :=
    {
      negative := false
      significand := leftSignificand
      exponent := leftExponent
    }
  let right : Dyadic :=
    {
      negative := false
      significand := rightSignificand
      exponent := rightExponent
    }
  change (left.compare right).swap = right.compare left
  cases hcomparison : left.compare right with
  | lt =>
      have hless : left.toRat < right.toRat :=
        (Dyadic.compare_eq_lt_iff left right).mp hcomparison
      have hreverse : right.compare left = .gt :=
        (Dyadic.compare_eq_gt_iff right left).mpr hless
      simp [hreverse, Ordering.swap]
  | eq =>
      have hequal : left.toRat = right.toRat :=
        (Dyadic.compare_eq_eq_iff left right).mp hcomparison
      have hreverse : right.compare left = .eq :=
        (Dyadic.compare_eq_eq_iff right left).mpr hequal.symm
      simp [hreverse, Ordering.swap]
  | gt =>
      have hgreater : right.toRat < left.toRat :=
        (Dyadic.compare_eq_gt_iff left right).mp hcomparison
      have hreverse : right.compare left = .lt :=
        (Dyadic.compare_eq_lt_iff right left).mpr hgreater
      simp [hreverse, Ordering.swap]

/--
A recognized word shift preserves the corresponding exact natural-number alignment.

Arithmetic backends reuse this theorem after sharing `shiftFits` with the comparison kernel.
-/
theorem shiftLeft_toNat
    (significand : UInt64) (shift : Nat)
    (hshift : shift < 64) (hfit : shiftFits significand shift) :
    (significand <<< UInt64.ofNat shift).toNat =
      significand.toNat <<< shift := by
  apply FloatLib.Numerics.FixedWord.shiftLeft_toNat significand shift hshift
  rcases hfit with hzero | hleading
  · subst significand
    simp
  · have hleadingNat :
        significand.log2.toNat = significand.toNat.log2 :=
      FloatLib.Numerics.FixedWord.log2_toNat significand
    have hbound :
        significand.toNat <<< shift <
          2 ^ (significand.toNat.log2 + 1 + shift) :=
      Nat.shiftLeft_lt (x := significand.toNat)
        (n := significand.toNat.log2 + 1) (m := shift)
        Nat.lt_log2_self
    have hexponent :
        significand.toNat.log2 + 1 + shift ≤ 64 := by
      rw [← hleadingNat]
      omega
    exact lt_of_lt_of_le hbound
      (Nat.pow_le_pow_right (by decide) hexponent)

/--
A recognized two-limb shift preserves the corresponding exact natural-number alignment.
-/
theorem shiftLeft128_toNat
    (significand : UInt128) (shift : Nat)
    (hshift : shift < 128) (hfit : shiftFits128 significand shift) :
    (UInt128.shiftLeft significand shift).toNat =
      significand.toNat <<< shift := by
  apply UInt128.shiftLeft_toNat significand shift hshift
  rcases hfit with hzero | hleading
  · subst significand
    norm_num [UInt128.toNat]
  · have hleadingNat :
        UInt128.log2 significand = significand.toNat.log2 :=
      UInt128.log2_toNat significand
    have hbound :
        significand.toNat <<< shift <
          2 ^ (significand.toNat.log2 + 1 + shift) :=
      Nat.shiftLeft_lt (x := significand.toNat)
        (n := significand.toNat.log2 + 1) (m := shift)
        Nat.lt_log2_self
    have hexponent :
        significand.toNat.log2 + 1 + shift ≤ 128 := by
      rw [← hleadingNat]
      omega
    exact lt_of_lt_of_le hbound
      (Nat.pow_le_pow_right (by decide) hexponent)

/--
Native-word comparison returns exactly the same ordering as arbitrary-precision dyadic field
comparison.
-/
theorem compareNonnegative_eq
    (leftSignificand : UInt64) (leftExponent : Int)
    (rightSignificand : UInt64) (rightExponent : Int) :
    compareNonnegative leftSignificand leftExponent
        rightSignificand rightExponent =
      Dyadic.compareNonnegativeFields
        leftSignificand.toNat leftExponent
        rightSignificand.toNat rightExponent := by
  have hleftZero :
      (leftSignificand.toNat == 0) = (leftSignificand == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro equality
      apply UInt64.toNat_inj.mp
      simpa using equality
    · intro equality
      subst leftSignificand
      rfl
  have hrightZero :
      (rightSignificand.toNat == 0) = (rightSignificand == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro equality
      apply UInt64.toNat_inj.mp
      simpa using equality
    · intro equality
      subst rightSignificand
      rfl
  unfold compareNonnegative Dyadic.compareNonnegativeFields
  rw [hleftZero, hrightZero]
  split
  · rfl
  · split
    · change
        (if hshift : Int.toNat (rightExponent - leftExponent) < 64 then
          if hfit :
              shiftFits rightSignificand
                (Int.toNat (rightExponent - leftExponent)) then
            Ord.compare leftSignificand
              (rightSignificand <<<
                UInt64.ofNat (Int.toNat (rightExponent - leftExponent)))
          else
            Ord.compare leftSignificand.toNat
              (rightSignificand.toNat <<<
                Int.toNat (rightExponent - leftExponent))
        else
          Ord.compare leftSignificand.toNat
            (rightSignificand.toNat <<<
              Int.toNat (rightExponent - leftExponent))) =
          Ord.compare leftSignificand.toNat
            (rightSignificand.toNat <<<
              Int.toNat (rightExponent - leftExponent))
      split
      · rename_i hshift
        split
        · rename_i hfit
          rw [UInt64.compare_eq_toNat_compare_toNat,
            shiftLeft_toNat rightSignificand
              (Int.toNat (rightExponent - leftExponent))
              hshift hfit]
        · rfl
      · rfl
    · change
        (if hshift : Int.toNat (leftExponent - rightExponent) < 64 then
          if hfit :
              shiftFits leftSignificand
                (Int.toNat (leftExponent - rightExponent)) then
            Ord.compare
              (leftSignificand <<<
                UInt64.ofNat (Int.toNat (leftExponent - rightExponent)))
              rightSignificand
          else
            Ord.compare
              (leftSignificand.toNat <<<
                Int.toNat (leftExponent - rightExponent))
              rightSignificand.toNat
        else
          Ord.compare
            (leftSignificand.toNat <<<
              Int.toNat (leftExponent - rightExponent))
            rightSignificand.toNat) =
          Ord.compare
            (leftSignificand.toNat <<<
              Int.toNat (leftExponent - rightExponent))
            rightSignificand.toNat
      split
      · rename_i hshift
        split
        · rename_i hfit
          rw [UInt64.compare_eq_toNat_compare_toNat,
            shiftLeft_toNat leftSignificand
              (Int.toNat (leftExponent - rightExponent))
              hshift hfit]
        · rfl
      · rfl

/--
A word shift accepted by the 128-bit leading-bit test remains below the carrier limit.

The runtime test uses only `UInt64.log2` and scalar addition. This theorem supplies the exact
natural-number capacity fact required by the two-limb shift refinement.
-/
private theorem word_shift_lt_twoPow128
    (value : UInt64) (shift : Nat)
    (hfit : value.log2.toNat + shift < 128) :
    value.toNat <<< shift < 2 ^ 128 := by
  have hlog :
      value.log2.toNat = value.toNat.log2 :=
    FloatLib.Numerics.FixedWord.log2_toNat value
  have hbound :
      value.toNat <<< shift <
        2 ^ (value.toNat.log2 + 1 + shift) :=
    Nat.shiftLeft_lt
      (x := value.toNat)
      (n := value.toNat.log2 + 1)
      (m := shift)
      Nat.lt_log2_self
  have hexponent :
      value.toNat.log2 + 1 + shift ≤ 128 := by
    rw [← hlog]
    omega
  exact lt_of_lt_of_le hbound
    (Nat.pow_le_pow_right (by decide) hexponent)

/--
Failing the 128-bit leading-bit test means a nonzero shifted word reaches at least `2^128`.
-/
private theorem twoPow128_le_word_shift_of_not_fit
    (value : UInt64) (shift : Nat)
    (hvalue : value ≠ 0)
    (hfit : ¬value.log2.toNat + shift < 128) :
    2 ^ 128 ≤ value.toNat <<< shift := by
  have hvalueNat : value.toNat ≠ 0 := by
    intro hzero
    apply hvalue
    apply UInt64.toNat_inj.mp
    simpa using hzero
  have hlog :
      value.log2.toNat = value.toNat.log2 :=
    FloatLib.Numerics.FixedWord.log2_toNat value
  have hexponent :
      128 ≤ value.toNat.log2 + shift := by
    rw [← hlog]
    omega
  calc
    2 ^ 128 ≤ 2 ^ (value.toNat.log2 + shift) :=
      Nat.pow_le_pow_right (by decide) hexponent
    _ = 2 ^ value.toNat.log2 * 2 ^ shift := by
      rw [pow_add]
    _ ≤ value.toNat * 2 ^ shift :=
      Nat.mul_le_mul_right _ (Nat.log2_self_le hvalueNat)
    _ = value.toNat <<< shift := by
      rw [Nat.shiftLeft_eq]

/-- Shifting a nonzero word by at least 128 bits exceeds the two-limb carrier. -/
private theorem twoPow128_le_word_shift_of_large_shift
    (value : UInt64) (shift : Nat)
    (hvalue : value ≠ 0)
    (hshift : 128 ≤ shift) :
    2 ^ 128 ≤ value.toNat <<< shift := by
  have hvalueNat : value.toNat ≠ 0 := by
    intro hzero
    apply hvalue
    apply UInt64.toNat_inj.mp
    simpa using hzero
  have hone : 1 ≤ value.toNat :=
    Nat.one_le_iff_ne_zero.mpr hvalueNat
  calc
    2 ^ 128 ≤ 2 ^ shift :=
      Nat.pow_le_pow_right (by decide) hshift
    _ = 1 * 2 ^ shift := by simp
    _ ≤ value.toNat * 2 ^ shift :=
      Nat.mul_le_mul_right _ hone
    _ = value.toNat <<< shift := by
      rw [Nat.shiftLeft_eq]

/--
Two-limb-versus-word dyadic comparison is exactly the arbitrary-precision field comparison.

The proof covers all runtime exits: a zero high limb delegates to the established word
comparator; a fitting right alignment is represented exactly in two limbs; and each capacity
rejection has a strict ordering proof. Consequently the executable wide path introduces no
approximation and no additional trust boundary.
-/
theorem compareNonnegative128ToWord_eq
    (leftSignificand : UInt128) (leftExponent : Int)
    (rightSignificand : UInt64) (rightExponent : Int) :
    compareNonnegative128ToWord
        leftSignificand leftExponent rightSignificand rightExponent =
      Dyadic.compareNonnegativeFields
        leftSignificand.toNat leftExponent
        rightSignificand.toNat rightExponent := by
  unfold compareNonnegative128ToWord
  by_cases hhigh : leftSignificand.hi = 0
  · simp only [beq_iff_eq, hhigh, ite_true]
    rw [compareNonnegative_eq]
    simp [UInt128.toNat, hhigh]
  · simp only [beq_iff_eq, hhigh, ite_false]
    have hhighNat : leftSignificand.hi.toNat ≠ 0 := by
      intro hzero
      apply hhigh
      apply UInt64.toNat_inj.mp
      simpa using hzero
    have hleftLarge : 2 ^ 64 ≤ leftSignificand.toNat := by
      unfold UInt128.toNat
      have hone : 1 ≤ leftSignificand.hi.toNat :=
        Nat.one_le_iff_ne_zero.mpr hhighNat
      have hscaled :
          2 ^ 64 ≤ leftSignificand.hi.toNat * 2 ^ 64 := by
        calc
          2 ^ 64 = 1 * 2 ^ 64 := by simp
          _ ≤ leftSignificand.hi.toNat * 2 ^ 64 :=
            Nat.mul_le_mul_right (2 ^ 64) hone
      omega
    have hleftPositive : 0 < leftSignificand.toNat := by
      exact lt_of_lt_of_le (by positivity) hleftLarge
    have hleftNonzero : leftSignificand.toNat ≠ 0 :=
      Nat.ne_of_gt hleftPositive
    unfold Dyadic.compareNonnegativeFields
    have hnotBoth :
        ¬((leftSignificand.toNat == 0 &&
            rightSignificand.toNat == 0) = true) := by
      simp [hleftNonzero]
    rw [ite_eq_right hnotBoth]
    by_cases hright : rightSignificand = 0
    · simp only [hright, ite_true, UInt64.toNat_zero]
      split
      · simpa [Nat.shiftLeft_eq] using
          (Nat.compare_eq_gt.mpr hleftPositive).symm
      · symm
        apply Nat.compare_eq_gt.mpr
        exact Nat.pos_of_ne_zero
          (Nat.shiftLeft_eq_zero_iff.not.mpr hleftNonzero)
    · simp only [hright, ite_false]
      by_cases hexponents : leftExponent ≤ rightExponent
      · simp only [hexponents, ite_true]
        let shift := Int.toNat (rightExponent - leftExponent)
        change
          (if _hshift : shift < 128 then
            if _hfit :
                rightSignificand.log2.toNat + shift < 128 then
              UInt128.compare leftSignificand
                (UInt128.shiftLeft
                  { hi := 0, lo := rightSignificand } shift)
            else
              .lt
          else
            .lt) =
          Ord.compare leftSignificand.toNat
            (rightSignificand.toNat <<< shift)
        by_cases hshift : shift < 128
        · simp only [hshift, dite_true]
          by_cases hfit :
              rightSignificand.log2.toNat + shift < 128
          · simp only [hfit, dite_true]
            rw [UInt128.compare_eq_toNat_compare_toNat]
            rw [UInt128.shiftLeft_toNat]
            · simp [UInt128.toNat]
            · exact hshift
            · simpa [UInt128.toNat] using
                word_shift_lt_twoPow128
                  rightSignificand shift hfit
          · simp only [hfit, dite_false]
            symm
            apply Nat.compare_eq_lt.mpr
            exact lt_of_lt_of_le leftSignificand.toNat_lt
              (twoPow128_le_word_shift_of_not_fit
                rightSignificand shift hright hfit)
        · simp only [hshift, dite_false]
          symm
          apply Nat.compare_eq_lt.mpr
          exact lt_of_lt_of_le leftSignificand.toNat_lt
            (twoPow128_le_word_shift_of_large_shift
              rightSignificand shift hright (Nat.le_of_not_gt hshift))
      · simp only [hexponents, ite_false]
        symm
        apply Nat.compare_eq_gt.mpr
        have hpow : 1 ≤ 2 ^ Int.toNat (leftExponent - rightExponent) := by
          have hpositive :
              0 < 2 ^ Int.toNat (leftExponent - rightExponent) :=
            pow_pos (by decide) _
          omega
        calc
          rightSignificand.toNat < 2 ^ 64 :=
            rightSignificand.toNat_lt
          _ ≤ leftSignificand.toNat := hleftLarge
          _ = leftSignificand.toNat * 1 := by simp
          _ ≤ leftSignificand.toNat *
                2 ^ Int.toNat (leftExponent - rightExponent) :=
            Nat.mul_le_mul_left _ hpow
          _ = leftSignificand.toNat <<<
                Int.toNat (leftExponent - rightExponent) := by
            rw [Nat.shiftLeft_eq]

/--
The leading-exponent power-of-two test is exactly the reference arbitrary-precision dyadic
comparison.
-/
theorem isLessPowerOfTwo_eq
    (significand : UInt64) (exponent power : Int) :
    isLessPowerOfTwo significand exponent power =
      Dyadic.isLessNonnegativeFields
        significand.toNat exponent 1 power := by
  have hlog :
      significand.log2.toNat = significand.toNat.log2 :=
    FloatLib.Numerics.FixedWord.log2_toNat significand
  unfold isLessPowerOfTwo
    Dyadic.isLessNonnegativeFields Dyadic.compareNonnegativeFields
  rw [hlog]
  by_cases hzero : significand = 0
  · subst significand
    have honeZero : ((1 : Nat) == 0) = false := by decide
    simp only [beq_self_eq_true, ite_true, UInt64.toNat_zero,
      Bool.true_and, honeZero, Bool.false_eq_true, ite_false]
    split <;> simp [Nat.shiftLeft_eq, Nat.compare_eq_lt]
  · have hzeroNat : significand.toNat ≠ 0 := by
      intro hzeroNat
      apply hzero
      apply UInt64.toNat_inj.mp
      simpa using hzeroNat
    simp only [beq_iff_eq, hzero, ite_false]
    have hboth :
        ¬((significand.toNat == 0 && (1 : Nat) == 0) = true) := by
      simp
    rw [ite_eq_right hboth]
    by_cases hexponents : exponent ≤ power
    · simp only [hexponents, ite_true]
      let shift := Int.toNat (power - exponent)
      have hshift :
          Int.ofNat shift = power - exponent := by
        unfold shift
        exact Int.toNat_of_nonneg (sub_nonneg.mpr hexponents)
      have hcondition :
          exponent + Int.ofNat significand.toNat.log2 < power ↔
            significand.toNat.log2 < shift := by
        change
          exponent + (significand.toNat.log2 : Int) < power ↔
            significand.toNat.log2 < shift
        omega
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, Nat.compare_eq_lt,
        hcondition, Nat.log2_lt hzeroNat]
      simp [shift, Nat.shiftLeft_eq]
    · simp only [hexponents, ite_false]
      have hlogNonnegative :
          0 ≤ Int.ofNat significand.toNat.log2 :=
        Int.natCast_nonneg _
      have hnot :
          ¬exponent + Int.ofNat significand.toNat.log2 < power := by
        omega
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, Nat.compare_eq_lt]
      rw [Nat.lt_one_iff]
      constructor
      · exact fun hless => (hnot hless).elim
      · intro hshiftZero
        exact (hzeroNat
          (Nat.shiftLeft_eq_zero_iff.mp hshiftZero)).elim

/-- Native strict comparison is the reference exact nonnegative comparison. -/
theorem isLessNonnegative_eq
    (leftSignificand : UInt64) (leftExponent : Int)
    (rightSignificand : UInt64) (rightExponent : Int) :
    isLessNonnegative leftSignificand leftExponent
        rightSignificand rightExponent =
      Dyadic.isLessNonnegativeFields
        leftSignificand.toNat leftExponent
        rightSignificand.toNat rightExponent := by
  unfold isLessNonnegative Dyadic.isLessNonnegativeFields
  rw [compareNonnegative_eq]

/-- Native non-strict comparison is the reference exact nonnegative comparison. -/
theorem isLessOrEqualNonnegative_eq
    (leftSignificand : UInt64) (leftExponent : Int)
    (rightSignificand : UInt64) (rightExponent : Int) :
    isLessOrEqualNonnegative leftSignificand leftExponent
        rightSignificand rightExponent =
      Dyadic.isLessOrEqualNonnegativeFields
        leftSignificand.toNat leftExponent
        rightSignificand.toNat rightExponent := by
  unfold isLessOrEqualNonnegative
    Dyadic.isLessOrEqualNonnegativeFields
  rw [isLessNonnegative_eq]

end FloatLib.Numerics.FixedWord.DyadicCompare
