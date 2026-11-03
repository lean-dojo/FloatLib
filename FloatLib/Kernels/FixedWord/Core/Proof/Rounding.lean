/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Core.Proof.Word
public import FloatLib.Numerics.ShiftRightJam
import FloatLib.Numerics.ShiftRightJam.Proof
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Data.Rat.Cast.Order

/-!
# Verified native-word rounding

The one-word nearest-even shift and quotient kernels agree with the shared arbitrary-precision
definitions. The compiler substitutions therefore change only the representation used for
bounded inputs, not the numerical result. `jamCombine_toNat` gives the sticky combination of an
aligned sum or difference its `shiftRightJam` value.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/-- Natural-number view of the shared nonnegative finite-scale encoding. -/
@[simp, grind =] theorem finiteScale_toNat (exponent : UInt64) :
    (finiteScale exponent).toNat =
      if exponent = 0 then 0 else exponent.toNat - 1 := by
  by_cases hexponent : exponent = 0
  · simp [finiteScale, hexponent]
  · simp only [finiteScale, beq_iff_eq, hexponent, ite_false]
    rw [UInt64.toNat_sub_of_le]
    · simp
    · apply UInt64.le_iff_toNat_le.mpr
      have hexponentNat : exponent.toNat ≠ 0 := by
        intro h
        apply hexponent
        apply UInt64.toNat_inj.mp
        simpa using h
      simp
      omega

private theorem uint64_rounding_increment_toNat (value : UInt64) (shift : Nat)
    (hpositive : 0 < shift) (hshift : shift < 64) :
    ((value >>> UInt64.ofNat shift) + 1).toNat =
      (value.toNat >>> shift) + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
  have hquotientLe :
      value.toNat >>> (k + 1) ≤ value.toNat >>> 1 := by
    rw [show k + 1 = 1 + k by omega, Nat.shiftRight_add]
    exact Nat.shiftRight_le _ _
  have hhalf : value.toNat >>> 1 < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by decide)]
    simpa [pow_succ] using value.toNat_lt
  have hsum : value.toNat >>> (k + 1) + 1 < 2 ^ 64 := by
    omega
  rw [UInt64.toNat_add, shiftRight_toNat value (k + 1) hshift]
  simp only [UInt64.reduceToNat]
  rw [Nat.mod_eq_of_lt hsum]

/-- Native word rounding agrees with the generic natural-number rounder. -/
@[simp, grind =] theorem roundShiftRightEven_toNat (value : UInt64) (shift : Nat) :
    (roundShiftRightEven value shift).toNat =
      Numerics.roundShiftRightEven value.toNat shift := by
  by_cases hzero : shift = 0
  · subst shift
    simp [roundShiftRightEven, Numerics.roundShiftRightEven]
  by_cases hsmall : shift < 64
  · have hpositive : 0 < shift := Nat.pos_of_ne_zero hzero
    have hquotient :=
      shiftRight_toNat value shift hsmall
    have hremainder :=
      FloatLib.Numerics.FixedWord.uint64_lowBits_toNat
        value shift hsmall
    have hhalf :=
      FloatLib.Numerics.FixedWord.uint64_powTwo_toNat
        (shift - 1) (by omega)
    have hincrement :=
      uint64_rounding_increment_toNat value shift hpositive hsmall
    have hincrementBound : value.toNat >>> shift + 1 < 2 ^ 64 := by
      rw [← hincrement]
      exact UInt64.toNat_lt _
    have heven := lowBitIsZero_eq_even (value >>> UInt64.ofNat shift)
    rw [hquotient] at heven
    have hremainderNat :
        value.toNat - (value.toNat >>> shift <<< shift) =
          value.toNat % 2 ^ shift := by
      simpa [Numerics.shiftRightRemainder] using
        Numerics.shiftRightRemainder_eq_mod value.toNat shift
    unfold roundShiftRightEven
    rw [Numerics.roundShiftRightEven_def]
    simp only [beq_iff_eq, hzero, hsmall, ite_false, ite_true]
    simp only [UInt64.lt_iff_toNat_lt, hremainder, hhalf]
    split_ifs <;> simp_all <;> omega
  · have hlarge : 64 ≤ shift := Nat.le_of_not_gt hsmall
    by_cases heq : shift = 64
    · subst shift
      have hhalf : (0x8000000000000000 : UInt64).toNat = 2 ^ 63 := by
        decide
      rw [Numerics.roundShiftRightEven_of_lt_two_pow _ _ (by decide) value.toNat_lt]
      unfold roundShiftRightEven
      simp [UInt64.lt_iff_toNat_lt, hhalf]
      split_ifs <;> rfl
    · have hgt : 64 < shift := lt_of_le_of_ne hlarge (Ne.symm heq)
      have hvaluePow : value.toNat < 2 ^ shift := by
        exact lt_of_lt_of_le value.toNat_lt
          (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hgt))
      have hhalfBound : value.toNat < 2 ^ (shift - 1) := by
        exact lt_of_lt_of_le value.toNat_lt
          (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Numerics.roundShiftRightEven_of_lt_two_pow _ _ hzero hvaluePow,
        ite_eq_right (not_lt.mpr hhalfBound.le)]
      unfold roundShiftRightEven
      simp [beq_iff_eq, hzero, hsmall, heq]

/-- Capacity-selected nearest-even shifting agrees with arbitrary-precision rounding. -/
theorem roundShiftRightEvenNat_eq_roundShiftRightEven (value shift : Nat) :
    roundShiftRightEvenNat value shift =
      Numerics.roundShiftRightEven value shift := by
  unfold roundShiftRightEvenNat
  split
  next hvalue =>
    have hvalue64 : (UInt64.ofNat value).toNat = value :=
      UInt64.toNat_ofNat_of_lt' hvalue
    rw [roundShiftRightEven_toNat, hvalue64]
  next hvalue => rfl

/--
The compiler uses native nearest-even shifting for one-word inputs and guard-and-sticky rounding
for wider inputs.
-/
-- grind: no rule; this compiler substitution expands a capacity-dispatch implementation.
@[csimp] theorem roundShiftRightEven_eq_roundShiftRightEvenNat :
    Numerics.roundShiftRightEven = roundShiftRightEvenNat := by
  funext value shift
  exact (roundShiftRightEvenNat_eq_roundShiftRightEven value shift).symm

/--
Native quotient rounding agrees with natural-number quotient rounding whenever the denominator is
nonzero.

No bound on `den` is needed, because the kernel compares the remainder with `den - remainder`
instead of doubling it, so its intermediates never wrap. The incremented quotient always fits: a
round-up needs a nonzero remainder, so `den` is at least two and the quotient is below `2 ^ 63`.
-/
theorem roundQuotientEven_toNat (num den : UInt64)
    (hden : den ≠ 0) :
    (roundQuotientEven num den).toNat =
      Numerics.roundQuotientEven num.toNat den.toNat := by
  have hdenNat : den.toNat ≠ 0 := by
    intro h
    apply hden
    apply UInt64.toNat_inj.mp
    simpa using h
  by_cases hone : den.toNat = 1
  · have hdenOne : den = 1 := UInt64.toNat_inj.mp (by simpa using hone)
    subst hdenOne
    simp [roundQuotientEven, Numerics.roundQuotientEven, Nat.mod_one]
  have hquotientFit : num.toNat / den.toNat + 1 < 2 ^ 64 := by
    have hhalf : num.toNat / den.toNat ≤ num.toNat / 2 :=
      Nat.div_le_div_left (by omega) (by decide)
    have := num.toNat_lt
    omega
  have hremainderLt :
      num.toNat % den.toNat < den.toNat :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero hdenNat)
  have hremainder :
      (num % den).toNat = num.toNat % den.toNat :=
    UInt64.toNat_mod num den
  have hremainderLe : num % den ≤ den := by
    rw [UInt64.le_iff_toNat_le, hremainder]
    exact hremainderLt.le
  have hcomplement :
      (den - num % den).toNat =
        den.toNat - num.toNat % den.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hremainderLe, hremainder]
  have hquotient :
      (num / den).toNat = num.toNat / den.toNat :=
    UInt64.toNat_div num den
  have hincrement :
      (num / den + 1).toNat =
        num.toNat / den.toNat + 1 := by
    rw [UInt64.toNat_add, hquotient]
    exact Nat.mod_eq_of_lt hquotientFit
  unfold roundQuotientEven Numerics.roundQuotientEven
  simp only [beq_iff_eq, hden, ite_false]
  have heven :
      (num / den % 2 == 0) ↔
        (num.toNat / den.toNat) % 2 == 0 := by
    simp [← UInt64.toNat_inj, hquotient]
  simp only [UInt64.lt_iff_toNat_lt, hremainder, hcomplement]
  split_ifs <;> simp_all <;> omega

/--
The native and arbitrary-precision branches compute the same nearest-even natural-number
quotient.
-/
theorem roundQuotientEvenNat_eq_roundQuotientEven (num den : Nat) :
    roundQuotientEvenNat num den = Numerics.roundQuotientEven num den := by
  unfold roundQuotientEvenNat
  split
  next hfit =>
    obtain ⟨hnum, hdenPositive, hden⟩ := hfit
    have hnum64 : (UInt64.ofNat num).toNat = num :=
      UInt64.toNat_ofNat_of_lt' (hnum.trans (by decide))
    have hden64 : (UInt64.ofNat den).toNat = den :=
      UInt64.toNat_ofNat_of_lt' hden
    have hdenNonzero : UInt64.ofNat den ≠ 0 := by
      intro h
      have := congrArg UInt64.toNat h
      simp [hden64, Nat.ne_of_gt hdenPositive] at this
    rw [roundQuotientEven_toNat _ _ hdenNonzero, hnum64, hden64]
  next hfit =>
    rw [Numerics.roundQuotientEven]

/--
The compiler uses native quotient rounding for bounded inputs and the arbitrary-precision
definition otherwise.
-/
-- grind: no rule; this compiler substitution expands a capacity-dispatch implementation.
@[csimp] theorem roundQuotientEven_eq_roundQuotientEvenNat :
    Numerics.roundQuotientEven = roundQuotientEvenNat := by
  funext num den
  exact (roundQuotientEvenNat_eq_roundQuotientEven num den).symm


/--
The word sticky combination is the natural-number jam of the exact aligned value. A sum needs
`A + q` to fit in the word; a difference needs only `B ≤ A * 2^d`, so exact cancellation to zero
is included.
-/
theorem jamCombine_toNat (sameSign exact : Bool) (A q : UInt64) (B d : Nat)
    (hq : q.toNat = B / 2 ^ d) (hexact : exact = decide (B % 2 ^ d = 0))
    (hfit : sameSign = true → A.toNat + q.toNat < 2 ^ 64)
    (hsub : sameSign = false → B ≤ A.toNat * 2 ^ d) :
    (jamCombine sameSign exact A q).toNat =
      Numerics.shiftRightJam
        (if sameSign then A.toNat * 2 ^ d + B else A.toNat * 2 ^ d - B) d := by
  unfold jamCombine
  subst hexact
  cases sameSign
  · have hB := hsub rfl
    simp only [Bool.false_eq_true, ite_false]
    rw [Numerics.shiftRightJam_mul_two_pow_sub _ _ _ hB, ← hq]
    have hle : q ≤ A := UInt64.le_iff_toNat_le.mpr (by
      rw [hq]
      exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hB))
    have hd : (A - q).toNat = A.toNat - q.toNat := UInt64.toNat_sub_of_le _ _ hle
    by_cases hz : B % 2 ^ d = 0
    · simp only [hz, decide_true, ite_true, hd]
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      have hlt : q.toNat < A.toNat := by
        rw [hq, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos d)]
        exact lt_of_le_of_ne hB fun h => hz (by rw [h, Nat.mul_mod_left])
      have hone : (1 : UInt64) ≤ A - q :=
        UInt64.le_iff_toNat_le.mpr (by rw [hd]; simp only [UInt64.reduceToNat]; omega)
      rw [UInt64.toNat_or, UInt64.toNat_sub_of_le _ _ hone, hd]
      rfl
  · have hfit := hfit rfl
    simp only [ite_true]
    rw [Numerics.shiftRightJam_add_mul_two_pow, ← hq]
    have hsum : (A + q).toNat = A.toNat + q.toNat := by
      rw [UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    by_cases hz : B % 2 ^ d = 0
    · simp only [hz, decide_true, ite_true, hsum]
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      rw [UInt64.toNat_or, hsum]
      rfl

end FloatLib.Numerics.FixedWord
