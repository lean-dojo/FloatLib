/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.LimbRound.Runtime
public import FloatLib.Kernels.FixedWord.Product.Proof
public import FloatLib.Kernels.FixedWord.Difference.Proof
public import FloatLib.Numerics.ShiftRightJam
import FloatLib.Numerics.ShiftRightJam.Proof
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Verified two-limb rounding

These theorems connect the native `UInt128` shifts, increments, and nearest-even rounding
operations to their natural-number meanings.

The runtime uses two `UInt64` limbs, and the proof model interprets them as one `Nat`.
Carry propagation, cross-limb shifts, low-bit insertion, ties-to-even rounding, and the sticky
combination of an aligned sum preserve that interpretation under the stated capacity bounds.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/-! ## Limb-local primitives -/

/-- Mathematical value of two-limb increment when it does not overflow. -/
theorem UInt128.increment_toNat (value : UInt128)
    (hfit : value.toNat + 1 < 2 ^ 128) :
    value.increment.toNat = value.toNat + 1 := by
  let sum := add64 value.lo 1
  have hsum :
      sum.value.toNat + sum.carry.toNat * 2 ^ 64 =
        value.lo.toNat + 1 := by
    simpa [sum] using add64_toNat value.lo 1
  have hcarry : sum.carry.toNat ≤ 1 := by
    simpa [sum] using add64_carry_le_one value.lo 1
  have hhighFit :
      value.hi.toNat + sum.carry.toNat < 2 ^ 64 := by
    unfold UInt128.toNat at hfit
    have hsumNonnegative :
        sum.value.toNat + sum.carry.toNat * 2 ^ 64 ≥
          sum.carry.toNat * 2 ^ 64 := by omega
    by_contra h
    have hlarge :
        2 ^ 64 ≤ value.hi.toNat + sum.carry.toNat :=
      Nat.le_of_not_gt h
    have hpow : 2 ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
    rw [hpow] at hfit
    nlinarith
  have hhigh :
      (value.hi + sum.carry).toNat =
        value.hi.toNat + sum.carry.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hhighFit]
  unfold UInt128.increment UInt128.toNat
  dsimp only
  rw [hhigh]
  change
    sum.value.toNat + (value.hi.toNat + sum.carry.toNat) * 2 ^ 64 =
      value.lo.toNat + value.hi.toNat * 2 ^ 64 + 1
  calc
    sum.value.toNat + (value.hi.toNat + sum.carry.toNat) * 2 ^ 64 =
        (sum.value.toNat + sum.carry.toNat * 2 ^ 64) +
          value.hi.toNat * 2 ^ 64 := by ring
    _ = (value.lo.toNat + 1) + value.hi.toNat * 2 ^ 64 := by
      rw [hsum]
    _ = value.lo.toNat + value.hi.toNat * 2 ^ 64 + 1 := by ring

/-- Setting the low bit of a two-limb value agrees with natural-number bitwise OR. -/
@[simp, grind =] theorem UInt128.setLowBit_toNat (value : UInt128) :
    value.setLowBit.toNat = value.toNat ||| 1 := by
  have hlow : value.lo.toNat < 2 ^ 64 :=
    value.lo.toNat_lt
  have hone : (1 : Nat) < 2 ^ 64 := by norm_num
  have hlowSet : value.lo.toNat ||| 1 < 2 ^ 64 :=
    Nat.or_lt_two_pow hlow hone
  unfold UInt128.setLowBit UInt128.toNat
  rw [UInt64.toNat_or]
  simp only [UInt64.toNat_one]
  calc
    (value.lo.toNat ||| 1) + value.hi.toNat * 2 ^ 64 =
        2 ^ 64 * value.hi.toNat + (value.lo.toNat ||| 1) := by ring
    _ = (2 ^ 64 * value.hi.toNat) ||| (value.lo.toNat ||| 1) :=
      Nat.two_pow_add_eq_or_of_lt hlowSet value.hi.toNat
    _ = ((2 ^ 64 * value.hi.toNat) ||| value.lo.toNat) ||| 1 := by
      rw [Nat.or_assoc]
    _ = (2 ^ 64 * value.hi.toNat + value.lo.toNat) ||| 1 := by
      rw [Nat.two_pow_add_eq_or_of_lt hlow value.hi.toNat]
    _ = (value.lo.toNat + value.hi.toNat * 2 ^ 64) ||| 1 := by
      congr 1
      ring

/-- Setting the low bit of an even two-limb value adds one. -/
theorem UInt128.setLowBit_toNat_of_even (value : UInt128)
    (heven : value.toNat % 2 = 0) :
    value.setLowBit.toNat = value.toNat + 1 := by
  have happend :=
    Nat.shiftLeft_add_eq_or_of_lt (a := value.toNat / 2) (i := 1) (b := 1) (by norm_num)
  rw [Nat.shiftLeft_eq, pow_one, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heven)] at happend
  rw [UInt128.setLowBit_toNat, ← happend]

namespace UInt128

/-! ## Cross-limb shifts -/

/-- The native two-word one-bit shift is floor division by two. -/
@[simp, grind =] theorem shiftRightOne_toNat (value : UInt128) :
    value.shiftRightOne.toNat = value.toNat / 2 := by
  have hhigh :
      (value.hi >>> 1).toNat = value.hi.toNat / 2 := by
    rw [UInt64.toNat_shiftRight]
    rw [show UInt64.toNat 1 % 64 = 1 by decide]
    norm_num [Nat.shiftRight_eq_div_pow]
  have hlow :
      (value.lo >>> 1).toNat = value.lo.toNat / 2 := by
    rw [UInt64.toNat_shiftRight]
    rw [show UInt64.toNat 1 % 64 = 1 by decide]
    norm_num [Nat.shiftRight_eq_div_pow]
  have hbit :
      (value.hi &&& 1).toNat = value.hi.toNat % 2 := by
    rw [UInt64.toNat_and]
    simp
  have hcarry :
      ((value.hi &&& 1) <<< 63).toNat =
        value.hi.toNat % 2 * 2 ^ 63 := by
    rw [UInt64.toNat_shiftLeft, hbit]
    rw [show UInt64.toNat 63 % 64 = 63 by decide]
    simp only [Nat.shiftLeft_eq]
    have hmod : value.hi.toNat % 2 < 2 :=
      Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_of_lt]
    nlinarith
  have hlowBound : value.lo.toNat / 2 < 2 ^ 63 := by
    have hlo := value.lo.toNat_lt
    omega
  have hor :
      (value.lo.toNat / 2) ||| (value.hi.toNat % 2 * 2 ^ 63) =
        value.lo.toNat / 2 + value.hi.toNat % 2 * 2 ^ 63 := by
    rw [Nat.or_comm]
    simpa [Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm] using
      (Nat.shiftLeft_add_eq_or_of_lt hlowBound
        (value.hi.toNat % 2)).symm
  unfold shiftRightOne UInt128.toNat
  rw [UInt64.toNat_or, hlow, hcarry, hor, hhigh]
  have hloDecompose := Nat.mod_add_div value.lo.toNat 2
  have hhiDecompose := Nat.mod_add_div value.hi.toNat 2
  norm_num at hloDecompose hhiDecompose ⊢
  omega

private theorem lowTwoBits_toNat (value : UInt128) :
    (value.lo &&& 3).toNat = value.toNat % 4 := by
  rw [UInt64.toNat_and]
  change value.lo.toNat &&& 3 = value.toNat % 4
  rw [show 3 = 2 ^ 2 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  unfold UInt128.toNat
  simp [Nat.add_mod, Nat.mul_mod]

/-! ## Nearest-even right shifts -/

/-- Native one-bit nearest-even rounding agrees with the mathematical rounder. -/
theorem roundShiftRightOneEven_toNat (value : UInt128) :
    value.roundShiftRightOneEven.toNat =
      FloatLib.Numerics.roundShiftRightEven
        value.toNat 1 := by
  have hshift := value.shiftRightOne_toNat
  have hfitShift :
      value.shiftRightOne.toNat + 1 < 2 ^ 128 := by
    rw [hshift]
    have := value.toNat_lt
    omega
  have hbits := lowTwoBits_toNat value
  rw [FloatLib.Numerics.roundShiftRightEven_one]
  unfold roundShiftRightOneEven
  dsimp only
  by_cases hround : value.toNat % 4 = 3
  · have hnative : value.lo &&& 3 = 3 := by
      apply UInt64.toNat_inj.mp
      rw [hbits, hround]
      decide
    simp only [hnative, beq_self_eq_true, ite_true]
    rw [increment_toNat _ hfitShift, hshift]
    simp [hround]
  · have hnative : value.lo &&& 3 ≠ 3 := by
      intro heq
      apply hround
      have heqNat := congrArg UInt64.toNat heq
      rw [hbits] at heqNat
      simpa using heqNat
    simp only [hnative, beq_iff_eq, ite_false, hshift, hround]

/-- Below one word, a two-limb value is its low limb plus a multiple of `2 ^ shift`. -/
private theorem toNat_eq_lo_add_two_pow_mul (value : UInt128) (shift : Nat)
    (hshift : shift < 64) :
    value.toNat = value.lo.toNat + 2 ^ shift * (value.hi.toNat * 2 ^ (64 - shift)) := by
  have hpow : 2 ^ 64 = 2 ^ shift * 2 ^ (64 - shift) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hshift)]
  unfold UInt128.toNat
  rw [hpow]
  ring

/--
Below one word, generic nearest-even rounding of a two-limb value inspects only the discarded
bits of its low limb.
-/
private theorem roundShiftRightEven_eq_lowBits (value : UInt128) (shift : Nat)
    (hshift : shift < 64) :
    FloatLib.Numerics.roundShiftRightEven value.toNat shift =
      if value.lo.toNat % 2 ^ shift < 2 ^ (shift - 1) then
        value.toNat.shiftRight shift
      else if value.lo.toNat % 2 ^ shift > 2 ^ (shift - 1) then
        value.toNat.shiftRight shift + 1
      else if value.toNat.shiftRight shift % 2 == 0 then
        value.toNat.shiftRight shift
      else
        value.toNat.shiftRight shift + 1 := by
  rcases Nat.eq_zero_or_pos shift with rfl | hpositive
  · simp [Nat.mod_one]
  have hremainderNat :
      value.toNat - (value.toNat >>> shift <<< shift) =
        value.lo.toNat % 2 ^ shift := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, ← Nat.mod_eq_sub_div_mul,
      toNat_eq_lo_add_two_pow_mul value shift hshift, Nat.add_mul_mod_self_left]
  change
    value.toNat - (value.toNat.shiftRight shift).shiftLeft shift =
      value.lo.toNat % 2 ^ shift at hremainderNat
  rw [FloatLib.Numerics.roundShiftRightEven_def]
  simp only [beq_iff_eq, Nat.ne_of_gt hpositive, ite_false]
  rw [hremainderNat]

/--
A native nearest-even choice between a quotient and its increment has the value of the
natural-number choice once its comparisons, parity test and candidates are interpreted.
-/
private theorem toNat_nearestEvenChoice {α : Type} (toNat : α → Nat)
    (remainder half : UInt64) (even : Bool) (quotient increment : α)
    (remainderNat halfNat quotientNat : Nat)
    (hremainder : remainder.toNat = remainderNat) (hhalf : half.toNat = halfNat)
    (heven : even = (quotientNat % 2 == 0))
    (hquotient : toNat quotient = quotientNat)
    (hincrement : toNat increment = quotientNat + 1) :
    toNat
        (if remainder < half then quotient
        else if remainder > half then increment
        else if even then quotient
        else increment) =
      if remainderNat < halfNat then quotientNat
      else if remainderNat > halfNat then quotientNat + 1
      else if quotientNat % 2 == 0 then quotientNat
      else quotientNat + 1 := by
  subst heven
  simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, hremainder, hhalf]
  split_ifs <;> assumption

/--
When the shifted result fits one limb, `shiftRightLow` is the mathematical right shift of the
two-limb input.

At `shift = 0` the fit condition makes the high limb zero, and the low limb is the whole value.
-/
theorem shiftRightLow_toNat (value : UInt128) (shift : Nat)
    (hshift : shift < 64)
    (hhigh : value.hi.toNat < 2 ^ shift) :
    (shiftRightLow value shift).toNat = value.toNat >>> shift := by
  rcases Nat.eq_zero_or_pos shift with rfl | hpositive
  · have hhi : value.hi = 0 := UInt64.toNat_inj.mp (by simpa using hhigh)
    simp [shiftRightLow, UInt128.toNat, hhi]
  have hcomplement : 64 - shift < 64 := by omega
  have hlowBound : value.lo.toNat >>> shift < 2 ^ (64 - shift) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]
    have hlo := value.lo.toNat_lt
    have hpow : 2 ^ (64 - shift) * 2 ^ shift = 2 ^ 64 := by
      rw [← pow_add]
      congr
      omega
    simpa [hpow] using hlo
  have hhighShift :
      (value.hi <<< UInt64.ofNat (64 - shift)).toNat =
        value.hi.toNat <<< (64 - shift) := by
    apply FloatLib.Numerics.FixedWord.shiftLeft_toNat
      value.hi (64 - shift)
    rw [Nat.shiftLeft_eq]
    have hpow : 2 ^ shift * 2 ^ (64 - shift) = 2 ^ 64 := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hshift)]
    nlinarith
  have hor :
      (value.lo.toNat >>> shift) |||
          (value.hi.toNat <<< (64 - shift)) =
        (value.lo.toNat >>> shift) +
          (value.hi.toNat <<< (64 - shift)) := by
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlowBound, Nat.add_comm]
  rw [toNat_eq_lo_add_two_pow_mul value shift hshift]
  unfold shiftRightLow
  rw [UInt64.toNat_or,
    FloatLib.Numerics.FixedWord.shiftRight_toNat value.lo shift hshift,
    hhighShift, hor]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.add_mul_div_left _ _ (by positivity)]

/--
The one-limb result of native two-limb nearest-even rounding agrees with the common mathematical
rounder whenever the incremented quotient fits one word.

That bound already keeps the high limb below `2 ^ shift`, so the quotient fits one limb.
-/
theorem roundShiftRightEven_toNat (value : UInt128) (shift : Nat)
    (hshift : shift < 64)
    (hincrementFit : (value.toNat >>> shift) + 1 < 2 ^ 64) :
    (roundShiftRightEven value shift).toNat =
      FloatLib.Numerics.roundShiftRightEven
        value.toNat shift := by
  have hhigh : value.hi.toNat < 2 ^ shift := by
    by_contra hcontra
    have hlarge : 2 ^ 64 ≤ value.toNat >>> shift := by
      rw [Nat.shiftRight_eq_div_pow, Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
      unfold UInt128.toNat
      calc
        2 ^ 64 * 2 ^ shift = 2 ^ shift * 2 ^ 64 := Nat.mul_comm _ _
        _ ≤ value.hi.toNat * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ value.lo.toNat + value.hi.toNat * 2 ^ 64 := Nat.le_add_left _ _
    omega
  have hquotient := shiftRightLow_toNat value shift hshift hhigh
  have hremainder := uint64_lowBits_toNat value.lo shift hshift
  have hhalf :
      (((1 : UInt64) <<< UInt64.ofNat (shift - 1)).toNat) =
        2 ^ (shift - 1) :=
    uint64_powTwo_toNat (shift - 1) (by omega)
  have hincrement :
      (shiftRightLow value shift + 1).toNat =
        (value.toNat >>> shift) + 1 := by
    rw [UInt64.toNat_add, hquotient]
    exact Nat.mod_eq_of_lt hincrementFit
  have heven :
      ((shiftRightLow value shift &&& 1) == 0) =
        ((value.toNat >>> shift) % 2 == 0) := by
    simp [← UInt64.toNat_inj, hquotient]
  rw [roundShiftRightEven_eq_lowBits value shift hshift]
  unfold roundShiftRightEven
  exact toNat_nearestEvenChoice UInt64.toNat _ _ _ _ _ _ _ _
    hremainder hhalf heven hquotient hincrement

end UInt128

/--
Native two-limb nearest-even rounding with a two-limb quotient agrees with the common mathematical
rounder for every shift below 64.
-/
theorem UInt128.roundShiftRightEven128_toNat (value : UInt128) (shift : Nat)
    (hshift : shift < 64) :
    (UInt128.roundShiftRightEven128 value shift).toNat =
      FloatLib.Numerics.roundShiftRightEven value.toNat shift := by
  rcases Nat.eq_zero_or_pos shift with rfl | hpositive
  · simp [UInt128.roundShiftRightEven128, UInt128.shiftRight]
  have hquotient : (value.shiftRight shift).toNat = value.toNat >>> shift := by
    rw [UInt128.shiftRight_toNat, Nat.shiftRight_eq_div_pow]
  have hquotientFit : (value.shiftRight shift).toNat + 1 < 2 ^ 128 := by
    rw [hquotient, Nat.shiftRight_eq_div_pow]
    have hlt := value.toNat_lt
    have hdivLt : value.toNat / 2 ^ shift < 2 ^ 127 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc value.toNat < 2 ^ 128 := hlt
        _ = 2 ^ 127 * 2 ^ 1 := by norm_num
        _ ≤ 2 ^ 127 * 2 ^ shift :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hpositive)
    have : (2 : Nat) ^ 127 + 1 ≤ 2 ^ 128 := by norm_num
    omega
  have hincrement :
      (value.shiftRight shift).increment.toNat = (value.toNat >>> shift) + 1 := by
    rw [UInt128.increment_toNat _ hquotientFit, hquotient]
  have hremainder := uint64_lowBits_toNat value.lo shift hshift
  have hhalf :
      (((1 : UInt64) <<< UInt64.ofNat (shift - 1)).toNat) = 2 ^ (shift - 1) :=
    uint64_powTwo_toNat (shift - 1) (by omega)
  have hlowBit : (value.shiftRight shift).lo.toNat % 2 = (value.toNat >>> shift) % 2 := by
    rw [← hquotient]
    unfold UInt128.toNat
    omega
  have heven :
      (((value.shiftRight shift).lo &&& 1) == 0) = ((value.toNat >>> shift) % 2 == 0) := by
    rw [← hlowBit]
    simp [← UInt64.toNat_inj, UInt64.toNat_and, Nat.and_one_is_mod]
  rw [UInt128.roundShiftRightEven_eq_lowBits value shift hshift]
  unfold UInt128.roundShiftRightEven128
  exact UInt128.toNat_nearestEvenChoice UInt128.toNat _ _ _ _ _ _ _ _
    hremainder hhalf heven hquotient hincrement

/--
The two-word sticky combination is the natural-number jam of the exact aligned value. A sum needs
`A + q` to fit in two words; a difference needs only `B ≤ A * 2^d`, so exact cancellation to zero
is included.
-/
theorem UInt128.jamCombine_toNat (sameSign exact : Bool) (A q : UInt128) (B d : Nat)
    (hq : q.toNat = B / 2 ^ d) (hexact : exact = decide (B % 2 ^ d = 0))
    (hfit : sameSign = true → A.toNat + q.toNat < 2 ^ 128)
    (hsub : sameSign = false → B ≤ A.toNat * 2 ^ d) :
    (UInt128.jamCombine sameSign exact A q).toNat =
      Numerics.shiftRightJam
        (if sameSign then A.toNat * 2 ^ d + B else A.toNat * 2 ^ d - B) d := by
  unfold UInt128.jamCombine
  subst hexact
  cases sameSign
  · have hB := hsub rfl
    simp only [Bool.false_eq_true, ite_false]
    rw [Numerics.shiftRightJam_mul_two_pow_sub _ _ _ hB, ← hq]
    have hle : q.toNat ≤ A.toNat := by
      rw [hq]
      exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hB)
    have hd : (UInt128.sub A q).toNat = A.toNat - q.toNat := UInt128.sub_toNat A q hle
    have hone : ({ hi := 0, lo := 1 } : UInt128).toNat = 1 := by
      simp [UInt128.toNat]
    by_cases hz : B % 2 ^ d = 0
    · simp only [hz, decide_true, ite_true, hd]
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      have hlt : q.toNat < A.toNat := by
        rw [hq, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos d)]
        exact lt_of_le_of_ne hB fun h => hz (by rw [h, Nat.mul_mod_left])
      rw [UInt128.setLowBit_toNat, UInt128.sub_toNat _ _ (by rw [hd, hone]; omega), hd, hone]
  · have hfit := hfit rfl
    simp only [ite_true]
    rw [Numerics.shiftRightJam_add_mul_two_pow, ← hq]
    have hv := add128_value_toNat_of_carry_zero A q (add128_carry_eq_zero_of_lt A q hfit)
    by_cases hz : B % 2 ^ d = 0
    · simp only [hz, decide_true, ite_true, hv]
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false, UInt128.setLowBit_toNat, hv]

end FloatLib.Numerics.FixedWord
