/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Core.Runtime
import Mathlib.Tactic.Bound
import all Init.Data.Fin.Log2
import all Init.Data.UInt.Log2
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic

/-!
# Verified single-word primitives for executable numerical arithmetic

Native-word shifts, bit operations, and restoring square-root state have exact natural-number
interpretations. Nearest-even rounding is proved in `Core.Proof.Rounding`; wider two-limb values
and exact `64 × 64 → 128` multiplication are proved in `Core.Proof.UInt128`.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/--
A native-word sum has its ordinary natural-number value when that sum does not overflow the word.
-/
theorem uint64_add_toNat_of_lt (x y : UInt64)
    (hfit : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt hfit]

/-- A native-word product has its natural-number value when it does not overflow the word. -/
theorem uint64_mul_toNat_of_lt (x y : UInt64)
    (hfit : x.toNat * y.toNat < 2 ^ 64) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hfit]

/--
Mathematical meaning of a restoring square-root state, independent of the native carrier used by
the executable loop.
-/
def RestoringRootState.Represents
    {α : Type} (toNat : α → Nat)
    (state : RestoringRootState α) (value : Nat) : Prop :=
  toNat state.root * toNat state.root + toNat state.remainder = value ∧
    toNat state.remainder ≤ 2 * toNat state.root

/--
The root component of a valid restoring state fits in the requested precision whenever the
processed radicand fits in twice that precision.
-/
theorem RestoringRootState.root_lt_two_pow
    {α : Type} (toNat : α → Nat) (precision : Nat)
    {state : RestoringRootState α} {value : Nat}
    (hrep : state.Represents toNat value)
    (hvalue : value < 2 ^ (2 * precision)) :
    toNat state.root < 2 ^ precision := by
  apply Nat.mul_self_lt_mul_self_iff.mp
  rw [← pow_add, ← two_mul]
  exact (Nat.le_add_right _ _).trans_lt (hrep.1.symm ▸ hvalue)

/--
The root component of a valid restoring state is the exact floor square root, independently of
the machine-word carrier used by the executable loop.
-/
theorem RestoringRootState.root_eq_sqrt
    {α : Type} (toNat : α → Nat)
    {state : RestoringRootState α} {value : Nat}
    (hrep : state.Represents toNat value) :
    toNat state.root = Nat.sqrt value := by
  rw [← hrep.1]
  exact (Nat.sqrt_add_eq _ (by simpa only [two_mul] using hrep.2)).symm

/--
A valid restoring state contains the exact floor square root and its square remainder.
-/
theorem RestoringRootState.sqrt_spec
    {α : Type} (toNat : α → Nat)
    {state : RestoringRootState α} {value : Nat}
    (hrep : state.Represents toNat value) :
    toNat state.root = Nat.sqrt value ∧
      toNat state.remainder = value - Nat.sqrt value * Nat.sqrt value := by
  have hroot := RestoringRootState.root_eq_sqrt toNat hrep
  constructor
  · exact hroot
  · rw [← hroot]
    exact Nat.eq_sub_of_add_eq' hrep.1

/-- Masking a native word to one base-four digit always produces a value below four. -/
theorem maskedBaseFourDigit_lt (value : UInt64) :
    (value &&& 3).toNat < 4 := by
  rw [UInt64.toNat_and]
  exact lt_of_le_of_lt Nat.and_le_right (by decide)

/-- Native low-bit inspection is exactly natural-number parity. -/
theorem lowBitIsZero_eq_even (code : UInt64) :
    ((code &&& 1) == 0) = decide (code.toNat % 2 = 0) := by
  have hbit : (code &&& 1).toNat = code.toNat % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_one]
    norm_num [Nat.and_two_pow_sub_one_eq_mod]
  by_cases heven : code.toNat % 2 = 0
  · have hword : code &&& 1 = 0 := by
      apply UInt64.toNat_inj.mp
      simpa [hbit] using heven
    simp [hword, heven]
  · have hword : code &&& 1 ≠ 0 := by
      intro equality
      apply heven
      have equalityNat := congrArg UInt64.toNat equality
      simpa [hbit] using equalityNat
    simp [hword, heven]

/-- Native low-bit nonzero inspection is exactly odd natural-number parity. -/
theorem lowBitIsNonzero_eq_odd (code : UInt64) :
    ((code &&& 1) != 0) = (code.toNat % 2 != 0) := by
  rw [bne_eq, bne_eq, lowBitIsZero_eq_even]
  congr 1

/-- Inspecting the low bit of a two-limb word is natural-number parity. -/
theorem UInt128.lowBitIsZero_eq_even (code : UInt128) :
    ((code.lo &&& 1) == 0) = decide (code.toNat % 2 = 0) := by
  rw [FloatLib.Numerics.FixedWord.lowBitIsZero_eq_even]
  norm_num [UInt128.toNat, Nat.add_mod, Nat.mul_mod]

/-- Two-limb low-bit nonzero inspection is exactly odd natural-number parity. -/
theorem UInt128.lowBitIsNonzero_eq_odd (code : UInt128) :
    ((code.lo &&& 1) != 0) = (code.toNat % 2 != 0) := by
  rw [bne_eq, bne_eq, UInt128.lowBitIsZero_eq_even]
  congr 1

/--
Machine-word nearest-even selection has the same natural-number code as the shared scalar
selector.
-/
@[simp, grind =] theorem selectNearestEvenWord_toNat
    (comparison : Ordering) (lower upper : UInt64) :
    (selectNearestEvenWord comparison lower upper).toNat =
      selectNearestEvenNat comparison lower.toNat upper.toNat := by
  cases comparison
  · rfl
  · unfold selectNearestEvenWord selectNearestEvenNat
    rw [lowBitIsZero_eq_even]
    by_cases heven : lower.toNat % 2 = 0 <;> simp [heven]
  · rfl

/-- Native `UInt64.log2` has the same natural-number value as `Nat.log2`. -/
@[simp, grind =] theorem log2_toNat (value : UInt64) :
    value.log2.toNat = value.toNat.log2 := by
  unfold UInt64.log2 Fin.log2
  rfl

/-- When the high part is nonzero, the low bits do not change its leading-bit position. -/
theorem log2_low_add_high_mul_pow (low high offset : Nat)
    (hlow : low < 2 ^ offset) (hhigh : high ≠ 0) :
    (low + high * 2 ^ offset).log2 = offset + high.log2 := by
  have hvalue : low + high * 2 ^ offset ≠ 0 := by
    positivity
  apply (Nat.log2_eq_iff hvalue).2
  constructor
  · rw [pow_add]
    calc
      2 ^ offset * 2 ^ high.log2 ≤ 2 ^ offset * high :=
        Nat.mul_le_mul_left _ (Nat.log2_self_le hhigh)
      _ = high * 2 ^ offset := Nat.mul_comm _ _
      _ ≤ low + high * 2 ^ offset := Nat.le_add_left _ _
  · rw [Nat.add_assoc, pow_add]
    calc
      low + high * 2 ^ offset < 2 ^ offset + high * 2 ^ offset :=
        Nat.add_lt_add_right hlow _
      _ = 2 ^ offset * (high + 1) := by ring
      _ ≤ 2 ^ offset * 2 ^ (high.log2 + 1) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr Nat.lt_log2_self)

/-- A correct stage on `shift` bits extends to a correct stage on twice as many bits. -/
private theorem log2WordStep_toNat (shift : UInt64) (next : UInt64 → UInt64)
    (hshift : shift.toNat < 64)
    (hnext : ∀ value : UInt64, value.toNat < 2 ^ shift.toNat →
      (next value).toNat = value.toNat.log2)
    (value : UInt64) (hvalue : value.toNat < 2 ^ (shift.toNat + shift.toNat)) :
    (log2WordStep shift next value).toNat = value.toNat.log2 := by
  have hhigh : (value >>> shift).toNat = value.toNat / 2 ^ shift.toNat := by
    rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hshift, Nat.shiftRight_eq_div_pow]
  have hhigh_lt : (value >>> shift).toNat < 2 ^ shift.toNat := by
    rw [hhigh, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    simpa only [pow_add] using hvalue
  by_cases hzero : value >>> shift = 0
  · have hsmall : value.toNat < 2 ^ shift.toNat := by
      have hdiv : value.toNat / 2 ^ shift.toNat = 0 := by
        rw [← hhigh, hzero]
        rfl
      exact (Nat.div_eq_zero_iff.mp hdiv).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
    simpa [log2WordStep, hzero] using hnext value hsmall
  · have hhigh_ne : (value >>> shift).toNat ≠ 0 := by
      simpa only [← UInt64.toNat_inj, UInt64.toNat_zero] using hzero
    have hlog : value.toNat.log2 = shift.toNat + (value >>> shift).toNat.log2 := by
      have h := log2_low_add_high_mul_pow
        (value.toNat % 2 ^ shift.toNat) (value.toNat / 2 ^ shift.toNat) shift.toNat
        (Nat.mod_lt _ (Nat.two_pow_pos _)) (hhigh ▸ hhigh_ne)
      rw [Nat.mod_add_div'] at h
      simpa only [hhigh] using h
    have hvalue_ne : value.toNat ≠ 0 := by
      intro hz
      apply hhigh_ne
      simp [hhigh, hz]
    have hfit : shift.toNat + (next (value >>> shift)).toNat < 2 ^ 64 := by
      rw [hnext _ hhigh_lt, ← hlog]
      have hlt : value.toNat.log2 < 64 :=
        (Nat.log2_lt hvalue_ne).mpr value.toNat_lt
      omega
    simpa [log2WordStep, hzero, uint64_add_toNat_of_lt _ _ hfit,
      hnext _ hhigh_lt] using hlog.symm

/-- Each two-bit entry of the packed constant gives the logarithm of its four-bit index. -/
private theorem log2WordNibble_toNat (value : UInt64) (hvalue : value.toNat < 16) :
    (((0xffffaa50 : UInt64) >>> (value <<< 1)) &&& 3).toNat = value.toNat.log2 := by
  have hlookup : ∀ n : Fin 16,
      (((0xffffaa50 : UInt64) >>> (UInt64.ofNat n.val <<< 1)) &&& 3).toNat =
        n.val.log2 := by decide
  simpa only [UInt64.ofNat_toNat] using hlookup ⟨value.toNat, hvalue⟩

/-- The bounded word stages compute the natural-number binary logarithm exactly. -/
@[simp, grind =] theorem log2Word_toNat (value : UInt64) :
    (log2Word value).toNat = value.toNat.log2 := by
  have h4 := log2WordStep_toNat 4 _ (by decide) log2WordNibble_toNat
  unfold log2Word
  split
  · have hsmall : value.toNat < 2 := UInt64.lt_iff_toNat_lt.mp ‹value < 2›
    rw [Nat.log2_def]
    simp only [show ¬ 2 ≤ value.toNat by omega, ↓reduceIte]
    rfl
  · split
    · exact log2WordNibble_toNat value (UInt64.lt_iff_toNat_lt.mp ‹value < 16›)
    · split
      · exact h4 value (UInt64.lt_iff_toNat_lt.mp ‹value < 256›)
      · have h8 := log2WordStep_toNat 8 _ (by decide) h4
        have h16 := log2WordStep_toNat 16 _ (by decide) h8
        exact log2WordStep_toNat 32 _ (by decide) h16 value value.toNat_lt

/-- The bounded search agrees with `UInt64.log2`, including at zero. -/
theorem log2Word_eq_log2 (value : UInt64) : log2Word value = value.log2 := by
  apply UInt64.toNat_inj.mp
  rw [log2Word_toNat, log2_toNat]

/-- Compile direct calls through the proved word search. -/
@[csimp] theorem uint64_log2_eq_log2Word : UInt64.log2 = log2Word := by
  funext value
  exact (log2Word_eq_log2 value).symm

/--
If a nonzero native word fits below `2 ^ width`, then its leading-bit position is smaller than
`width`.
-/
theorem log2_toNat_lt_of_toNat_lt_two_pow
    (value : UInt64) (width : Nat)
    (hvalue : value ≠ 0) (hfit : value.toNat < 2 ^ width) :
    value.log2.toNat < width := by
  rw [log2_toNat, Nat.log2_lt]
  · exact hfit
  · simpa [← UInt64.toNat_inj] using hvalue

/-- A nonzero value shifted left by `shift` is at least `2 ^ (log2 value + shift)`. -/
theorem two_pow_log2_add_le_shiftLeft (value shift : Nat) (hvalue : value ≠ 0) :
    2 ^ (value.log2 + shift) ≤ value <<< shift := by
  rw [Nat.shiftLeft_eq, pow_add]
  exact Nat.mul_le_mul_right _ (Nat.log2_self_le hvalue)

/--
Moving a nonzero value's leading bit to `precision` puts it at or above `2 ^ precision`.

When the leading bit already lies above `precision`, the shift is zero and the value itself is at
least `2 ^ precision`.
-/
theorem two_pow_le_shiftLeft_sub_log2 (precision value : Nat) (hvalue : value ≠ 0) :
    2 ^ precision ≤ value <<< (precision - value.log2) :=
  (Nat.pow_le_pow_right (by decide) (by omega)).trans
    (two_pow_log2_add_le_shiftLeft value (precision - value.log2) hvalue)

/-- A shift that keeps the leading bit below `width` keeps the value below `2 ^ width`. -/
theorem shiftLeft_lt_two_pow_of_log2_add_le (value shift width : Nat)
    (hwidth : value.log2 + 1 + shift ≤ width) :
    value <<< shift < 2 ^ width := by
  rw [Nat.shiftLeft_eq]
  calc
    value * 2 ^ shift < 2 ^ (value.log2 + 1) * 2 ^ shift :=
      Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos _)
    _ = 2 ^ (value.log2 + 1 + shift) := by rw [← pow_add]
    _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) hwidth

/-- Moving the leading bit to `precision` keeps the value below the next power of two. -/
theorem shiftLeft_sub_log2_lt_two_pow (precision value : Nat)
    (hleading : value.log2 ≤ precision) :
    value <<< (precision - value.log2) < 2 ^ (precision + 1) :=
  shiftLeft_lt_two_pow_of_log2_add_le value _ _ (by omega)

/-- A value whose product with `2 ^ shift` stays below `2 ^ width ≤ 2 ^ shift` is zero. -/
theorem eq_zero_of_mul_two_pow_lt {value shift width : Nat}
    (hfit : value * 2 ^ shift < 2 ^ width) (hwidth : width ≤ shift) : value = 0 := by
  by_contra hne
  have hpow : 2 ^ width ≤ 2 ^ shift := Nat.pow_le_pow_right (by decide) hwidth
  have : 2 ^ shift ≤ value * 2 ^ shift := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
  omega

/--
A native left shift has its mathematical natural-number value when the result fits.

A fitting result already bounds the shift amount below the word width, except for the zero word,
which every shift leaves at zero.
-/
theorem shiftLeft_toNat (value : UInt64) (shift : Nat)
    (hfit : value.toNat <<< shift < 2 ^ 64) :
    (value <<< UInt64.ofNat shift).toNat = value.toNat <<< shift := by
  by_cases hshift : shift < 64
  · rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat_of_lt' (hshift.trans (by decide)),
      Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt hfit]
  · have hzero : value.toNat = 0 :=
      eq_zero_of_mul_two_pow_lt (by rwa [Nat.shiftLeft_eq] at hfit) (by omega)
    have hvalue : value = 0 := UInt64.toNat_inj.mp (by simpa using hzero)
    subst hvalue
    simp

/-- An in-range native left shift is multiplication modulo the word size. -/
theorem shiftLeft_toNat_mod (value : UInt64) (shift : Nat)
    (hshift : shift < 64) :
    (value <<< UInt64.ofNat shift).toNat =
      (value.toNat * 2 ^ shift) % 2 ^ 64 := by
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat_of_lt' (hshift.trans (by decide)),
    Nat.mod_eq_of_lt hshift, Nat.shiftLeft_eq]

/-- Shifting the native word `1` within range represents the corresponding power of two. -/
theorem uint64_powTwo_toNat (exponent : Nat) (hexponent : exponent < 64) :
    (((1 : UInt64) <<< UInt64.ofNat exponent).toNat) = 2 ^ exponent := by
  rw [shiftLeft_toNat (1 : UInt64) exponent]
  · exact Nat.one_shiftLeft exponent
  · simpa only [UInt64.toNat_one, Nat.one_shiftLeft] using
      (Nat.pow_lt_pow_right (by decide) hexponent : 2 ^ exponent < 2 ^ 64)

/--
Moving the low `inner` bits of a word to the high end gives
`(value % 2 ^ inner) * 2 ^ (64 - inner)`, for positive `inner`.

This is the wrapped half of a cross-limb right shift. Keeping it in the fixed-word core lets every
multi-limb backend share the same machine-word argument. From `inner = 64` on, the shift amount is
zero and both sides are the word itself.
-/
theorem shiftLeftLowBits_toNat (value : UInt64) (inner : Nat)
    (hpositive : 0 < inner) :
    (value <<< UInt64.ofNat (64 - inner)).toNat =
      (value.toNat % 2 ^ inner) * 2 ^ (64 - inner) := by
  by_cases hinner : inner < 64
  swap
  · rw [show 64 - inner = 0 by omega, Nat.mod_eq_of_lt (value.toNat_lt.trans_le
      (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp
  have hcomplement : 64 - inner < 64 := by omega
  have hpow : 2 ^ 64 = 2 ^ inner * 2 ^ (64 - inner) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hinner)]
  rw [shiftLeft_toNat_mod value (64 - inner) hcomplement, hpow, Nat.mul_mod_mul_right]

/-- A native right shift by a natural below 64 is the natural-number right shift. -/
theorem shiftRight_toNat (value : UInt64) (shift : Nat)
    (hshift : shift < 64) :
    (value >>> UInt64.ofNat shift).toNat = value.toNat >>> shift := by
  simp [Nat.mod_eq_of_lt hshift]

/--
Joining the two halves of a cross-limb right shift by `0 < inner < 64` gives
`low / 2 ^ inner + (high % 2 ^ inner) * 2 ^ (64 - inner)`.
-/
theorem shiftedPair_toNat (low high : UInt64) (inner : Nat)
    (hpositive : 0 < inner) (hinner : inner < 64) :
    ((low >>> UInt64.ofNat inner) |||
        (high <<< UInt64.ofNat (64 - inner))).toNat =
      low.toNat / 2 ^ inner +
        (high.toNat % 2 ^ inner) * 2 ^ (64 - inner) := by
  have hlow :
      (low >>> UInt64.ofNat inner).toNat =
        low.toNat / 2 ^ inner := by
    rw [shiftRight_toNat low inner hinner, Nat.shiftRight_eq_div_pow]
  have hhigh := shiftLeftLowBits_toNat high inner hpositive
  have hbound : low.toNat / 2 ^ inner < 2 ^ (64 - inner) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have hpow : 2 ^ (64 - inner) * 2 ^ inner = 2 ^ 64 := by
      rw [← pow_add]
      congr
      omega
    simpa [hpow] using low.toNat_lt
  rw [UInt64.toNat_or, hlow, hhigh, Nat.or_comm]
  calc
    (high.toNat % 2 ^ inner * 2 ^ (64 - inner)) |||
        low.toNat / 2 ^ inner =
      ((high.toNat % 2 ^ inner) <<< (64 - inner)) |||
        low.toNat / 2 ^ inner := by simp [Nat.shiftLeft_eq]
    _ = ((high.toNat % 2 ^ inner) <<< (64 - inner)) +
        low.toNat / 2 ^ inner :=
      (Nat.shiftLeft_add_eq_or_of_lt hbound
        (high.toNat % 2 ^ inner)).symm
    _ = low.toNat / 2 ^ inner +
        high.toNat % 2 ^ inner * 2 ^ (64 - inner) := by
      simp [Nat.shiftLeft_eq, Nat.add_comm]

namespace BaseFour

/-- Positional weight of one base-four digit. -/
def place (index : Nat) : Nat :=
  2 ^ (2 * index)

/--
Value reconstructed from the first `steps` digits of any machine-word base-four source.

Concrete radicand layouts provide only their digit reader; the positional recurrence and loop
proof are shared across one-word and multi-word square-root kernels.
-/
def digitsValue {α : Type} (digitAt : α → Nat → UInt64) (source : α) : Nat → Nat
  | 0 => 0
  | steps + 1 =>
      (digitAt source steps).toNat * place steps +
        digitsValue digitAt source steps

/-- Base-four digit selected from a machine word; indices below 32 avoid shift-count wraparound. -/
def wordDigit (value : UInt64) (index : Nat) : Nat :=
  ((value >>> UInt64.ofNat (2 * index)) &&& 3).toNat

/-- Value reconstructed from the first `steps` base-four digits of a machine word. -/
def wordDigits (value : UInt64) : Nat → Nat
  | 0 => 0
  | steps + 1 =>
      wordDigit value steps * place steps + wordDigits value steps

/-- Machine extraction agrees with natural-number base-four digit selection. -/
theorem wordDigit_eq
    (value : UInt64) (index : Nat) (hindex : index < 32) :
    wordDigit value index =
      (value.toNat / place index) % 4 := by
  unfold wordDigit place
  rw [UInt64.toNat_and, shiftRight_toNat value (2 * index) (by omega)]
  change (value.toNat >>> (2 * index)) &&& 3 =
    value.toNat / 2 ^ (2 * index) % 4
  rw [show (3 : Nat) = 2 ^ 2 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

/-- Advancing one base-four position multiplies its weight by four. -/
theorem place_succ (index : Nat) :
    place (index + 1) = place index * 4 := by
  simpa only [place, Nat.pow_mul] using Nat.pow_succ 4 index

/--
Generic refinement of a restoring loop from a proved digit step.

Only the carrier-specific step theorem and recursive equations are supplied by a backend. The
base-four accumulation and induction are independent of word width.
-/
theorem loop_represents
    {α β : Type}
    (toNat : α → Nat)
    (digitAt : β → Nat → UInt64)
    (step : UInt64 → RestoringRootState α → RestoringRootState α)
    (loop : β → Nat → RestoringRootState α → RestoringRootState α)
    (bound : Nat)
    (hloopZero : ∀ source state, loop source 0 state = state)
    (hloopSucc : ∀ source steps state,
      loop source (steps + 1) state =
        loop source steps (step (digitAt source steps) state))
    (hdigit : ∀ source index, (digitAt source index).toNat < 4)
    (hstep : ∀ state digit value,
      RestoringRootState.Represents toNat state value →
      value < bound →
      digit.toNat < 4 →
      RestoringRootState.Represents toNat
        (step digit state) (value * 4 + digit.toNat))
    (source : β) (steps : Nat)
    (state : RestoringRootState α) (value : Nat)
    (hrep : RestoringRootState.Represents toNat state value)
    (hfit : value * place steps + digitsValue digitAt source steps < bound) :
    RestoringRootState.Represents toNat (loop source steps state)
      (value * place steps + digitsValue digitAt source steps) := by
  induction steps generalizing state value with
  | zero =>
      rw [hloopZero]
      simpa [place, digitsValue, RestoringRootState.Represents] using hrep
  | succ steps ih =>
      rw [hloopSucc]
      let digit := digitAt source steps
      let next := step digit state
      let nextValue := value * 4 + digit.toNat
      have hplacePositive : 0 < place (steps + 1) := by
        simp [place]
      have hvalueLe :
          value ≤ value * place (steps + 1) +
            digitsValue digitAt source (steps + 1) := by
        exact le_trans
          (Nat.le_mul_of_pos_right value hplacePositive)
          (Nat.le_add_right _ _)
      have hvalue : value < bound :=
        lt_of_le_of_lt hvalueLe hfit
      have hnext :
          RestoringRootState.Represents toNat next nextValue := by
        exact hstep state digit value hrep hvalue (hdigit source steps)
      have hsame :
          nextValue * place steps + digitsValue digitAt source steps =
            value * place (steps + 1) +
              digitsValue digitAt source (steps + 1) := by
        dsimp only [nextValue, digit]
        rw [place_succ, digitsValue]
        ring
      have hnextFit :
          nextValue * place steps + digitsValue digitAt source steps <
            bound := by
        rw [hsame]
        exact hfit
      rw [← hsame]
      exact ih next nextValue hnext hnextFit

/-- Base-four positional weights multiply when their indices add. -/
theorem place_add (left right : Nat) :
    place (left + right) = place left * place right := by
  simp only [place, Nat.pow_mul, pow_add]

/-- Reconstructing the low base-four digits is reduction modulo their total width. -/
theorem wordDigits_eq_mod
    (value : UInt64) (steps : Nat) (hsteps : steps ≤ 32) :
    wordDigits value steps = value.toNat % place steps := by
  induction steps with
  | zero => simp [wordDigits, place, Nat.mod_one]
  | succ steps ih =>
      rw [wordDigits, wordDigit_eq value steps (by omega), ih (by omega)]
      simp only [place, Nat.pow_mul]
      rw [Nat.mod_pow_succ (b := 2 ^ 2) (k := steps)]
      ac_rfl

end BaseFour

/-- Machine-indexed bit inspection agrees with natural-number bit inspection. -/
@[simp, grind =] theorem bitAtWord_eq_testBit (value index : UInt64) :
    bitAtWord value index = value.toNat.testBit index.toNat := by
  unfold bitAtWord
  split
  next hindex =>
    have hindexNat : index.toNat < 64 := by
      simpa only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] using hindex
    rw [Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj,
      UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_one,
      Nat.mod_eq_of_lt hindexNat, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  next hindex =>
    have hindexNat : 64 ≤ index.toNat := by
      simpa [UInt64.lt_iff_toNat_lt] using hindex
    symm
    exact Nat.testBit_lt_two_pow
      (value.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) hindexNat))

/-- Natural value of a machine-indexed low-bit mask below the carrier width. -/
theorem lowMaskWord_toNat (width : UInt64) (hwidth : width < 64) :
    (lowMaskWord width).toNat = 2 ^ width.toNat - 1 := by
  have hwidthNat : width.toNat < 64 := by
    simpa [UInt64.lt_iff_toNat_lt] using hwidth
  have hpow : 2 ^ width.toNat < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by decide) hwidthNat
  unfold lowMaskWord
  rw [ite_eq_left hwidth, UInt64.toNat_sub_of_le]
  · simp only [UInt64.toNat_shiftLeft, UInt64.toNat_one]
    rw [Nat.mod_eq_of_lt hwidthNat, Nat.shiftLeft_eq, one_mul]
    change 2 ^ width.toNat % 2 ^ 64 - 1 = 2 ^ width.toNat - 1
    rw [Nat.mod_eq_of_lt hpow]
  · rw [UInt64.le_iff_toNat_le]
    simp only [UInt64.toNat_one, UInt64.toNat_shiftLeft]
    rw [Nat.mod_eq_of_lt hwidthNat, Nat.shiftLeft_eq, one_mul]
    rw [Nat.mod_eq_of_lt hpow]
    exact Nat.one_le_two_pow

/--
Machine-indexed low-bit extraction is reduction modulo `2 ^ width`.

From `width = 64` on, the mask keeps the whole word, which is already below `2 ^ width`.
-/
theorem lowBitsWord_toNat (value width : UInt64) :
    (lowBitsWord value width).toNat =
      value.toNat % 2 ^ width.toNat := by
  by_cases hwidthLt : width < 64
  · rw [lowBitsWord, UInt64.toNat_and,
      lowMaskWord_toNat width hwidthLt]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  · have hwidthNat : 64 ≤ width.toNat := by
      simpa [UInt64.lt_iff_toNat_lt] using hwidthLt
    simp only [lowBitsWord, lowMaskWord, hwidthLt, ite_false, UInt64.toNat_and]
    change value.toNat &&& 2 ^ 64 - 1 = value.toNat % 2 ^ width.toNat
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt value.toNat_lt,
      Nat.mod_eq_of_lt (value.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) hwidthNat))]

/--
Masking a native word to a `Nat`-indexed low-bit field agrees with reduction modulo the
corresponding power of two.

This theorem bridges kernels whose control flow uses `Nat` to the shared machine-indexed
`lowBitsWord` primitive; the executable data path remains on unboxed `UInt64` values.
-/
theorem uint64_lowBits_toNat (value : UInt64) (shift : Nat)
    (hshift : shift < 64) :
    (value &&& (((1 : UInt64) <<< UInt64.ofNat shift) - 1)).toNat =
      value.toNat % 2 ^ shift := by
  have hshiftNat : (UInt64.ofNat shift).toNat = shift :=
    UInt64.toNat_ofNat_of_lt' (hshift.trans (by decide))
  have hshiftWord : UInt64.ofNat shift < 64 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [hshiftNat]
    exact hshift
  have hbits :=
    lowBitsWord_toNat value (UInt64.ofNat shift)
  unfold lowBitsWord lowMaskWord at hbits
  rw [ite_eq_left hshiftWord] at hbits
  rw [hshiftNat] at hbits
  exact hbits

/--
Machine-indexed right shift agrees with natural-number right shift.

From the carrier width on, both sides are zero.
-/
theorem shiftRightWord_toNat (value shift : UInt64) :
    (shiftRightWord value shift).toNat =
      value.toNat >>> shift.toNat := by
  unfold shiftRightWord
  by_cases hshift : shift < 64
  · have hshiftNat : shift.toNat < 64 := by
      simpa [UInt64.lt_iff_toNat_lt] using hshift
    rw [ite_eq_left hshift, UInt64.toNat_shiftRight]
    rw [Nat.mod_eq_of_lt hshiftNat]
  · have hshiftNat : 64 ≤ shift.toNat := by
      simpa [UInt64.lt_iff_toNat_lt] using hshift
    rw [ite_eq_right hshift, UInt64.toNat_zero, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (value.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) hshiftNat))]

/--
Machine-width leading-zero counting, read as a natural number, with its machine subtraction and
increment interpreted exactly; the field is still the machine word `lowBitsWord value width`.
`countLeadingZerosWord_toNat_eq_log2` states the count through `value.toNat % 2 ^ width.toNat`.

The nonzero branch proves that `log2 + 1` is at most the retained field width before interpreting
the machine subtraction. This is the capacity invariant that rules out unsigned wraparound.
-/
theorem countLeadingZerosWord_toNat
    (value width : UInt64) :
    (countLeadingZerosWord value width).toNat =
      let truncated := lowBitsWord value width
      if truncated == 0 then
        width.toNat
      else
        width.toNat - (truncated.log2.toNat + 1) := by
  let truncated := lowBitsWord value width
  have htruncated :
      truncated.toNat = value.toNat % 2 ^ width.toNat := by
    exact lowBitsWord_toNat value width
  have htruncatedLt : truncated.toNat < 2 ^ width.toNat := by
    rw [htruncated]
    exact Nat.mod_lt _ (Nat.two_pow_pos width.toNat)
  unfold countLeadingZerosWord
  simp only [log2Word_eq_log2]
  change
    (if truncated == 0 then
      width
    else
      width - (truncated.log2 + 1)).toNat =
        if truncated == 0 then
          width.toNat
        else
          width.toNat - (truncated.log2.toNat + 1)
  split
  · rfl
  next hnonzero =>
    have hne : truncated ≠ 0 := fun hzero => hnonzero (by simp [hzero])
    have hlogLt :=
      log2_toNat_lt_of_toNat_lt_two_pow truncated width.toNat hne htruncatedLt
    have hlogBound :=
      log2_toNat_lt_of_toNat_lt_two_pow truncated 64 hne truncated.toNat_lt
    have hlogAdd :
        (truncated.log2 + 1).toNat =
          truncated.log2.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
    rw [UInt64.toNat_sub_of_le]
    · rw [hlogAdd]
    · rw [UInt64.le_iff_toNat_le, hlogAdd]
      omega

/--
The number of leading zeros in the low `width` bits of `value`, in natural-number arithmetic: with
`field = value.toNat % 2 ^ width.toNat`, it is `width` for a zero field and
`width - (Nat.log2 field + 1)` otherwise.
-/
theorem countLeadingZerosWord_toNat_eq_log2 (value width : UInt64) :
    (countLeadingZerosWord value width).toNat =
      if value.toNat % 2 ^ width.toNat = 0 then
        width.toNat
      else
        width.toNat - ((value.toNat % 2 ^ width.toNat).log2 + 1) := by
  rw [countLeadingZerosWord_toNat]
  simp only [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_zero, log2_toNat, lowBitsWord_toNat]

/-- Machine-width equal-bit run counting reduces to the shared leading-zero primitive. -/
theorem countLeadingRunWord_toNat
    (value width : UInt64) (bit : Bool) :
    (countLeadingRunWord value width bit).toNat =
      let source := if bit then ~~~value else value
      let truncated := lowBitsWord source width
      if truncated == 0 then
        width.toNat
      else
        width.toNat - (truncated.log2.toNat + 1) := by
  unfold countLeadingRunWord
  exact countLeadingZerosWord_toNat
    (if bit then ~~~value else value) width

/--
For `width ≤ 64`, the length of the leading run of `bit` in the low `width` bits of `value`, in
natural-number arithmetic. In general it is the leading-zero count of the field of `~~~value` when
`bit` is set and of `value` otherwise (`countLeadingZerosWord_toNat_eq_log2`), so for `width > 64`
a set `bit` also counts the field bits above bit 63 as ones.
-/
theorem countLeadingRunWord_toNat_eq_log2 (value width : UInt64) (bit : Bool) :
    (countLeadingRunWord value width bit).toNat =
      let field := (if bit then ~~~value else value).toNat % 2 ^ width.toNat
      if field = 0 then width.toNat else width.toNat - (field.log2 + 1) := by
  unfold countLeadingRunWord
  exact countLeadingZerosWord_toNat_eq_log2 (if bit then ~~~value else value) width

end FloatLib.Numerics.FixedWord
