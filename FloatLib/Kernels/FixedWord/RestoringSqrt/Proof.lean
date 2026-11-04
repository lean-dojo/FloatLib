/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.RestoringSqrt.Compiler
public import FloatLib.Kernels.FixedWord.Difference.Proof
public import FloatLib.Kernels.FixedWord.LimbRound.Proof
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.Rat.Cast.Order

/-!
# Restoring square-root refinement

We prove that the restoring loop returns the floor square root and square remainder of its input,
using an invariant that relates the consumed radicand prefix to the partial root at each
shift-and-subtract step. With this proof, callers can use the kernel without a runtime certificate
check, as long as the scaled radicand fits the fixed-word bound.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.RestoringSquareRoot

open FloatLib.Numerics.FixedWord
open FloatLib.Numerics.FixedWord.BaseFour

/-! ## Restoring-loop invariant -/

local notation "RootRep128" =>
  RestoringRootState.Represents UInt128.toNat

private theorem digit_lt_four (radicand : UInt256) (index : Nat) :
    (digitAt radicand index).toNat < 4 := by
  unfold digitAt
  split
  · exact maskedBaseFourDigit_lt _
  · split
    · exact maskedBaseFourDigit_lt _
    · split <;> exact maskedBaseFourDigit_lt _

private theorem shiftLeftOne_eq (value : UInt128) :
    shiftLeftOne value = UInt128.shiftLeft value 1 := by
  simp [shiftLeftOne, UInt128.shiftLeft]

private theorem shiftLeftTwo_eq (value : UInt128) :
    shiftLeftTwo value = UInt128.shiftLeft value 2 := by
  simp [shiftLeftTwo, UInt128.shiftLeft]

private theorem shiftedLow_append_digit
    (value digit : UInt64)
    (hdigit : digit.toNat < 4) :
    ((value <<< 2) ||| digit).toNat =
      (value <<< 2).toNat + digit.toNat := by
  have hshift :
      (value <<< 2).toNat = (value.toNat % 2 ^ 62) <<< 2 := by
    rw [UInt64.toNat_shiftLeft]
    norm_num [Nat.shiftLeft_eq]
    change
      value.toNat * 4 % (2 ^ 62 * 4) =
        value.toNat % 2 ^ 62 * 4
    exact Nat.mul_mod_mul_right 4 value.toNat (2 ^ 62)
  rw [UInt64.toNat_or, hshift]
  exact (Nat.shiftLeft_add_eq_or_of_lt hdigit
    (value.toNat % 2 ^ 62)).symm

private theorem rootStep_spec
    (state : RestoringRootState UInt128) (digit : UInt64) (value : Nat)
    (hrep : RootRep128 state value)
    (hvalue : value < 2 ^ 250)
    (hdigit : digit.toNat < 4) :
    RootRep128 (rootStep digit state) (value * 4 + digit.toNat) := by
  let expandedBase := shiftLeftTwo state.remainder
  let expanded : UInt128 :=
    { expandedBase with lo := expandedBase.lo ||| digit }
  let trialBase := shiftLeftTwo state.root
  let trial := trialBase.setLowBit
  let doubledRoot := shiftLeftOne state.root
  have hroot :=
    RestoringRootState.root_lt_two_pow UInt128.toNat 125 hrep hvalue
  have hremainderLe :
      state.remainder.toNat ≤ 2 * state.root.toNat :=
    hrep.2
  have hremainder : state.remainder.toNat < 2 ^ 126 := by
    norm_num at hroot ⊢
    omega
  have htrialBase :
      trialBase.toNat = state.root.toNat * 4 := by
    dsimp only [trialBase]
    rw [shiftLeftTwo_eq, UInt128.shiftLeft_toNat_eq_mul _ 2 (by omega)]
    norm_num
  have hdoubledRoot :
      doubledRoot.toNat = state.root.toNat * 2 := by
    dsimp only [doubledRoot]
    rw [shiftLeftOne_eq, UInt128.shiftLeft_toNat_eq_mul _ 1 (by omega)]
    norm_num
  have hexpandedBase :
      expandedBase.toNat = state.remainder.toNat * 4 := by
    dsimp only [expandedBase]
    rw [shiftLeftTwo_eq, UInt128.shiftLeft_toNat_eq_mul _ 2 (by omega)]
    norm_num
  have hexpanded :
      expanded.toNat =
        state.remainder.toNat * 4 + digit.toNat := by
    have hexpandedLow :
        (expandedBase.lo ||| digit).toNat =
          expandedBase.lo.toNat + digit.toNat := by
      dsimp only [expandedBase, shiftLeftTwo]
      exact shiftedLow_append_digit state.remainder.lo digit hdigit
    rw [UInt128.toNat.eq_1 expanded]
    change
      (expandedBase.lo ||| digit).toNat +
          expandedBase.hi.toNat * 2 ^ 64 =
        state.remainder.toNat * 4 + digit.toNat
    rw [hexpandedLow]
    have hbase :
        expandedBase.lo.toNat + expandedBase.hi.toNat * 2 ^ 64 =
          state.remainder.toNat * 4 := by
      simpa only [UInt128.toNat] using hexpandedBase
    omega
  have htrial :
      trial.toNat = state.root.toNat * 4 + 1 := by
    dsimp only [trial]
    rw [UInt128.setLowBit_toNat_of_even _ (by rw [htrialBase]; omega), htrialBase]
  by_cases hbelow :
      state.remainder.toNat * 4 + digit.toNat <
        state.root.toNat * 4 + 1
  · have hnativeBelow : UInt128.less expanded trial = true := by
      apply (UInt128.less_eq_true_iff expanded trial).2
      simpa [hexpanded, htrial] using hbelow
    have hstep :
        rootStep digit state =
          { root := doubledRoot, remainder := expanded } := by
      change
        (if UInt128.less expanded trial = true then
            (⟨doubledRoot, expanded⟩ : RestoringRootState UInt128)
          else
            ⟨doubledRoot.setLowBit, UInt128.sub expanded trial⟩) =
          (⟨doubledRoot, expanded⟩ : RestoringRootState UInt128)
      rw [ite_eq_left hnativeBelow]
    rw [hstep]
    have hsquare :
        state.root.toNat * 2 * (state.root.toNat * 2) =
          4 * (state.root.toNat * state.root.toNat) := by
      ring
    have hvalueEq := hrep.1
    constructor
    · rw [hdoubledRoot, hexpanded]
      omega
    · rw [hdoubledRoot, hexpanded]
      omega
  · have hnativeBelow : UInt128.less expanded trial = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      have hlt := (UInt128.less_eq_true_iff expanded trial).1 htrue
      rw [hexpanded, htrial] at hlt
      exact hbelow hlt
    have hordered : trial.toNat ≤ expanded.toNat := by
      rw [hexpanded, htrial]
      omega
    have hrootOdd :
        doubledRoot.setLowBit.toNat =
          state.root.toNat * 2 + 1 := by
      rw [UInt128.setLowBit_toNat_of_even _ (by rw [hdoubledRoot]; omega), hdoubledRoot]
    have hremainderSub :
        (UInt128.sub expanded trial).toNat =
          state.remainder.toNat * 4 + digit.toNat -
            (state.root.toNat * 4 + 1) := by
      rw [UInt128.sub_toNat expanded trial hordered, hexpanded, htrial]
    have hsubAdd :
        (state.remainder.toNat * 4 + digit.toNat -
            (state.root.toNat * 4 + 1)) +
            (state.root.toNat * 4 + 1) =
          state.remainder.toNat * 4 + digit.toNat :=
      Nat.sub_add_cancel (by omega)
    have hstep :
        rootStep digit state =
          { root := doubledRoot.setLowBit
            remainder := UInt128.sub expanded trial } := by
      change
        (if UInt128.less expanded trial = true then
            (⟨doubledRoot, expanded⟩ : RestoringRootState UInt128)
          else
            ⟨doubledRoot.setLowBit, UInt128.sub expanded trial⟩) =
          (⟨doubledRoot.setLowBit,
              UInt128.sub expanded trial⟩ :
            RestoringRootState UInt128)
      rw [ite_eq_right (by simpa only [hnativeBelow] using Bool.false_ne_true)]
    rw [hstep]
    have hsquare :
        (state.root.toNat * 2 + 1) * (state.root.toNat * 2 + 1) =
          4 * (state.root.toNat * state.root.toNat) + 4 * state.root.toNat + 1 := by
      ring
    have hvalueEq := hrep.1
    constructor
    · rw [hrootOdd, hremainderSub]
      omega
    · rw [hrootOdd, hremainderSub]
      apply Nat.sub_le_iff_le_add.mpr
      omega

/-! ## Four-word radicand reconstruction -/

private theorem digitAt_limb0
    (radicand : UInt256) (index : Nat) (hindex : index < 32) :
    (digitAt radicand index).toNat =
      wordDigit radicand.limb0 index := by
  simp [digitAt, wordDigit, hindex]

private theorem digitAt_limb1
    (radicand : UInt256) (index : Nat)
    (hlower : 32 ≤ index) (hupper : index < 64) :
    (digitAt radicand index).toNat =
      wordDigit radicand.limb1 (index - 32) := by
  simp [digitAt, wordDigit, Nat.not_lt.mpr hlower, hupper]

private theorem digitAt_limb2
    (radicand : UInt256) (index : Nat)
    (hlower : 64 ≤ index) (hupper : index < 96) :
    (digitAt radicand index).toNat =
      wordDigit radicand.limb2 (index - 64) := by
  simp [digitAt, wordDigit, Nat.not_lt.mpr (by omega : 32 ≤ index),
    Nat.not_lt.mpr hlower, hupper]

private theorem digitAt_limb3
    (radicand : UInt256) (index : Nat) (hlower : 96 ≤ index) :
    (digitAt radicand index).toNat =
      wordDigit radicand.limb3 (index - 96) := by
  simp [digitAt, wordDigit, Nat.not_lt.mpr (by omega : 32 ≤ index),
    Nat.not_lt.mpr (by omega : 64 ≤ index),
    Nat.not_lt.mpr hlower]

private theorem digitsValue_limb0
    (radicand : UInt256) (steps : Nat) (hsteps : steps ≤ 32) :
    digitsValue digitAt radicand steps =
      wordDigits radicand.limb0 steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [digitsValue, wordDigits,
        digitAt_limb0 radicand steps (by omega), ih (by omega)]

/--
Past a word boundary at digit `base`, the reconstruction adds the digits of the next word at that
boundary's place value.
-/
private theorem digitsValue_add_word
    (radicand : UInt256) (word : UInt64) (base steps : Nat)
    (hdigit : ∀ index, base ≤ index → index < base + steps →
      (digitAt radicand index).toNat = wordDigit word (index - base)) :
    digitsValue digitAt radicand (base + steps) =
      wordDigits word steps * place base +
        digitsValue digitAt radicand base := by
  induction steps with
  | zero => simp [wordDigits]
  | succ steps ih =>
      change
        (digitAt radicand (base + steps)).toNat *
              place (base + steps) +
            digitsValue digitAt radicand (base + steps) =
          (wordDigit word steps * place steps +
              wordDigits word steps) * place base +
            digitsValue digitAt radicand base
      rw [hdigit (base + steps) (by omega) (by omega), Nat.add_sub_cancel_left,
        ih (fun index hlower hupper => hdigit index hlower (by omega)), place_add]
      ring

private theorem digitsValue_limb1
    (radicand : UInt256) (steps : Nat) (hsteps : steps ≤ 32) :
    digitsValue digitAt radicand (32 + steps) =
      wordDigits radicand.limb1 steps * place 32 +
        wordDigits radicand.limb0 32 := by
  rw [digitsValue_add_word radicand radicand.limb1 32 steps
      (fun index hlower hupper => digitAt_limb1 radicand index hlower (by omega)),
    digitsValue_limb0 radicand 32 le_rfl]

private theorem digitsValue_limb2
    (radicand : UInt256) (steps : Nat) (hsteps : steps ≤ 32) :
    digitsValue digitAt radicand (64 + steps) =
      wordDigits radicand.limb2 steps * place 64 +
        wordDigits radicand.limb1 32 * place 32 +
        wordDigits radicand.limb0 32 := by
  rw [digitsValue_add_word radicand radicand.limb2 64 steps
      (fun index hlower hupper => digitAt_limb2 radicand index hlower (by omega)),
    digitsValue_limb1 radicand 32 le_rfl]
  ring

private theorem digitsValue_limb3
    (radicand : UInt256) (steps : Nat) :
    digitsValue digitAt radicand (96 + steps) =
      wordDigits radicand.limb3 steps * place 96 +
        wordDigits radicand.limb2 32 * place 64 +
        wordDigits radicand.limb1 32 * place 32 +
        wordDigits radicand.limb0 32 := by
  rw [digitsValue_add_word radicand radicand.limb3 96 steps
      (fun index hlower _ => digitAt_limb3 radicand index hlower),
    digitsValue_limb2 radicand 32 le_rfl]
  ring

/-! ## Restoring-loop refinement -/

private theorem rootLoop_spec
    (radicand : UInt256) (steps : Nat)
    (state : RestoringRootState UInt128) (value : Nat)
    (hrep : RootRep128 state value)
    (hfit :
      value * place steps + digitsValue digitAt radicand steps < 2 ^ 250) :
    RootRep128 (rootLoop radicand steps state)
      (value * place steps + digitsValue digitAt radicand steps) :=
  loop_represents UInt128.toNat digitAt rootStep rootLoop (2 ^ 250)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    digit_lt_four rootStep_spec radicand steps state value hrep hfit

private theorem rootAndRemainder_rep
    (radicand : UInt256) (steps : Nat)
    (hdigits : digitsValue digitAt radicand steps = radicand.toNat)
    (hfit : radicand.toNat < 2 ^ 250) :
    RootRep128 (rootAndRemainder radicand steps) radicand.toNat := by
  have hinitial :
      RootRep128
        ({ root := ⟨0, 0⟩, remainder := ⟨0, 0⟩ } :
          RestoringRootState UInt128) 0 := by
    simp [RestoringRootState.Represents, UInt128.toNat]
  have hloop :=
    rootLoop_spec radicand steps
      { root := ⟨0, 0⟩, remainder := ⟨0, 0⟩ } 0 hinitial
  rw [zero_mul, zero_add, hdigits] at hloop
  exact hloop hfit

/-- A limb weighted by `place base` inside a value below `place (base + digits)` has at most
`digits` base-four digits. -/
private theorem mod_place_eq_of_mul_place_le (limb value base digits : Nat)
    (hlimb : limb * place base ≤ value) (hvalue : value < place (base + digits)) :
    limb % place digits = limb := by
  apply Nat.mod_eq_of_lt
  rw [place_add, Nat.mul_comm] at hvalue
  exact Nat.lt_of_mul_lt_mul_right (hlimb.trans_lt hvalue)

/--
The first `steps` base-four digits reconstruct every radicand below `2^(2 * steps)`, for any digit
count up to 128.

This covers both the 96- and 113-digit kernels.
-/
private theorem digitsValue_eq_toNat
    (radicand : UInt256) (steps : Nat)
    (hupper : steps ≤ 128)
    (hfit : radicand.toNat < 2 ^ (2 * steps)) :
    digitsValue digitAt radicand steps = radicand.toNat := by
  have h0 := radicand.limb0.toNat_lt
  have h1 := radicand.limb1.toNat_lt
  have h2 := radicand.limb2.toNat_lt
  have hlimb0 : radicand.limb0.toNat % place 32 = radicand.limb0.toNat := by
    apply Nat.mod_eq_of_lt
    simpa [place] using h0
  have hlimb1 : radicand.limb1.toNat % place 32 = radicand.limb1.toNat := by
    apply Nat.mod_eq_of_lt
    simpa [place] using h1
  have hvalue :
      radicand.toNat =
        radicand.limb0.toNat + radicand.limb1.toNat * 2 ^ 64 +
          radicand.limb2.toNat * 2 ^ 128 + radicand.limb3.toNat * 2 ^ 192 := rfl
  by_cases hfirst : steps ≤ 32
  · -- Only the low limb is nonzero, and it has at most `2 * steps` significant bits.
    have hfit64 : radicand.toNat < 2 ^ 64 :=
      hfit.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have hlimb0Steps :=
      mod_place_eq_of_mul_place_le radicand.limb0.toNat radicand.toNat 0 steps
        (by unfold place; rw [hvalue]; omega)
        (by rw [Nat.zero_add]; exact hfit)
    rw [digitsValue_limb0 radicand steps hfirst, wordDigits_eq_mod radicand.limb0 steps hfirst,
      hlimb0Steps]
    omega
  by_cases hsecond : steps ≤ 64
  · -- The top two limbs are zero and the second limb has at most `2 * steps - 64` bits.
    have hsplit : steps = 32 + (steps - 32) := by omega
    have hfit128 : radicand.toNat < 2 ^ 128 :=
      hfit.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have hlimb1Steps :=
      mod_place_eq_of_mul_place_le radicand.limb1.toNat radicand.toNat 32 (steps - 32)
        (by unfold place; rw [hvalue]; omega)
        (by rw [← hsplit]; exact hfit)
    rw [hsplit, digitsValue_limb1 radicand (steps - 32) (by omega),
      wordDigits_eq_mod radicand.limb1 (steps - 32) (by omega),
      wordDigits_eq_mod radicand.limb0 32 (by omega), hlimb0, hlimb1Steps]
    unfold place
    omega
  by_cases hmiddle : steps ≤ 96
  · -- The top limb is zero and the third limb has at most `2 * steps - 128` significant bits.
    have hsplit : steps = 64 + (steps - 64) := by omega
    have hlimb3 : radicand.limb3.toNat = 0 := by
      have hmod :=
        mod_place_eq_of_mul_place_le radicand.limb3.toNat radicand.toNat 96 0
          (by unfold place; rw [hvalue]; omega)
          (by unfold place; exact hfit.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
      simp only [place, Nat.mul_zero, Nat.pow_zero, Nat.mod_one] at hmod
      omega
    have hlimb2 :=
      mod_place_eq_of_mul_place_le radicand.limb2.toNat radicand.toNat 64 (steps - 64)
        (by unfold place; rw [hvalue, hlimb3]; omega)
        (by rw [← hsplit]; exact hfit)
    rw [hsplit, digitsValue_limb2 radicand (steps - 64) (by omega),
      wordDigits_eq_mod radicand.limb2 (steps - 64) (by omega),
      wordDigits_eq_mod radicand.limb1 32 (by omega),
      wordDigits_eq_mod radicand.limb0 32 (by omega), hlimb0, hlimb1, hlimb2, hvalue, hlimb3]
    simp [place]
    ring
  · -- The top limb has at most `2 * steps - 192` significant bits.
    have hsplit : steps = 96 + (steps - 96) := by omega
    have hlimb2 : radicand.limb2.toNat % place 32 = radicand.limb2.toNat := by
      apply Nat.mod_eq_of_lt
      simpa [place] using h2
    have hlimb3 :=
      mod_place_eq_of_mul_place_le radicand.limb3.toNat radicand.toNat 96 (steps - 96)
        (by unfold place; rw [hvalue]; omega)
        (by rw [← hsplit]; exact hfit)
    rw [hsplit, digitsValue_limb3 radicand (steps - 96),
      wordDigits_eq_mod radicand.limb3 (steps - 96) (by omega),
      wordDigits_eq_mod radicand.limb2 32 (by omega),
      wordDigits_eq_mod radicand.limb1 32 (by omega),
      wordDigits_eq_mod radicand.limb0 32 (by omega), hlimb0, hlimb1, hlimb2, hlimb3, hvalue]
    simp [place]
    ring

/--
The restoring kernel with `steps` digits returns the floor root and square remainder for every
radicand below `2^(2 * steps)`, for any digit count up to 125.

The upper bound keeps the remainder doubled twice inside the two-word state. The two-word
square-root kernels use `fracWidth + 1` digits.
-/
theorem rootAndRemainder_spec
    (radicand : UInt256) (steps : Nat)
    (hupper : steps ≤ 125)
    (hfit : radicand.toNat < 2 ^ (2 * steps)) :
    let state := rootAndRemainder radicand steps
    state.root.toNat = Nat.sqrt radicand.toNat ∧
      state.remainder.toNat =
        radicand.toNat -
          Nat.sqrt radicand.toNat * Nat.sqrt radicand.toNat := by
  let state := rootAndRemainder radicand steps
  have hfit250 : radicand.toNat < 2 ^ 250 :=
    lt_of_lt_of_le hfit (Nat.pow_le_pow_right (by decide) (by omega))
  have hrep : RootRep128 state radicand.toNat :=
    rootAndRemainder_rep radicand steps
      (digitsValue_eq_toNat radicand steps (by omega) hfit) hfit250
  exact RestoringRootState.sqrt_spec UInt128.toNat hrep

/-- Native nearest-root rounding agrees with the mathematical remainder boundary. -/
theorem roundRoot_toNat
    (radicand : UInt256) (steps : Nat)
    (hupper : steps ≤ 125)
    (hfit : radicand.toNat < 2 ^ (2 * steps)) :
    (roundRoot (rootAndRemainder radicand steps)).toNat =
      let root := Nat.sqrt radicand.toNat
      let remainder := radicand.toNat - root * root
      if remainder ≤ root then root else root + 1 := by
  let state := rootAndRemainder radicand steps
  change
    (roundRoot state).toNat =
      if radicand.toNat -
            Nat.sqrt radicand.toNat * Nat.sqrt radicand.toNat ≤
          Nat.sqrt radicand.toNat then
        Nat.sqrt radicand.toNat
      else
        Nat.sqrt radicand.toNat + 1
  have hspec := rootAndRemainder_spec radicand steps hupper hfit
  have hroot : state.root.toNat = Nat.sqrt radicand.toNat := hspec.1
  have hremainder :
      state.remainder.toNat =
        radicand.toNat -
          Nat.sqrt radicand.toNat * Nat.sqrt radicand.toNat :=
    hspec.2
  have hrootUpper : state.root.toNat < 2 ^ steps := by
    rw [hroot, Nat.sqrt_lt, ← pow_add, ← two_mul]
    exact hfit
  have hincrementFit : state.root.toNat + 1 < 2 ^ 128 := by
    have hcapacity : 2 ^ steps + 1 < 2 ^ 128 := by
      have := Nat.pow_le_pow_right (by decide : 0 < 2) hupper
      norm_num at this ⊢
      omega
    omega
  have hincrement :
      state.root.increment.toNat = state.root.toNat + 1 :=
    FloatLib.Numerics.FixedWord.UInt128.increment_toNat state.root hincrementFit
  by_cases hle : state.remainder.toNat ≤ state.root.toNat
  · have hnative :
        FloatLib.Numerics.FixedWord.UInt128.less state.root state.remainder = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact (Nat.not_lt_of_ge hle)
        ((FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff _ _).1 htrue)
    have hsemantic :
        radicand.toNat - Nat.sqrt radicand.toNat * Nat.sqrt radicand.toNat ≤
          Nat.sqrt radicand.toNat := by
      simpa only [hremainder, hroot] using hle
    simp only [roundRoot, hnative, Bool.false_eq_true, ite_false]
    rw [hroot]
    simp only [hsemantic, ite_true]
  · have hnative :
        FloatLib.Numerics.FixedWord.UInt128.less state.root state.remainder = true := by
      apply (FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff _ _).2
      omega
    have hsemantic :
        ¬radicand.toNat - Nat.sqrt radicand.toNat * Nat.sqrt radicand.toNat ≤
          Nat.sqrt radicand.toNat := by
      intro h
      apply hle
      simpa only [hremainder, hroot] using h
    simp only [roundRoot, hnative, ite_true]
    rw [hincrement, hroot]
    simp only [hsemantic, ite_false]

end FloatLib.Numerics.FixedWord.RestoringSquareRoot
