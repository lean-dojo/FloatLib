/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Core.Proof
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Sqrt.Runtime
public import FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic
public import FloatLib.Floats.ExecFloat.Backends.SqrtNormalRounding
public import Mathlib.Data.Nat.Sqrt
public import FloatLib.Kernels.FixedWord.CheckedSqrt.Proof

/-!
# Correctness of the native binary64 square-root kernel

The restoring two-limb kernel rebuilds its scaled radicand one base-four digit at a time, and its
state invariant shows that the final native root is `Nat.sqrt`, with the exact remainder. A checked
Newton candidate gives the same state (`rootAndRemainderChecked_eq`). A format-level theorem then
refines the native field packing to Lean's unpacked binary64 model.
-/

@[expose] public section

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic

open FloatLib.Numerics.FixedWord
open FloatLib.Numerics.FixedWord.BaseFour

/-! ## Restoring-root invariant -/

local notation "RootRep64" =>
  RestoringRootState.Represents UInt64.toNat

private theorem digit_lt_four (radicand : FloatLib.Numerics.FixedWord.UInt128) (index : Nat) :
    (digitAt radicand index).toNat < 4 := by
  unfold digitAt
  split <;> exact maskedBaseFourDigit_lt _

private theorem rootStep_spec
    (state : RestoringRootState UInt64) (digit : UInt64) (value : Nat)
    (hrep : RootRep64 state value)
    (hvalue : value < 2 ^ 106)
    (hdigit : digit.toNat < 4) :
    RootRep64 (rootStep digit state) (value * 4 + digit.toNat) := by
  unfold rootStep
  dsimp only
  have hroot :=
    RestoringRootState.root_lt_two_pow UInt64.toNat 53 hrep hvalue
  have hremainderLe :
      state.remainder.toNat ≤ 2 * state.root.toNat :=
    hrep.2
  have hremainder : state.remainder.toNat < 2 ^ 54 := by
    norm_num at hroot ⊢
    omega
  norm_num at hroot hremainder
  have hrootMulFour : (state.root * 4).toNat = state.root.toNat * 4 :=
    uint64_mul_toNat_of_lt _ _ (by simp only [UInt64.reduceToNat]; omega)
  have hrootMulTwo : (state.root * 2).toNat = state.root.toNat * 2 :=
    uint64_mul_toNat_of_lt _ _ (by simp only [UInt64.reduceToNat]; omega)
  have hremainderMulFour : (state.remainder * 4).toNat = state.remainder.toNat * 4 :=
    uint64_mul_toNat_of_lt _ _ (by simp only [UInt64.reduceToNat]; omega)
  have hexpanded :
      (state.remainder * 4 + digit).toNat = state.remainder.toNat * 4 + digit.toNat := by
    rw [uint64_add_toNat_of_lt _ _ (by rw [hremainderMulFour]; omega), hremainderMulFour]
  have htrial : (state.root * 4 + 1).toNat = state.root.toNat * 4 + 1 := by
    rw [uint64_add_toNat_of_lt _ _ (by rw [hrootMulFour, UInt64.toNat_one]; omega),
      hrootMulFour, UInt64.toNat_one]
  have hrootOdd : (state.root * 2 + 1).toNat = state.root.toNat * 2 + 1 := by
    rw [uint64_add_toNat_of_lt _ _ (by rw [hrootMulTwo, UInt64.toNat_one]; omega),
      hrootMulTwo, UInt64.toNat_one]
  by_cases hle : state.root * 4 + 1 ≤ state.remainder * 4 + digit
  · rw [ite_eq_left hle]
    have hleNat : state.root.toNat * 4 + 1 ≤
        state.remainder.toNat * 4 + digit.toNat := by
      simpa [UInt64.le_iff_toNat_le, htrial, hexpanded] using hle
    have hremainderSub :
        ((state.remainder * 4 + digit) -
          (state.root * 4 + 1)).toNat =
          state.remainder.toNat * 4 + digit.toNat -
            (state.root.toNat * 4 + 1) := by
      rw [UInt64.toNat_sub_of_le _ _ hle, hexpanded, htrial]
    have hsubAdd :
        (state.remainder.toNat * 4 + digit.toNat -
            (state.root.toNat * 4 + 1)) +
            (state.root.toNat * 4 + 1) =
          state.remainder.toNat * 4 + digit.toNat :=
      Nat.sub_add_cancel hleNat
    have hsquare :
        (state.root.toNat * 2 + 1) * (state.root.toNat * 2 + 1) =
          4 * (state.root.toNat * state.root.toNat) + 4 * state.root.toNat + 1 := by
      ring
    have hvalueEq := hrep.1
    constructor
    · rw [hrootOdd, hremainderSub]
      omega
    · rw [hrootOdd, hremainderSub]
      omega
  · rw [ite_eq_right hle]
    have hltNat :
        state.remainder.toNat * 4 + digit.toNat <
          state.root.toNat * 4 + 1 := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
      simpa [htrial, hexpanded] using this
    have hsquare :
        state.root.toNat * 2 * (state.root.toNat * 2) =
          4 * (state.root.toNat * state.root.toNat) := by
      ring
    have hvalueEq := hrep.1
    constructor
    · rw [hrootMulTwo, hexpanded]
      omega
    · rw [hrootMulTwo, hexpanded]
      omega

/-! ## Two-word radicand digits -/

private theorem shiftedRadicand_toNat
    (mantissa : UInt64) (shift : Nat)
    (hpositive : 0 < shift)
    (hshift : shift < 128)
    (hfit : mantissa.toNat <<< shift < 2 ^ 128) :
    (shiftedRadicand mantissa shift).toNat =
      mantissa.toNat <<< shift := by
  unfold shiftedRadicand FloatLib.Numerics.FixedWord.UInt128.toNat
  by_cases hsmall : shift < 64
  · rw [ite_eq_left hsmall]
    have hshiftSize : shift < 2 ^ 64 :=
      lt_trans hsmall (by norm_num)
    have hcomplement : 64 - shift < 64 := by omega
    have hcomplementSize : 64 - shift < 2 ^ 64 :=
      lt_trans hcomplement (by norm_num)
    have hlo :
        (mantissa <<< UInt64.ofNat shift).toNat =
          (mantissa.toNat <<< shift) % 2 ^ 64 := by
      rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hshiftSize, Nat.mod_eq_of_lt hsmall]
    have hhi :
        (mantissa >>> UInt64.ofNat (64 - shift)).toNat =
          mantissa.toNat / 2 ^ (64 - shift) := by
      rw [UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hcomplementSize,
        Nat.mod_eq_of_lt hcomplement, Nat.shiftRight_eq_div_pow]
    have hpow :
        2 ^ 64 = 2 ^ (64 - shift) * 2 ^ shift := by
      calc
        2 ^ 64 = 2 ^ ((64 - shift) + shift) := by
          rw [Nat.sub_add_cancel (Nat.le_of_lt hsmall)]
        _ = 2 ^ (64 - shift) * 2 ^ shift := pow_add ..
    have hquotient :
        (mantissa.toNat <<< shift) / 2 ^ 64 =
          mantissa.toNat / 2 ^ (64 - shift) := by
      rw [Nat.shiftLeft_eq, hpow]
      exact Nat.mul_div_mul_right mantissa.toNat (2 ^ (64 - shift))
        (by positivity)
    rw [hlo, hhi, ← hquotient, Nat.shiftLeft_eq]
    exact Nat.mod_add_div' (mantissa.toNat * 2 ^ shift) (2 ^ 64)
  · rw [ite_eq_right hsmall]
    have hlarge : 64 ≤ shift := Nat.le_of_not_gt hsmall
    have hinner : shift - 64 < 64 := by omega
    have hinnerSize : shift - 64 < 2 ^ 64 :=
      lt_trans hinner (by norm_num)
    have hpow :
        2 ^ shift = 2 ^ (shift - 64) * 2 ^ 64 := by
      calc
        2 ^ shift = 2 ^ ((shift - 64) + 64) := by
          rw [Nat.sub_add_cancel hlarge]
        _ = 2 ^ (shift - 64) * 2 ^ 64 := pow_add ..
    have hhighFit :
        mantissa.toNat <<< (shift - 64) < 2 ^ 64 := by
      rw [Nat.shiftLeft_eq] at hfit ⊢
      rw [hpow] at hfit
      nlinarith [show 0 < 2 ^ 64 by positivity]
    have hhi :
        (mantissa <<< UInt64.ofNat (shift - 64)).toNat =
          mantissa.toNat <<< (shift - 64) := by
      rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hinnerSize, Nat.mod_eq_of_lt hinner,
        Nat.mod_eq_of_lt hhighFit]
    rw [hhi]
    simp only [UInt64.reduceToNat, zero_add, Nat.shiftLeft_eq]
    rw [hpow]
    ring

/-! ## Restoring-loop refinement -/

private theorem digitAt_low
    (radicand : FloatLib.Numerics.FixedWord.UInt128) (index : Nat)
    (hindex : index < 32) :
    (digitAt radicand index).toNat =
      wordDigit radicand.lo index := by
  simp [digitAt, wordDigit, hindex]

private theorem digitAt_high
    (radicand : FloatLib.Numerics.FixedWord.UInt128) (index : Nat)
    (hindex : 32 ≤ index) :
    (digitAt radicand index).toNat =
      wordDigit radicand.hi (index - 32) := by
  simp [digitAt, wordDigit, Nat.not_lt.mpr hindex]

private theorem digitsValue_low
    (radicand : FloatLib.Numerics.FixedWord.UInt128) (steps : Nat)
    (hsteps : steps ≤ 32) :
    digitsValue digitAt radicand steps = wordDigits radicand.lo steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [digitsValue, wordDigits, digitAt_low radicand steps (by omega),
        ih (by omega)]

private theorem digitsValue_high
    (radicand : FloatLib.Numerics.FixedWord.UInt128) (steps : Nat)
    (hsteps : steps ≤ 32) :
    digitsValue digitAt radicand (32 + steps) =
      wordDigits radicand.hi steps * place 32 +
        wordDigits radicand.lo 32 := by
  induction steps with
  | zero =>
      change
        digitsValue digitAt radicand 32 =
          0 * place 32 + wordDigits radicand.lo 32
      rw [zero_mul, zero_add]
      exact digitsValue_low radicand 32 (by omega)
  | succ steps ih =>
      change
        (digitAt radicand (32 + steps)).toNat * place (32 + steps) +
            digitsValue digitAt radicand (32 + steps) =
          (wordDigit radicand.hi steps * place steps +
              wordDigits radicand.hi steps) * place 32 +
            wordDigits radicand.lo 32
      rw [digitAt_high radicand (32 + steps) (by omega),
        show 32 + steps - 32 = steps by omega, ih (by omega),
        place_add]
      ring

private theorem digitsValue_53_eq_toNat
    (radicand : FloatLib.Numerics.FixedWord.UInt128)
    (hfit : radicand.toNat < 2 ^ 106) :
    digitsValue digitAt radicand 53 = radicand.toNat := by
  have hhigh : radicand.hi.toNat < 2 ^ 42 := by
    unfold FloatLib.Numerics.FixedWord.UInt128.toNat at hfit
    norm_num at hfit ⊢
    nlinarith [radicand.lo.toNat.zero_le]
  rw [show 53 = 32 + 21 by omega,
    digitsValue_high radicand 21 (by omega),
    wordDigits_eq_mod radicand.hi 21 (by omega),
    wordDigits_eq_mod radicand.lo 32 (by omega)]
  have hlo : radicand.lo.toNat % place 32 = radicand.lo.toNat := by
    apply Nat.mod_eq_of_lt
    simpa [place] using radicand.lo.toNat_lt
  have hhi : radicand.hi.toNat % place 21 = radicand.hi.toNat := by
    apply Nat.mod_eq_of_lt
    simpa [place] using hhigh
  rw [hlo, hhi]
  simp [FloatLib.Numerics.FixedWord.UInt128.toNat, place, Nat.add_comm, Nat.mul_comm]

private theorem rootLoop_spec
    (radicand : FloatLib.Numerics.FixedWord.UInt128) (steps : Nat)
    (state : RestoringRootState UInt64) (value : Nat)
    (hrep : RootRep64 state value)
    (hfit :
      value * place steps + digitsValue digitAt radicand steps < 2 ^ 106) :
    RootRep64 (rootLoop radicand steps state)
      (value * place steps + digitsValue digitAt radicand steps) :=
  loop_represents UInt64.toNat digitAt rootStep rootLoop (2 ^ 106)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    digit_lt_four rootStep_spec radicand steps state value hrep hfit

private theorem rootLoop_53_spec
    (radicand : FloatLib.Numerics.FixedWord.UInt128)
    (hfit : radicand.toNat < 2 ^ 106) :
    RootRep64
      (rootLoop radicand 53 { root := 0, remainder := 0 })
      radicand.toNat := by
  have hinitial :
      RootRep64 ({ root := 0, remainder := 0 } : RestoringRootState UInt64) 0 := by
    simp [RestoringRootState.Represents]
  have hloop :=
    rootLoop_spec radicand 53 { root := 0, remainder := 0 } 0
      hinitial
  rw [zero_mul, zero_add, digitsValue_53_eq_toNat radicand hfit] at hloop
  exact hloop hfit

/-- When the shifted significand fits in 106 bits, the restoring root returns the integer square
root and its remainder. -/
theorem rootAndRemainder_spec
    (mantissa : UInt64) (shift : Nat)
    (hpositive : 0 < shift)
    (hshift : shift < 128)
    (hfit : mantissa.toNat <<< shift < 2 ^ 106) :
    let state := rootAndRemainder mantissa shift
    state.root.toNat = Nat.sqrt (mantissa.toNat <<< shift) ∧
      state.remainder.toNat =
        (mantissa.toNat <<< shift) -
          Nat.sqrt (mantissa.toNat <<< shift) *
            Nat.sqrt (mantissa.toNat <<< shift) := by
  let radicand := shiftedRadicand mantissa shift
  let state := rootLoop radicand 53 { root := 0, remainder := 0 }
  have hradicand :
      radicand.toNat = mantissa.toNat <<< shift := by
    exact shiftedRadicand_toNat mantissa shift hpositive hshift
      (lt_trans hfit (Nat.pow_lt_pow_right (by decide) (by omega)))
  have hradicandFit : radicand.toNat < 2 ^ 106 := by
    rw [hradicand]
    exact hfit
  have hrep : RootRep64 state radicand.toNat :=
    rootLoop_53_spec radicand hradicandFit
  change
    state.root.toNat = Nat.sqrt (mantissa.toNat <<< shift) ∧
      state.remainder.toNat =
        (mantissa.toNat <<< shift) -
          Nat.sqrt (mantissa.toNat <<< shift) *
            Nat.sqrt (mantissa.toNat <<< shift)
  simpa [hradicand] using
    RestoringRootState.sqrt_spec UInt64.toNat hrep

/-! ## Binary64 scaling and rounding specification -/

private theorem sqrt_target_exponent
    (leading scale : Nat) (hleading : leading < 53) :
    let inputExponent := Int.ofNat scale - 1074
    let position := leading + scale
    let rootExponent := Int.ofNat ((position + 972) / 2) - 1023
    min (inputExponent.ediv 2)
        ((FloatFormat.toModel FloatFormat.binary64).targetExponent
          ((Float.Model.totalExponent (2 ^ leading) inputExponent + 1).ediv 2)) =
      rootExponent - 52 := by
  dsimp only
  norm_num [Float.Model.Format.targetExponent, Float.Model.Format.minExponent,
    Float.Model.Format.mantissaBits, FloatFormat.toModel, FloatFormat.binary64,
    Float.Model.totalExponent, Nat.log2_two_pow]
  exact
    FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic.target_exponent
      leading scale 1074 972 1023 52
      (by omega) (by decide) (by decide)

private theorem sqrt_shift_amount
    (leading scale : Nat) :
    let inputExponent := Int.ofNat scale - 1074
    let position := leading + scale
    let rootExponent := Int.ofNat ((position + 972) / 2) - 1023
    (inputExponent - 2 * (rootExponent - 52)).toNat =
      if position % 2 = 0 then 104 - leading else 105 - leading := by
  dsimp only
  simpa using
    FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic.shift_amount_of_even_offset
      leading scale 1074 972 1023 52 (by decide) (by decide)

private def sqrtPositiveFiniteSpec (mantissa scale : Nat) : UInt64 :=
  let leading := mantissa.log2
  let position := leading + scale
  let shift := if position % 2 == 0 then 104 - leading else 105 - leading
  let scaledMantissa := mantissa <<< shift
  let root := Nat.sqrt scaledMantissa
  let remainder := scaledMantissa - root * root
  let roundedRoot := if remainder ≤ root then root else root + 1
  let carry := roundedRoot == Model.pow2 53
  let encodedExponent := (position + 972) / 2 + if carry then 1 else 0
  let roundedMantissa := if carry then Model.pow2 52 else roundedRoot
  packFieldsWord false (UInt64.ofNat encodedExponent)
    (UInt64.ofNat (roundedMantissa - Model.pow2 52))

/-! ## Checked Newton root -/

/-- On every input, the checked candidate path computes `rootAndRemainder`. -/
theorem rootAndRemainderChecked_eq (mantissa : UInt64) (shift : Nat) :
    rootAndRemainderChecked mantissa shift = rootAndRemainder mantissa shift := by
  unfold rootAndRemainderChecked
  split
  · rename_i hguard
    dsimp only
    split
    · rename_i state hstate
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hguard
      obtain ⟨⟨hpos, hlt⟩, hbits⟩ := hguard
      have hfit : mantissa.toNat <<< shift < 2 ^ 106 := by
        rcases hbits with h0 | hb
        · subst h0; simp
        · rw [FloatLib.Numerics.FixedWord.log2Word_eq_log2,
            FloatLib.Numerics.FixedWord.log2_toNat] at hb
          rw [Nat.shiftLeft_eq]
          have hm : mantissa.toNat < 2 ^ (mantissa.toNat.log2 + 1) := Nat.lt_log2_self
          calc mantissa.toNat * 2 ^ shift < 2 ^ (mantissa.toNat.log2 + 1) * 2 ^ shift :=
                Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
            _ = 2 ^ (mantissa.toNat.log2 + 1 + shift) := (pow_add 2 _ _).symm
            _ ≤ 2 ^ 106 := Nat.pow_le_pow_right (by decide) (by omega)
      have hrad := shiftedRadicand_toNat mantissa shift hpos hlt
        (lt_trans hfit (Nat.pow_lt_pow_right (by decide) (by decide)))
      obtain ⟨hroot, hrem⟩ := rootAndRemainder_spec mantissa shift hpos hlt hfit
      obtain ⟨hroot', hrem'⟩ := CheckedSquareRoot.checkRoot?_spec hstate
      rw [hrad] at hroot' hrem'
      cases hloop : rootAndRemainder mantissa shift with
      | mk root remainder =>
        rw [hloop] at hroot hrem
        cases state
        simp only at hroot hrem hroot' hrem' ⊢
        rw [UInt64.toNat_inj.mp (hroot'.trans hroot.symm),
          UInt64.toNat_inj.mp (hrem'.trans hrem.symm)]
    · rfl
  · rfl

/-! ## Native-core refinement -/

private theorem sqrtPositiveFiniteCore_eq_spec
    (mantissa scale : UInt64)
    (hmantissa : mantissa ≠ 0)
    (hmantissaBound : mantissa.toNat < 2 ^ 53)
    (hscaleBound : scale.toNat ≤ 2045) :
    sqrtPositiveFiniteCore mantissa scale =
      sqrtPositiveFiniteSpec mantissa.toNat scale.toNat := by
  unfold sqrtPositiveFiniteCore
  simp only [rootAndRemainderChecked_eq]
  simp only [FloatLib.Numerics.FixedWord.log2Word_eq_log2]
  let nativeLeading := mantissa.log2
  let nativePosition := nativeLeading + scale
  let nativeShift :=
    if nativePosition % 2 == 0 then
      104 - nativeLeading.toNat
    else
      105 - nativeLeading.toNat
  let nativeState := rootAndRemainder mantissa nativeShift
  let nativeRoot := nativeState.root
  let nativeRemainder := nativeState.remainder
  let nativeRounded :=
    if nativeRemainder ≤ nativeRoot then nativeRoot else nativeRoot + 1
  let nativeCarry := nativeRounded == 0x0020000000000000
  let nativeEncoded :=
    (nativePosition + 972) / 2 + if nativeCarry then 1 else 0
  let nativeRoundedMantissa :=
    if nativeCarry then 0x0010000000000000 else nativeRounded
  let nativeFraction := nativeRoundedMantissa - 0x0010000000000000
  let genericLeading := mantissa.toNat.log2
  let genericPosition := genericLeading + scale.toNat
  let genericShift :=
    if genericPosition % 2 == 0 then
      104 - genericLeading
    else
      105 - genericLeading
  let genericScaled := mantissa.toNat <<< genericShift
  let genericRoot := Nat.sqrt genericScaled
  let genericRemainder := genericScaled - genericRoot * genericRoot
  let genericRounded :=
    if genericRemainder ≤ genericRoot then genericRoot else genericRoot + 1
  let genericCarry := genericRounded == Model.pow2 53
  let genericEncoded :=
    (genericPosition + 972) / 2 + if genericCarry then 1 else 0
  let genericRoundedMantissa :=
    if genericCarry then Model.pow2 52 else genericRounded
  let genericFraction := genericRoundedMantissa - Model.pow2 52
  change
    packFieldsWord false nativeEncoded nativeFraction =
      packFieldsWord false (UInt64.ofNat genericEncoded)
        (UInt64.ofNat genericFraction)
  have hmantissaNat : mantissa.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hmantissa
  have hleading : nativeLeading.toNat = genericLeading := by
    dsimp only [nativeLeading, genericLeading]
    exact FloatLib.Numerics.FixedWord.log2_toNat mantissa
  have hleadingLt : genericLeading < 53 := by
    dsimp only [genericLeading]
    rw [Nat.log2_lt hmantissaNat]
    exact hmantissaBound
  have hpositionBound : genericPosition < 2 ^ 64 := by
    dsimp only [genericPosition]
    omega
  have hpositionLe : genericPosition ≤ 2097 := by
    dsimp only [genericPosition]
    omega
  have hposition : nativePosition.toNat = genericPosition := by
    dsimp only [nativePosition]
    rw [UInt64.toNat_add, hleading, Nat.mod_eq_of_lt hpositionBound]
  have hparity := mod_two_beq_zero_of_toNat_eq nativePosition genericPosition hposition
  have hshift : nativeShift = genericShift := by
    dsimp only [nativeShift, genericShift]
    rw [hparity, hleading]
  have hshiftPositive : 0 < genericShift := by
    dsimp only [genericShift]
    split <;> omega
  have hshiftLt : genericShift < 128 := by
    dsimp only [genericShift]
    split <;> omega
  obtain ⟨hscaledLower, hscaledFit, hrootLower, hrootLt⟩ :
      2 ^ 104 ≤ genericScaled ∧ genericScaled < 2 ^ 106 ∧
        2 ^ 52 ≤ genericRoot ∧ genericRoot < 2 ^ 53 :=
    sqrt_shiftLeft_bounds 52 mantissa.toNat genericShift hmantissaNat
      (by dsimp only [genericShift]; split <;> omega)
      (by dsimp only [genericShift]; split <;> omega)
  have hstate :
      nativeRoot.toNat = genericRoot ∧
        nativeRemainder.toNat = genericRemainder := by
    simpa only [nativeRoot, nativeRemainder, nativeState, genericRoot,
      genericRemainder, genericScaled, hshift] using
      rootAndRemainder_spec mantissa nativeShift
        (by simpa [hshift] using hshiftPositive)
        (by simpa [hshift] using hshiftLt)
        (by simpa [hshift] using hscaledFit)
  have hroot := hstate.1
  have hremainder := hstate.2
  have hrounded : nativeRounded.toNat = genericRounded :=
    roundedRoot_toNat nativeRoot nativeRemainder genericRoot genericRemainder hroot hremainder
      (by omega)
  have hpositionAdd :
      (nativePosition + 972).toNat = genericPosition + 972 := by
    rw [UInt64.toNat_add, hposition]
    change (genericPosition + 972) % 2 ^ 64 = genericPosition + 972
    apply Nat.mod_eq_of_lt
    omega
  have hpositionHalf :
      ((nativePosition + 972) / 2).toNat =
        (genericPosition + 972) / 2 := by
    rw [UInt64.toNat_div, hpositionAdd]
    rfl
  have hroundedLower : 2 ^ 52 ≤ genericRounded := by
    dsimp only [genericRounded]
    split <;> omega
  obtain ⟨hencoded, hfraction⟩ : nativeEncoded.toNat = _ ∧ nativeFraction.toNat = _ :=
    sqrtCarry_toNat 52 nativeRounded ((nativePosition + 972) / 2) 0x0020000000000000
      0x0010000000000000 genericRounded ((genericPosition + 972) / 2) hrounded hpositionHalf
      (by decide) (by decide) hroundedLower (by omega)
  rw [← UInt64.ofNat_toNat (x := nativeEncoded), ← UInt64.ofNat_toNat (x := nativeFraction),
    hencoded, hfraction]
  simp only [genericEncoded, genericFraction, genericRoundedMantissa, genericCarry, beq_iff_eq]

/-! ## Unpacked binary64 semantic refinement -/

/-- On every positive finite binary64 value, including subnormals, the native square root agrees
with the unpacked model after packing. -/
theorem sqrt_eq_generic_of_positive_finite
    (x : Value)
    (hexponent :
      Model.expField x ≠ FloatFormat.expAllOnesNat FloatFormat.binary64)
    (hnonzero : Model.isZero x = false)
    (hsign : Model.signBit x = false) :
    ofUInt64
        (sqrtPositiveFinite
          (expField (toUInt64 x))
          (fracField (toUInt64 x))) =
      Model.ofModel FloatFormat.binary64 (
        Float.Model.UnpackedFloat.sqrt
          (FloatFormat.toModel FloatFormat.binary64)
          (Model.toModel x)) := by
  let bits := toUInt64 x
  let exponent := expField bits
  let fraction := fracField bits
  let mantissa := finiteMantissa exponent fraction
  let scale := finiteScale exponent
  have hfraction : fraction.toNat < 2 ^ 52 := by
    simpa only [fraction, bits] using fracField_lt x
  have hexponentNative : exponent ≠ 0x7ff := by
    intro h
    apply hexponent
    rw [← expField_toNat x]
    simp only [bits, exponent, h]
    decide
  have hmantissa : mantissa ≠ 0 := by
    intro h
    have hmantissaNat : mantissa.toNat = 0 := congrArg UInt64.toNat h
    rw [finiteMantissa_toNat exponent fraction hfraction] at hmantissaNat
    by_cases hexponentZero : exponent = 0
    · simp only [hexponentZero, ite_true] at hmantissaNat
      have hfractionZero : fraction = 0 := by
        apply UInt64.toNat_inj.mp
        simpa using hmantissaNat
      have hzero : Model.isZero x = true := by
        change Model.IEEE.isZero x = true
        unfold Model.IEEE.isZero
        rw [Bool.and_eq_true]
        constructor
        · apply beq_iff_eq.mpr
          rw [← expField_toNat x]
          simp [bits, exponent, hexponentZero]
        · apply beq_iff_eq.mpr
          rw [← fracField_toNat x]
          simp [bits, fraction, hfractionZero]
      rw [hzero] at hnonzero
      contradiction
    · simp only [hexponentZero, ite_false] at hmantissaNat
      simp [Model.pow2_eq_two_pow] at hmantissaNat
  have hsignNative : signBit bits = false := by
    simpa only [bits, signBit_eq] using hsign
  have hmantissaNat : mantissa.toNat ≠ 0 := by
    intro h
    apply hmantissa
    apply UInt64.toNat_inj.mp
    simpa using h
  have hscale :
      FiniteKernel.scale exponent.toNat = scale.toNat :=
    (FiniteKernel.finiteScale_toNat_eq_scale exponent).symm
  have hdecode :
      Model.toDyadic? x =
        some
          ({ negative := false
             significand := mantissa.toNat
             exponent := Int.ofNat scale.toNat - 1074 } : Numerics.Dyadic) := by
    rw [FiniteKernel.toDyadic_eq_decode, ← decode_eq]
    unfold decode?
    simp only [bits, exponent, hexponentNative, beq_iff_eq,
      ite_false, hsignNative]
    change
      (some ({
        sign := false
        exponent := exponent.toNat
        mantissa := mantissa.toNat } : FiniteKernel.Components)).map
          (FiniteKernel.Components.toDyadic FloatFormat.binary64) =
        some
          ({ negative := false
             significand := mantissa.toNat
             exponent := Int.ofNat scale.toNat - 1074 } : Numerics.Dyadic)
    simp only [Option.map_some, FiniteKernel.Components.toDyadic,
      hmantissaNat, beq_iff_eq, ite_false]
    rw [FiniteKernel.exponent_eq_scale, hscale]
    rw [show FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 by
      decide]
    norm_num
  rw [Model.toModel_eq_finite_positive_of_toDyadic?_eq_some (by decide) x _ _ hmantissaNat
    hdecode]
  have hmantissaBound : mantissa.toNat < 2 ^ 53 :=
    finiteMantissa_lt exponent fraction hfraction
  have hexponentLt : exponent.toNat < 2 ^ 11 := by
    change Model.expField x < 2 ^ 11
    simpa only [show FloatFormat.binary64.expWidth = 11 by decide] using
      Model.expField_lt_pow2 x
  have hscaleBound : scale.toNat ≤ 2045 :=
    finiteScale_le exponent hexponentLt hexponentNative
  have hleading : mantissa.toNat.log2 < 53 := by
    rw [Nat.log2_lt hmantissaNat]
    exact hmantissaBound
  have hfracWidth : FloatFormat.binary64.fracWidth = 52 := by decide
  have hbias : FloatFormat.binary64.bias = 1023 := by decide
  rw [Model.ofModel_sqrt_finite_positive_eq_ofFields FloatFormat.binary64 mantissa.toNat
    (if (mantissa.toNat.log2 + scale.toNat) % 2 = 0 then 104 - mantissa.toNat.log2
      else 105 - mantissa.toNat.log2)
    ((mantissa.toNat.log2 + scale.toNat + 972) / 2) (Int.ofNat scale.toNat - 1074)
    (Nat.pos_of_ne_zero hmantissaNat)
    (by rw [hfracWidth]; split <;> omega) (by rw [hfracWidth]; split <;> omega)
    (by omega) (by rw [hbias]; omega)
    (by simpa only [hfracWidth, hbias, Float.Model.totalExponent, Nat.log2_two_pow,
      Int.ofNat_eq_natCast, Nat.cast_ofNat] using
        sqrt_target_exponent mantissa.toNat.log2 scale.toNat hleading)
    (by simpa only [hfracWidth, hbias, Int.ofNat_eq_natCast, Nat.cast_ofNat] using
      sqrt_shift_amount mantissa.toNat.log2 scale.toNat)]
  change ofUInt64 (sqrtPositiveFiniteCore mantissa scale) = _
  rw [sqrtPositiveFiniteCore_eq_spec mantissa scale hmantissa hmantissaBound hscaleBound]
  simp only [sqrtPositiveFiniteSpec, beq_iff_eq, packFieldsWord_eq_ofNat, hfracWidth]

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
