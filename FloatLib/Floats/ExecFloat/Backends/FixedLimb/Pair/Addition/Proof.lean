/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Addition.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.ScaleAdd.Runtime
import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Proof
import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Multiplication.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Add.Proof
import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
import FloatLib.Floats.ExecFloat.Backends.Generic.ScaleAdd.Proof
import FloatLib.Floats.Formats.BinaryInterchange.ModelRounding.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core
import FloatLib.Kernels.FixedWord.LimbRound.Proof
import FloatLib.Kernels.FixedWord.Difference.Proof
import FloatLib.Numerics.ShiftRightJam.Proof
import Mathlib.Tactic.NormNum

/-!
# Correctness of two-word finite addition

Under `Eligible`, every accepted result of `Addition.Runtime` is the exact finite kernel's answer.
The proof follows the one-word addition proof `NativeSmallWordAdd`: the two-word rounder computes
the natural-number normal specification `NativeSmallWordAdd.normalSpec?`, the aligned and sticky
combinations match `FiniteScaleAdd.roundMagnitudes`, and the decoded storage fields are those of
`FiniteKernel.decode?`. The natural-number lemmas about sticky alignment are shared with the
one-word kernel.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

open FloatLib.Numerics.FixedWord

variable {fmt : FloatFormat}

/-! ## Constants -/

/-- `alignOffset` equals `FiniteKernel.finiteScaleOffset` as a natural number. -/
theorem alignOffset_toNat (h : Eligible fmt) :
    (alignOffset fmt).toNat = FiniteKernel.finiteScaleOffset fmt := by
  have hbias := h.bias_lt
  have hfracLe := h.frac_le
  unfold alignOffset FiniteKernel.finiteScaleOffset
  rw [h.exponentBias_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
  norm_num at hbias ⊢
  omega

private theorem finiteScaleOffset_lt (h : Eligible fmt) :
    FiniteKernel.finiteScaleOffset fmt < 2 ^ 62 := by
  have hbias := h.bias_lt
  have hfracLe := h.frac_le
  unfold FiniteKernel.finiteScaleOffset
  rw [h.exponentBias_eq]
  norm_num at hbias ⊢
  omega

/-- `shiftLimit` equals `126 - fracWidth` as a natural number. -/
theorem shiftLimit_toNat (h : Eligible fmt) :
    (shiftLimit fmt).toNat = 126 - fmt.fracWidth := by
  have hfracLe := h.frac_le
  have hfrac := fracWidth_toNat h
  unfold shiftLimit
  rw [UInt64.toNat_sub_of_le, hfrac]
  · rfl
  · apply UInt64.le_iff_toNat_le.mpr
    rw [hfrac]
    change fmt.fracWidth ≤ 126
    omega

/-! ## Rounding -/

/-- Carry normalization, overflow, and packing agree with the generic rounder's normal branch. -/
theorem finishWords_eq (h : Eligible fmt) (sign : Bool) (position : UInt64)
    (rounded : UInt128) (positionNat roundedNat : Nat)
    (hposition : position.toNat = positionNat)
    (hpositionAdd : (position + 1).toNat = positionNat + 1)
    (hrounded : rounded.toNat = roundedNat)
    (hnormal : fmt.bias + 2 * fmt.fracWidth - 1 ≤ positionNat)
    (hroundedLower : 2 ^ fmt.fracWidth ≤ roundedNat)
    (hroundedUpper : roundedNat ≤ 2 ^ (fmt.fracWidth + 1)) :
    (finishWords? fmt sign position rounded).map (ofWords fmt) =
      (let carry := roundedNat = pow2 (fmt.fracWidth + 1)
       let normalizedPosition := if carry then positionNat + 1 else positionNat
       if 3 * fmt.bias + 2 * fmt.fracWidth - 2 < normalizedPosition then
         none
       else
         let normalizedMantissa := if carry then pow2 fmt.fracWidth else roundedNat
         some <| ofFields fmt sign
           (normalizedPosition - (fmt.bias + 2 * fmt.fracWidth - 2))
           (normalizedMantissa - pow2 fmt.fracWidth)) := by
  have hbias := h.bias_lt
  have hfracLe := h.frac_le
  have hoverflowWord := overflowThreshold_toNat h
  have hoffsetWord := exponentOffset_toNat h
  have hcarry := isCarry_iff h rounded
  rw [hrounded] at hcarry
  unfold finishWords?
  dsimp only
  -- Both sides branch on the same carry, so the normalized positions agree.
  have hnormalized :
      (if isCarry fmt rounded = true then position + 1 else position).toNat =
        if roundedNat = pow2 (fmt.fracWidth + 1) then positionNat + 1 else positionNat := by
    by_cases hc : roundedNat = pow2 (fmt.fracWidth + 1)
    · rw [ite_eq_left (hcarry.mpr hc), ite_eq_left hc, hpositionAdd]
    · rw [ite_eq_right (fun hk => hc (hcarry.mp hk)), ite_eq_right hc, hposition]
  set normalizedPosition := if isCarry fmt rounded = true then position + 1 else position
    with hnormalizedDef
  set normalizedNat :=
    if roundedNat = pow2 (fmt.fracWidth + 1) then positionNat + 1 else positionNat
    with hnormalizedNatDef
  have hoverflowIff :
      UInt64.ofNat (3 * fmt.bias + 2 * fmt.fracWidth - 2) < normalizedPosition ↔
        3 * fmt.bias + 2 * fmt.fracWidth - 2 < normalizedNat := by
    rw [UInt64.lt_iff_toNat_lt, hoverflowWord, hnormalized]
  by_cases hoverflow : 3 * fmt.bias + 2 * fmt.fracWidth - 2 < normalizedNat
  · rw [ite_eq_left (hoverflowIff.mpr hoverflow), ite_eq_left hoverflow]
    rfl
  rw [ite_eq_right (fun hk => hoverflow (hoverflowIff.mp hk)), ite_eq_right hoverflow,
    Option.map_some]
  congr 1
  have hnormalizedLower : fmt.bias + 2 * fmt.fracWidth - 2 ≤ normalizedNat := by
    rw [hnormalizedNatDef]
    split <;> omega
  have hexponentLe :
      UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2) ≤ normalizedPosition := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hoffsetWord, hnormalized]
    exact hnormalizedLower
  have hexponentNat :
      (normalizedPosition - UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2)).toNat =
        normalizedNat - (fmt.bias + 2 * fmt.fracWidth - 2) := by
    rw [UInt64.toNat_sub_of_le _ _ hexponentLe, hoffsetWord, hnormalized]
  have hexponentBound :
      (normalizedPosition - UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2)).toNat <
        2 ^ fmt.expWidth := by
    rw [hexponentNat, fmt.two_pow_expWidth_eq_two_mul_bias_add_two]
    omega
  have hmantissa :
      (normalizeCarry fmt (isCarry fmt rounded) rounded).toNat =
        if roundedNat = pow2 (fmt.fracWidth + 1) then pow2 fmt.fracWidth else roundedNat := by
    rw [normalizeCarry_toNat h]
    by_cases hc : roundedNat = pow2 (fmt.fracWidth + 1)
    · rw [ite_eq_left (hcarry.mpr hc), ite_eq_left hc]
    · rw [ite_eq_right (fun hk => hc (hcarry.mp hk)), ite_eq_right hc, hrounded]
  have hmantissaLower :
      2 ^ fmt.fracWidth ≤ (normalizeCarry fmt (isCarry fmt rounded) rounded).toNat := by
    rw [hmantissa]
    split
    · simp [pow2_eq_two_pow]
    · exact hroundedLower
  have hmantissaUpper :
      (normalizeCarry fmt (isCarry fmt rounded) rounded).toNat < 2 ^ (fmt.fracWidth + 1) := by
    rw [hmantissa]
    split
    · rw [pow2_eq_two_pow]
      exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
    · rename_i hc
      rw [pow2_eq_two_pow] at hc
      exact lt_of_le_of_ne hroundedUpper hc
  change packNormal fmt sign _ _ = _
  rw [packNormal_eq_ofFields h sign _ _ hexponentBound hmantissaLower hmantissaUpper,
    hexponentNat, hmantissa]

private theorem rounded_toNat (h : Eligible fmt) (magnitude : UInt128)
    (hmagnitude : magnitude.toNat ≠ 0) :
    (if UInt64.ofNat fmt.fracWidth < UInt64.ofNat magnitude.log2 then
        magnitude.roundShiftRightEven128
          (UInt64.ofNat magnitude.log2 - UInt64.ofNat fmt.fracWidth).toNat
      else
        magnitude.shiftLeft
          (UInt64.ofNat fmt.fracWidth - UInt64.ofNat magnitude.log2).toNat).toNat =
      roundMantissaToLeadingBitEven magnitude.toNat fmt.fracWidth := by
  have hfrac := h.frac_gt
  have hfracLe := h.frac_le
  have hfracWord := fracWidth_toNat h
  have hlogLt : magnitude.toNat.log2 < 128 :=
    (Nat.log2_lt hmagnitude).2 magnitude.toNat_lt
  have hleading : (UInt64.ofNat magnitude.log2).toNat = magnitude.toNat.log2 := by
    rw [UInt128.log2_toNat, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  unfold roundMantissaToLeadingBitEven
  by_cases hlt : fmt.fracWidth < magnitude.toNat.log2
  · have hltWord : UInt64.ofNat fmt.fracWidth < UInt64.ofNat magnitude.log2 := by
      rw [UInt64.lt_iff_toNat_lt, hfracWord, hleading]
      exact hlt
    have hleWord := UInt64.le_of_lt hltWord
    rw [ite_eq_left hltWord, ite_eq_left hlt.le, UInt64.toNat_sub_of_le _ _ hleWord, hleading,
      hfracWord]
    exact UInt128.roundShiftRightEven128_toNat _ _ (by omega) (by omega)
  · have hltWord : ¬UInt64.ofNat fmt.fracWidth < UInt64.ofNat magnitude.log2 := by
      rw [UInt64.lt_iff_toNat_lt, hfracWord, hleading]
      exact hlt
    have hleWord : UInt64.ofNat magnitude.log2 ≤ UInt64.ofNat fmt.fracWidth := by
      rw [UInt64.le_iff_toNat_le, hfracWord, hleading]
      omega
    rw [ite_eq_right hltWord, UInt64.toNat_sub_of_le _ _ hleWord, hleading, hfracWord]
    have hfit : magnitude.toNat <<< (fmt.fracWidth - magnitude.toNat.log2) < 2 ^ 128 := by
      have hshifted :=
        Nat.shiftLeft_lt (m := fmt.fracWidth - magnitude.toNat.log2)
          (Nat.lt_log2_self (n := magnitude.toNat))
      rw [show magnitude.toNat.log2 + 1 + (fmt.fracWidth - magnitude.toNat.log2) =
        fmt.fracWidth + 1 by omega] at hshifted
      exact hshifted.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    rw [UInt128.shiftLeft_toNat _ _ (by omega) hfit]
    by_cases heq : fmt.fracWidth = magnitude.toNat.log2
    · rw [ite_eq_left heq.le, heq, Nat.sub_self, Numerics.roundShiftRightEven_zero,
        Nat.shiftLeft_zero]
    · rw [ite_eq_right (by omega)]

/--
The two-word rounder computes the natural-number normal specification of the one-word kernel.
-/
theorem roundMagnitudeWords_eq_normalSpec (h : Eligible fmt) (offset : UInt64) (sign : Bool)
    (magnitude : UInt128) (scale : UInt64) (hmagnitude : magnitude.toNat ≠ 0)
    (hscale : scale.toNat + offset.toNat < 2 ^ 63) :
    (roundMagnitudeWords? fmt offset sign magnitude scale).map (ofWords fmt) =
      NativeSmallWordAdd.normalSpec? fmt sign magnitude.toNat (scale.toNat + offset.toNat) := by
  have hbias := h.bias_lt
  have hfracLe := h.frac_le
  have hnormalWord := normalThreshold_toNat h
  have hlogLt : magnitude.toNat.log2 < 128 :=
    (Nat.log2_lt hmagnitude).2 magnitude.toNat_lt
  have hleading : (UInt64.ofNat magnitude.log2).toNat = magnitude.toNat.log2 := by
    rw [UInt128.log2_toNat, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  let positionNat := magnitude.toNat.log2 + (scale.toNat + offset.toNat)
  have hposition :
      (UInt64.ofNat magnitude.log2 + scale + offset).toNat = positionNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add, hleading,
      Nat.mod_eq_of_lt (by norm_num at hscale ⊢; omega),
      Nat.mod_eq_of_lt (by norm_num at hscale ⊢; omega)]
    omega
  have hpositionAdd :
      (UInt64.ofNat magnitude.log2 + scale + offset + 1).toNat = positionNat + 1 := by
    rw [UInt64.toNat_add, hposition, UInt64.toNat_one, Nat.mod_eq_of_lt]
    norm_num at hscale ⊢
    omega
  unfold roundMagnitudeWords? NativeSmallWordAdd.normalSpec?
  dsimp only
  rw [show magnitude.toNat.log2 + (scale.toNat + offset.toNat) = positionNat by rfl]
  by_cases hsubnormal : positionNat < fmt.bias + 2 * fmt.fracWidth - 1
  · have hsubnormalWord :
        UInt64.ofNat magnitude.log2 + scale + offset <
          UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 1) := by
      rw [UInt64.lt_iff_toNat_lt, hposition, hnormalWord]
      exact hsubnormal
    rw [ite_eq_left hsubnormalWord, ite_eq_left hsubnormal]
    rfl
  have hsubnormalWord :
      ¬UInt64.ofNat magnitude.log2 + scale + offset <
        UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 1) := by
    rw [UInt64.lt_iff_toNat_lt, hposition, hnormalWord]
    exact hsubnormal
  rw [ite_eq_right hsubnormalWord, ite_eq_right hsubnormal]
  have hrounded := rounded_toNat h magnitude hmagnitude
  have hroundedLower :=
    pow2_le_roundMantissaToLeadingBitEven magnitude.toNat fmt.fracWidth hmagnitude
  have hroundedUpper := roundMantissaToLeadingBitEven_le_pow2_succ magnitude.toNat fmt.fracWidth
  rw [pow2_eq_two_pow] at hroundedLower hroundedUpper
  rw [finishWords_eq h sign _ _ positionNat _ hposition hpositionAdd hrounded (by omega)
    hroundedLower hroundedUpper]
  rfl

/-- An accepted two-word rounding is the unsigned-scale rounding of the exact kernel. -/
theorem roundMagnitudeWords_refines (h : Eligible fmt) (offset : UInt64) (sign : Bool)
    (magnitude : UInt128) (scale : UInt64) (hmagnitude : magnitude.toNat ≠ 0)
    (hscale : scale.toNat + offset.toNat < 2 ^ 63)
    (words : UInt128)
    (hresult : roundMagnitudeWords? fmt offset sign magnitude scale = some words) :
    ofWords fmt words =
      FiniteScaleAdd.roundMagnitude fmt offset.toNat sign magnitude.toNat scale.toNat := by
  have hmap := roundMagnitudeWords_eq_normalSpec h offset sign magnitude scale hmagnitude hscale
  rw [hresult, Option.map_some] at hmap
  unfold FiniteScaleAdd.roundMagnitude
  exact NativeSmallWordAdd.normalSpec_refines fmt sign _ _ hmagnitude _ hmap.symm

/-! ## Signed magnitudes -/

private theorem model_eq_of_toNatBits {x y : Model fmt} (h : x.toNatBits = y.toNatBits) :
    x = y := by
  rw [← ofNatBits_toNatBits x, ← ofNatBits_toNatBits y, h]

/-- All-zero storage words are positive zero. -/
theorem ofWords_zero : ofWords fmt ⟨0, 0⟩ = zero fmt false := by
  apply model_eq_of_toNatBits
  rw [ofWords_toNat _ (by simp [UInt128.toNat])]
  simp [zero, posZero, UInt128.toNat]

/-- An accepted aligned combination is the exact kernel's signed-magnitude combination. -/
theorem roundAlignedWords_refines (h : Eligible fmt) (offset : UInt64) (leftSign rightSign : Bool)
    (left right : UInt128) (scale : UInt64)
    (hright : right.toNat ≠ 0)
    (hsum : left.toNat + right.toNat < 2 ^ 128) (hscale : scale.toNat + offset.toNat < 2 ^ 63)
    (words : UInt128)
    (hresult : roundAlignedWords? fmt offset leftSign rightSign left right scale = some words) :
    ofWords fmt words =
      FiniteScaleAdd.roundMagnitudes fmt offset.toNat
        leftSign rightSign left.toNat right.toNat scale.toNat := by
  unfold roundAlignedWords? at hresult
  unfold FiniteScaleAdd.roundMagnitudes
  by_cases hsign : leftSign = rightSign
  · rw [ite_eq_left (by simp [hsign])] at hresult
    rw [ite_eq_left (by simp [hsign])]
    have hadd := add128_value_toNat_of_lt left right hsum
    rw [roundMagnitudeWords_refines h offset leftSign _ scale (by rw [hadd]; omega) hscale words
      hresult, hadd]
  · rw [ite_eq_right (by simpa using hsign)] at hresult
    rw [ite_eq_right (by simpa using hsign)]
    by_cases heq : left = right
    · subst heq
      simp only [beq_self_eq_true, ite_true, Option.some.injEq] at hresult
      simp only [beq_self_eq_true, ite_true]
      subst hresult
      have hand : (leftSign && rightSign) = false := by
        cases leftSign <;> cases rightSign <;> simp_all
      rw [hand, ofWords_zero]
    · have heqNat : left.toNat ≠ right.toNat := fun hnat => heq (UInt128.toNat_injective hnat)
      rw [ite_eq_right (by simpa using heq)] at hresult
      rw [ite_eq_right (by simpa using heqNat)]
      by_cases hlt : left.toNat < right.toNat
      · have hless : left.less right = true := (UInt128.less_eq_true_iff _ _).mpr hlt
        rw [ite_eq_left hless] at hresult
        rw [ite_eq_left hlt]
        have hsub := UInt128.sub_toNat right left hlt.le
        rw [roundMagnitudeWords_refines h offset rightSign _ scale (by rw [hsub]; omega) hscale
          words hresult, hsub]
      · have hless : ¬left.less right = true :=
          fun hk => hlt ((UInt128.less_eq_true_iff _ _).mp hk)
        rw [ite_eq_right hless] at hresult
        rw [ite_eq_right hlt]
        have hsub := UInt128.sub_toNat left right (by omega)
        rw [roundMagnitudeWords_refines h offset leftSign _ scale (by rw [hsub]; omega) hscale words
          hresult, hsub]

/-! ## Sticky alignment -/

private theorem jammedMagnitudeWords_toNat (sameSign : Bool) (high low : UInt128) (gap : UInt64)
    (hhigh : high.toNat < 2 ^ 124) (hlowLt : low.toNat < high.toNat * 2 ^ gap.toNat)
    (hlowNe : low.toNat ≠ 0) (hgap : 3 ≤ gap.toNat) :
    (jammedMagnitudeWords sameSign high low gap).toNat =
      Numerics.shiftRightJam
        (if sameSign then high.toNat * 2 ^ gap.toNat + low.toNat
          else high.toNat * 2 ^ gap.toNat - low.toNat)
        (gap.toNat - 3) := by
  have hdiscard : (gap - 3).toNat = gap.toNat - 3 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hgap))
  set d := gap.toNat - 3 with hd
  have hlowerNat : (low.shiftRight (gap - 3).toNat).toNat = low.toNat / 2 ^ d := by
    rw [UInt128.shiftRight_toNat, hdiscard]
  have hexact :
      ((low.shiftRight (gap - 3).toNat).shiftLeft (gap - 3).toNat == low) =
        decide (low.toNat % 2 ^ d = 0) := by
    rw [hdiscard]
    exact UInt128.shiftRight_shiftLeft_beq low d hlowNe
  have hupper : (high.shiftLeft 3).toNat = high.toNat * 2 ^ 3 := by
    rw [UInt128.shiftLeft_toNat _ _ (by decide) (by rw [Nat.shiftLeft_eq]; omega),
      Nat.shiftLeft_eq]
  have hgapSplit : high.toNat * 2 ^ gap.toNat = high.toNat * 2 ^ 3 * 2 ^ d := by
    rw [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  have hlowSplit : low.toNat < high.toNat * 2 ^ 3 * 2 ^ d := by
    rw [← hgapSplit]
    exact hlowLt
  have hquot : low.toNat / 2 ^ d < high.toNat * 2 ^ 3 :=
    Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hlowSplit)
  unfold jammedMagnitudeWords UInt128.jamCombine
  simp only [hexact]
  rw [hgapSplit]
  cases sameSign
  · simp only [Bool.false_eq_true, ite_false]
    rw [Numerics.shiftRightJam_mul_two_pow_sub _ _ _ hlowSplit.le]
    have hordered : (low.shiftRight (gap - 3).toNat).toNat ≤ (high.shiftLeft 3).toNat := by
      rw [hlowerNat, hupper]
      omega
    have hsub := UInt128.sub_toNat _ _ hordered
    rw [hlowerNat, hupper] at hsub
    by_cases hz : low.toNat % 2 ^ d = 0
    · simp only [hz, decide_true, ite_true]
      exact hsub
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      have hunit : (⟨0, 1⟩ : UInt128).toNat = 1 := by simp [UInt128.toNat]
      have hone :
          (⟨0, 1⟩ : UInt128).toNat ≤
            ((high.shiftLeft 3).sub (low.shiftRight (gap - 3).toNat)).toNat := by
        rw [hsub, hunit]
        omega
      rw [UInt128.setLowBit_toNat, UInt128.sub_toNat _ _ hone, hsub, hunit]
  · simp only [ite_true]
    rw [Numerics.shiftRightJam_add_mul_two_pow]
    have hsum :
        (add128 (high.shiftLeft 3) (low.shiftRight (gap - 3).toNat)).value.toNat =
          high.toNat * 2 ^ 3 + low.toNat / 2 ^ d := by
      rw [add128_value_toNat_of_lt _ _ (by rw [hupper, hlowerNat]; omega), hupper, hlowerNat]
    by_cases hz : low.toNat % 2 ^ d = 0
    · simp only [hz, decide_true, ite_true]
      exact hsum
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      rw [UInt128.setLowBit_toNat, hsum]

/-- An accepted sticky alignment is the exact signed-magnitude combination of the same fields. -/
theorem roundJammedWords_refines (h : Eligible fmt) (offset : UInt64) (highSign lowSign : Bool)
    (high low : UInt128) (gap scale : UInt64)
    (hlow : low.toNat ≤ 2 ^ (fmt.fracWidth + gap.toNat - 1)) (hlowNe : low.toNat ≠ 0)
    (hscale : scale.toNat + gap.toNat + offset.toNat < 2 ^ 63)
    (words : UInt128)
    (hresult : roundJammedWords? fmt offset highSign lowSign high low gap scale = some words) :
    ofWords fmt words =
      FiniteScaleAdd.roundMagnitudes fmt offset.toNat
        highSign lowSign (high.toNat <<< gap.toNat) low.toNat scale.toNat := by
  have hfrac := h.frac_gt
  unfold roundJammedWords? at hresult
  split at hresult
  · rename_i hguard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hguard
    obtain ⟨⟨himplicit, hhighWord⟩, hgap⟩ := hguard
    have hhighLower : 2 ^ fmt.fracWidth ≤ high.toNat := by
      have hnat := UInt64.le_iff_toNat_le.mp himplicit
      rw [implicitBit_toNat h] at hnat
      have hsplit : 2 ^ fmt.fracWidth = 2 ^ (fmt.fracWidth - 64) * 2 ^ 64 := by
        rw [← Nat.pow_add]
        congr 1
        omega
      unfold UInt128.toNat
      rw [hsplit]
      exact (Nat.mul_le_mul_right _ hnat).trans (Nat.le_add_left _ _)
    have hhigh : high.toNat < 2 ^ 124 := by
      have hnat := UInt64.lt_iff_toNat_lt.mp hhighWord
      have hlo := high.lo.toNat_lt
      unfold UInt128.toNat
      norm_num at hnat hlo ⊢
      omega
    have hgapNat : 3 ≤ gap.toNat := by simpa using UInt64.le_iff_toNat_le.mp hgap
    have hbelow := NativeSmallWordAdd.alignedMagnitude_lower fmt.fracWidth high.toNat low.toNat
      gap.toNat false hhighLower hlow hgapNat
    have hlowLt : low.toNat < high.toNat * 2 ^ gap.toNat := by
      simp only [Bool.false_eq_true, ite_false] at hbelow
      have hpos : 0 < 2 ^ (fmt.fracWidth + gap.toNat - 1) := Nat.two_pow_pos _
      omega
    have hmag := jammedMagnitudeWords_toNat (highSign == lowSign) high low gap hhigh hlowLt
      hlowNe hgapNat
    have hdiscard : (gap - 3).toNat = gap.toNat - 3 :=
      UInt64.toNat_sub_of_le _ _ hgap
    have hscaleSum : (scale + (gap - 3)).toNat = scale.toNat + (gap.toNat - 3) := by
      rw [UInt64.toNat_add, hdiscard]
      exact Nat.mod_eq_of_lt (by omega)
    have hmagNe : (jammedMagnitudeWords (highSign == lowSign) high low gap).toNat ≠ 0 := by
      rw [hmag]
      refine Numerics.shiftRightJam_ne_zero _ _ ?_
      exact (Nat.pow_le_pow_right (by decide) (by omega)).trans
        (NativeSmallWordAdd.alignedMagnitude_lower fmt.fracWidth high.toNat low.toNat
          gap.toNat _ hhighLower hlow hgapNat)
    rw [roundMagnitudeWords_refines h offset highSign _ _ hmagNe (by rw [hscaleSum]; omega) words
      hresult, hmag, hscaleSum]
    exact FiniteScaleAdd.roundMagnitude_shiftRightJam fmt _ highSign lowSign high.toNat low.toNat
      gap.toNat scale.toNat hhighLower hlow hgapNat
  · simp at hresult

/-! ## Field addition -/

private theorem toNat_ne_zero_of_ne {value : UInt128} (h : value ≠ ⟨0, 0⟩) : value.toNat ≠ 0 :=
  fun hzero => h (UInt128.toNat_injective (by rw [hzero]; unfold UInt128.toNat; rfl))

private theorem scale_lt (h : Eligible fmt) (exponent : UInt64)
    (hexponent : exponent.toNat < 2 ^ fmt.expWidth) :
    (finiteScale exponent).toNat < 2 ^ 62 := by
  have hpow : 2 ^ fmt.expWidth ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) h.exp_le
  rw [NativeSmallWordAdd.finiteScale_toNat_eq_scale]
  unfold FiniteKernel.scale
  split <;> omega

private theorem shiftedMantissa_toNat (h : Eligible fmt) (mantissa : UInt128) (shift : UInt64)
    (hmantissa : mantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hshift : shift.toNat + fmt.fracWidth ≤ 126) :
    (mantissa.shiftLeft shift.toNat).toNat = mantissa.toNat <<< shift.toNat ∧
      mantissa.toNat <<< shift.toNat < 2 ^ 127 := by
  have hfit : mantissa.toNat <<< shift.toNat < 2 ^ 127 := by
    have hshifted := Nat.shiftLeft_lt (m := shift.toNat) hmantissa
    exact hshifted.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  exact ⟨UInt128.shiftLeft_toNat _ _ (by have := h.frac_gt; omega) (hfit.trans (by norm_num)),
    hfit⟩

private theorem shiftedMantissa_ne_zero (mantissa : UInt128) (shift : Nat)
    (hmantissa : mantissa.toNat ≠ 0)
    (hshifted : (mantissa.shiftLeft shift).toNat = mantissa.toNat <<< shift) :
    (mantissa.shiftLeft shift).toNat ≠ 0 := by
  rw [hshifted, Nat.shiftLeft_eq]
  exact Nat.mul_ne_zero hmantissa (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))

/-- An accepted two-word field addition is the exact unsigned-scale sum of the same fields. -/
theorem addFieldsWords_refines (h : Eligible fmt)
    (xSign : Bool) (xExponent : UInt64) (xMantissa : UInt128)
    (ySign : Bool) (yExponent : UInt64) (yMantissa : UInt128)
    (hxExponent : xExponent.toNat < 2 ^ fmt.expWidth)
    (hyExponent : yExponent.toNat < 2 ^ fmt.expWidth)
    (hxMantissa : xMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hyMantissa : yMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (words : UInt128)
    (hresult :
      addFieldsWords? fmt xSign xExponent xMantissa ySign yExponent yMantissa = some words) :
    ofWords fmt words =
      FiniteKernel.addFields fmt
        xSign xExponent.toNat xMantissa.toNat ySign yExponent.toNat yMantissa.toNat := by
  have hfracLe := h.frac_le
  have hlimit := shiftLimit_toNat h
  have hpow127 : 2 ^ (fmt.fracWidth + 1) ≤ 2 ^ 127 := Nat.pow_le_pow_right (by decide) (by omega)
  unfold addFieldsWords? at hresult
  by_cases hzero : (xMantissa == ⟨0, 0⟩ || yMantissa == ⟨0, 0⟩) = true
  · simp [hzero] at hresult
  rw [ite_eq_right hzero] at hresult
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hzero
  obtain ⟨hxNe, hyNe⟩ := hzero
  have hxNeNat := toNat_ne_zero_of_ne hxNe
  have hyNeNat := toNat_ne_zero_of_ne hyNe
  have hxScale := NativeSmallWordAdd.finiteScale_toNat_eq_scale xExponent
  have hyScale := NativeSmallWordAdd.finiteScale_toNat_eq_scale yExponent
  have hxScaleLt := scale_lt h xExponent hxExponent
  have hyScaleLt := scale_lt h yExponent hyExponent
  have hoffset := alignOffset_toNat h
  have hoffsetLt := finiteScaleOffset_lt h
  have hxBound : (finiteScale xExponent).toNat + (alignOffset fmt).toNat < 2 ^ 63 := by
    rw [hoffset]
    norm_num at hxScaleLt hoffsetLt ⊢
    omega
  have hyBound : (finiteScale yExponent).toNat + (alignOffset fmt).toNat < 2 ^ 63 := by
    rw [hoffset]
    norm_num at hyScaleLt hoffsetLt ⊢
    omega
  unfold FiniteKernel.addFields
  rw [ite_eq_left h.isIEEE]
  unfold FiniteScaleAdd.roundSum
  rw [ite_eq_right (by simpa using hxNeNat), ite_eq_right (by simpa using hyNeNat)]
  set xScale := finiteScale xExponent with hxScaleDef
  set yScale := finiteScale yExponent with hyScaleDef
  by_cases hle : xScale ≤ yScale
  · have hleNat : FiniteKernel.scale xExponent.toNat ≤ FiniteKernel.scale yExponent.toNat := by
      rw [← hxScale, ← hyScale]
      exact UInt64.le_iff_toNat_le.mp hle
    have hshiftNat :
        (yScale - xScale).toNat =
          FiniteKernel.scale yExponent.toNat - FiniteKernel.scale xExponent.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ hle, hxScale, hyScale]
    rw [ite_eq_left hle] at hresult
    rw [ite_eq_left hleNat, FiniteScaleAdd.roundAligned_eq]
    by_cases hshift : yScale - xScale ≤ shiftLimit fmt
    · rw [ite_eq_left hshift] at hresult
      have hshiftBound : (yScale - xScale).toNat + fmt.fracWidth ≤ 126 := by
        have hnat := UInt64.le_iff_toNat_le.mp hshift
        rw [hlimit] at hnat
        omega
      obtain ⟨hshifted, hshiftedLt⟩ :=
        shiftedMantissa_toNat h yMantissa (yScale - xScale) hyMantissa hshiftBound
      have hsum :
          xMantissa.toNat + (yMantissa.shiftLeft (yScale - xScale).toNat).toNat < 2 ^ 128 := by
        rw [hshifted]
        norm_num at hpow127 hshiftedLt ⊢
        omega
      rw [FiniteScaleAdd.roundMagnitudes_comm, roundAlignedWords_refines h (alignOffset fmt) xSign
        ySign xMantissa _ xScale (shiftedMantissa_ne_zero _ _ hyNeNat hshifted) hsum hxBound words
        hresult, hshifted, hshiftNat, hxScale, hoffset]
    · rw [ite_eq_right hshift] at hresult
      have hgt := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hshift)
      rw [hlimit] at hgt
      have hlowBound :
          xMantissa.toNat ≤ 2 ^ (fmt.fracWidth + (yScale - xScale).toNat - 1) :=
        hxMantissa.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
      have hscaleBound :
          xScale.toNat + (yScale - xScale).toNat + (alignOffset fmt).toNat < 2 ^ 63 := by
        rw [UInt64.toNat_sub_of_le _ _ hle]
        have := UInt64.le_iff_toNat_le.mp hle
        omega
      rw [roundJammedWords_refines h (alignOffset fmt) ySign xSign yMantissa xMantissa
        (yScale - xScale) xScale hlowBound hxNeNat hscaleBound words hresult, hshiftNat, hxScale,
        hoffset]
  · have hleNat :
        ¬FiniteKernel.scale xExponent.toNat ≤ FiniteKernel.scale yExponent.toNat := by
      intro hk
      apply hle
      apply UInt64.le_iff_toNat_le.mpr
      rwa [hxScale, hyScale]
    have hge : yScale ≤ xScale := by
      apply UInt64.le_iff_toNat_le.mpr
      have hnat : ¬xScale.toNat ≤ yScale.toNat := fun hk => hle (UInt64.le_iff_toNat_le.mpr hk)
      omega
    have hshiftNat :
        (xScale - yScale).toNat =
          FiniteKernel.scale xExponent.toNat - FiniteKernel.scale yExponent.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ hge, hxScale, hyScale]
    rw [ite_eq_right hle] at hresult
    rw [ite_eq_right hleNat, FiniteScaleAdd.roundAligned_eq]
    by_cases hshift : xScale - yScale ≤ shiftLimit fmt
    · rw [ite_eq_left hshift] at hresult
      have hshiftBound : (xScale - yScale).toNat + fmt.fracWidth ≤ 126 := by
        have hnat := UInt64.le_iff_toNat_le.mp hshift
        rw [hlimit] at hnat
        omega
      obtain ⟨hshifted, hshiftedLt⟩ :=
        shiftedMantissa_toNat h xMantissa (xScale - yScale) hxMantissa hshiftBound
      have hsum :
          (xMantissa.shiftLeft (xScale - yScale).toNat).toNat + yMantissa.toNat < 2 ^ 128 := by
        rw [hshifted]
        norm_num at hpow127 hshiftedLt ⊢
        omega
      rw [roundAlignedWords_refines h (alignOffset fmt) xSign ySign _ yMantissa yScale hyNeNat hsum
        hyBound words hresult, hshifted, hshiftNat, hyScale, hoffset]
    · rw [ite_eq_right hshift] at hresult
      have hgt := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hshift)
      rw [hlimit] at hgt
      have hlowBound :
          yMantissa.toNat ≤ 2 ^ (fmt.fracWidth + (xScale - yScale).toNat - 1) :=
        hyMantissa.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
      have hscaleBound :
          yScale.toNat + (xScale - yScale).toNat + (alignOffset fmt).toNat < 2 ^ 63 := by
        rw [UInt64.toNat_sub_of_le _ _ hge]
        have := UInt64.le_iff_toNat_le.mp hge
        omega
      rw [roundJammedWords_refines h (alignOffset fmt) xSign ySign xMantissa yMantissa
        (xScale - yScale) yScale hlowBound hyNeNat hscaleBound words hresult, hshiftNat, hyScale,
        hoffset]

/-! ## Storage-word decoding -/

/-- The two-word significand of a stored value is the generic kernel's decoded significand. -/
theorem finiteMantissaWords_toNat (h : Eligible fmt) (x : Model fmt) :
    (finiteMantissaWords fmt (expField fmt (toWords x).hi) (toWords x).hi
        (toWords x).lo).toNat =
      FiniteKernel.decodeMantissa fmt (Model.expField x) (Model.fracField x) := by
  have hexp := expField_toNat h x
  have hfraction := fraction_toNat h x
  unfold finiteMantissaWords FiniteKernel.decodeMantissa
  by_cases hzero : expField fmt (toWords x).hi = 0
  · have hzeroNat : Model.expField x = 0 := by
      rw [← hexp, hzero]
      rfl
    rw [ite_eq_left (by simp [hzero]), ite_eq_left (by simp [hzeroNat]), ← hfraction]
    unfold UInt128.toNat
    dsimp only
    omega
  · have hzeroNat : Model.expField x ≠ 0 := by
      rw [← hexp]
      intro hk
      exact hzero (UInt64.toNat_inj.mp (by rw [hk]; rfl))
    rw [ite_eq_right (by simpa using hzero), ite_eq_right (by simpa using hzeroNat),
      normalMantissa_toNat h _ _ (fracHigh_lt h _), ← hfraction, pow2_eq_two_pow]
    omega

/-- A decoded two-word significand has at most `fracWidth + 1` bits. -/
theorem finiteMantissaWords_lt (h : Eligible fmt) (exponent high low : UInt64) :
    (finiteMantissaWords fmt exponent high low).toNat < 2 ^ (fmt.fracWidth + 1) := by
  have hfrac := h.frac_gt
  unfold finiteMantissaWords
  split
  · have hhigh := fracHigh_lt h high
    have hlow := low.toNat_lt
    have hsplit : 2 ^ fmt.fracWidth = 2 ^ (fmt.fracWidth - 64) * 2 ^ 64 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hgrow : 2 ^ fmt.fracWidth < 2 ^ (fmt.fracWidth + 1) :=
      Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
    unfold UInt128.toNat
    calc low.toNat + (fracHigh fmt high).toNat * 2 ^ 64
        < ((fracHigh fmt high).toNat + 1) * 2 ^ 64 := by
          rw [Nat.succ_mul]
          omega
      _ ≤ 2 ^ (fmt.fracWidth - 64) * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ fmt.fracWidth := hsplit.symm
      _ < 2 ^ (fmt.fracWidth + 1) := hgrow
  · exact (normalMantissa_bounds h _ _ (fracHigh_lt h high)).2

private theorem isFinite_of_expField (h : Eligible fmt) (x : Model fmt)
    (hfinite : expField fmt (toWords x).hi ≠ expAllOnes fmt) :
    Model.isFinite x = true := by
  have hfiniteNat : Model.expField x ≠ fmt.expAllOnesNat := by
    rw [← expField_toNat h x, ← expAllOnes_toNat h]
    intro hk
    exact hfinite (UInt64.toNat_inj.mp hk)
  simp [Model.isFinite, h.encoding, Model.IEEE.isFinite, hfiniteNat]

/-- The generic finite decoder sees the fields the two-word kernel reads from the storage words. -/
theorem decode_of_finite (h : Eligible fmt) (x : Model fmt)
    (hfinite : expField fmt (toWords x).hi ≠ expAllOnes fmt) :
    FiniteKernel.decode? x =
      some {
        sign := signBit fmt (toWords x).hi
        exponent := (expField fmt (toWords x).hi).toNat
        mantissa :=
          (finiteMantissaWords fmt (expField fmt (toWords x).hi) (toWords x).hi
            (toWords x).lo).toNat } := by
  unfold FiniteKernel.decode?
  rw [ite_eq_right (by simp [isFinite_of_expField h x hfinite])]
  rw [finiteMantissaWords_toNat h x, expField_toNat h x, signBit_eq h x]

/-- Negating a finite value keeps its stored exponent and significand and toggles its sign. -/
theorem decode_neg_of_finite (h : Eligible fmt) (y : Model fmt)
    (hfinite : expField fmt (toWords y).hi ≠ expAllOnes fmt) :
    FiniteKernel.decode? (neg y) =
      some {
        sign := !signBit fmt (toWords y).hi
        exponent := (expField fmt (toWords y).hi).toNat
        mantissa :=
          (finiteMantissaWords fmt (expField fmt (toWords y).hi) (toWords y).hi
            (toWords y).lo).toNat } := by
  unfold FiniteKernel.decode?
  rw [ite_eq_right (by simp [isFinite_neg, isFinite_of_expField h y hfinite])]
  rw [expField_neg, fracField_neg, signBit_neg,
    ite_eq_left (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt h.isIEEE),
    finiteMantissaWords_toNat h y, expField_toNat h y, signBit_eq h y]

/--
An accepted two-word sum or difference is the answer of the compact finite kernel
`FiniteKernel.add?`.

`negateRight` selects subtraction: the kernel toggles the right sign on the storage word, and the
theorem states the corresponding claim about `neg y`.
-/
theorem addFiniteWords_refines (h : Eligible fmt) (x y : Model fmt) (negateRight : Bool)
    (words : UInt128)
    (hresult : addFiniteWords? fmt (toWords x) (toWords y) negateRight = some words) :
    FiniteKernel.add? x (if negateRight then neg y else y) = some (ofWords fmt words) := by
  unfold addFiniteWords? at hresult
  by_cases hexceptional :
      (expField fmt (toWords x).hi == expAllOnes fmt ||
        expField fmt (toWords y).hi == expAllOnes fmt) = true
  · simp [hexceptional] at hresult
  rw [ite_eq_right hexceptional] at hresult
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hexceptional
  obtain ⟨hxFinite, hyFinite⟩ := hexceptional
  have hxExponent := expField_lt h (toWords x).hi
  have hyExponent := expField_lt h (toWords y).hi
  have hxMantissa := finiteMantissaWords_lt h (expField fmt (toWords x).hi) (toWords x).hi
    (toWords x).lo
  have hyMantissa := finiteMantissaWords_lt h (expField fmt (toWords y).hi) (toWords y).hi
    (toWords y).lo
  unfold FiniteKernel.add?
  rw [decode_of_finite h x hxFinite]
  cases negateRight
  · simp only [Bool.false_eq_true, ite_false, Bool.xor_false] at hresult ⊢
    rw [decode_of_finite h y hyFinite]
    simp only
    rw [← FiniteKernel.addFields_eq]
    exact congrArg some
      (addFieldsWords_refines h _ _ _ _ _ _ hxExponent hyExponent hxMantissa hyMantissa words
        hresult).symm
  · simp only [ite_true, Bool.xor_true] at hresult ⊢
    rw [decode_neg_of_finite h y hyFinite]
    simp only
    rw [← FiniteKernel.addFields_eq]
    exact congrArg some
      (addFieldsWords_refines h _ _ _ _ _ _ hxExponent hyExponent hxMantissa hyMantissa words
        hresult).symm

/-! ## Model entry points -/

/-- An accepted storage-word sum is the model-level two-word sum. -/
theorem addFinite?_of_words (x y : Model fmt) (words : UInt128)
    (h : addFiniteWords? fmt (toWords x) (toWords y) false = some words) :
    addFinite? x y = some (ofWords fmt words) := by
  unfold addFinite?
  rw [h]

/-- An accepted storage-word difference is the model-level two-word difference. -/
theorem subFinite?_of_words (x y : Model fmt) (words : UInt128)
    (h : addFiniteWords? fmt (toWords x) (toWords y) true = some words) :
    subFinite? x y = some (ofWords fmt words) := by
  unfold subFinite?
  rw [h]

/-- Two-word addition and the generic finite kernel agree on every input. -/
theorem addFinite_eq (h : Eligible fmt) (x y : Model fmt) :
    addFinite? x y = FiniteKernel.add? x y := by
  unfold addFinite?
  cases hfast : addFiniteWords? fmt (toWords x) (toWords y) false with
  | none => exact FiniteKernel.addRuntime_eq x y
  | some words => simpa using (addFiniteWords_refines h x y false words hfast).symm

/-- Two-word subtraction and generic addition of the negated right operand agree. -/
theorem subFinite_eq (h : Eligible fmt) (x y : Model fmt) :
    subFinite? x y = FiniteKernel.add? x (neg y) := by
  unfold subFinite?
  cases hfast : addFiniteWords? fmt (toWords x) (toWords y) true with
  | none => exact FiniteKernel.addRuntime_eq x (neg y)
  | some words => simpa using (addFiniteWords_refines h x y true words hfast).symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
