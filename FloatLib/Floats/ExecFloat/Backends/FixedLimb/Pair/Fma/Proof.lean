/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Fma.Runtime
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Addition.Proof
import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Proof
import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Multiplication.Proof
import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
import FloatLib.Floats.ExecFloat.Backends.Generic.ScaleAdd.Proof
import FloatLib.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
import FloatLib.Kernels.FixedWord.LimbRound.Proof
import FloatLib.Kernels.FixedWord.Difference.Proof
import FloatLib.Kernels.FixedWord.Product.Proof
import FloatLib.Numerics.ShiftRightJam.Proof
import Mathlib.Tactic.NormNum

/-!
# Correctness of two-word fused multiply-add

Every accepted result of `Fma.Runtime` is the exact finite kernel's answer. The proof follows the
one-word FMA proof: `fmaFieldsWords_refines` matches the alignment branches of `fmaFieldsWords?`
with `FiniteScaleAdd.roundSum` at round offset `0`. Four-word magnitudes are reduced to two words
with `normalizeJam128`, which `FiniteProductRound.round_shiftRightJam` shows does not change the
rounding, and then go through the two-word rounder of `Addition.Proof`. The sticky alignments reuse
the natural-number lemmas of the one-word addition kernel.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

open FloatLib.Numerics.FixedWord

variable {fmt : FloatFormat}

/-! ## Rounding four-word magnitudes -/

/-- A four-word magnitude rounds like its sticky two-word normalization. -/
theorem roundProductWords_refines (h : Eligible fmt) (sign : Bool) (magnitude : UInt256)
    (scale : UInt64) (hmagnitude : magnitude.toNat ≠ 0) (hscale : scale.toNat < 2 ^ 62)
    (words : UInt128)
    (hresult : roundProductWords? fmt sign magnitude scale = some words) :
    ofWords fmt words =
      FiniteScaleAdd.roundMagnitude fmt 0 sign magnitude.toNat scale.toNat := by
  have hfracLe := h.frac_le
  unfold roundProductWords? at hresult
  set jam := magnitude.normalizationShift128 with hjamDef
  have hjamLe : jam ≤ 128 := UInt256.normalizationShift128_le magnitude
  have hjamWord : (UInt64.ofNat jam).toNat = jam := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hscaleJam : (scale + UInt64.ofNat jam).toNat = scale.toNat + jam := by
    rw [UInt64.toNat_add, hjamWord, Nat.mod_eq_of_lt (by omega)]
  have hjammedNe : magnitude.normalizeJam128.toNat ≠ 0 :=
    fun hzero => hmagnitude ((UInt256.normalizeJam128_toNat_eq_zero_iff magnitude).mp hzero)
  have hround := roundMagnitudeWords_refines h 0 sign _ _ hjammedNe
    (by rw [hscaleJam, UInt64.toNat_zero]; omega) words hresult
  rw [hround, UInt256.normalizeJam128_toNat, hscaleJam, UInt64.toNat_zero, ← hjamDef]
  unfold FiniteScaleAdd.roundMagnitude
  simp only [Nat.add_zero]
  by_cases hjam : jam = 0
  · rw [hjam]
    simp [Numerics.shiftRightJam, Nat.mod_one]
  · have hlog : jam + fmt.fracWidth + 2 ≤ magnitude.toNat.log2 := by
      have := UInt256.log2_toNat magnitude
      unfold UInt256.normalizationShift128 at hjamDef
      omega
    exact FiniteProductRound.round_shiftRightJam fmt sign _ _ _ hlog

private theorem toNat_ne_zero_of_ne256 {value : UInt256} (h : value ≠ ⟨0, 0, 0, 0⟩) :
    value.toNat ≠ 0 :=
  fun hzero => h (UInt256.toNat_injective (by rw [hzero]; rfl))

private theorem add256_value_toNat_of_lt (x y : UInt256) (hfit : x.toNat + y.toNat < 2 ^ 256) :
    (add256 x y).value.toNat = x.toNat + y.toNat := by
  rw [add256_value_toNat, Nat.mod_eq_of_lt hfit]

/-- An accepted aligned four-word combination is the exact signed-magnitude combination. -/
theorem roundAlignedProductWords_refines (h : Eligible fmt) (leftSign rightSign : Bool)
    (left right : UInt256) (scale : UInt64)
    (hright : right.toNat ≠ 0) (hsum : left.toNat + right.toNat < 2 ^ 256)
    (hscale : scale.toNat < 2 ^ 62) (words : UInt128)
    (hresult : roundAlignedProductWords? fmt leftSign rightSign left right scale = some words) :
    ofWords fmt words =
      FiniteScaleAdd.roundMagnitudes fmt 0 leftSign rightSign left.toNat right.toNat
        scale.toNat := by
  unfold roundAlignedProductWords? at hresult
  unfold FiniteScaleAdd.roundMagnitudes
  by_cases hsign : leftSign = rightSign
  · rw [ite_eq_left (by simp [hsign])] at hresult
    rw [ite_eq_left (by simp [hsign])]
    have hadd := add256_value_toNat_of_lt left right hsum
    rw [roundProductWords_refines h leftSign _ scale (by rw [hadd]; omega) hscale words hresult,
      hadd]
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
    · have heqNat : left.toNat ≠ right.toNat :=
        fun hnat => heq (UInt256.toNat_injective hnat)
      rw [ite_eq_right (by simpa using heq)] at hresult
      rw [ite_eq_right (by simpa using heqNat)]
      by_cases hlt : left.toNat < right.toNat
      · have hless : left.less right = true := (UInt256.less_eq_true_iff _ _).mpr hlt
        rw [ite_eq_left hless] at hresult
        rw [ite_eq_left hlt]
        have hsub := UInt256.sub_toNat right left hlt.le
        rw [roundProductWords_refines h rightSign _ scale (by rw [hsub]; omega) hscale words
          hresult, hsub]
      · have hless : ¬left.less right = true :=
          fun hk => hlt ((UInt256.less_eq_true_iff _ _).mp hk)
        rw [ite_eq_right hless] at hresult
        rw [ite_eq_right hlt]
        have hsub := UInt256.sub_toNat left right (by omega)
        rw [roundProductWords_refines h leftSign _ scale (by rw [hsub]; omega) hscale words
          hresult, hsub]

/-! ## Sticky alignments -/

private theorem double_three_toNat (high : UInt256) (hhigh : high.toNat < 2 ^ 252) :
    high.double.double.double.toNat = high.toNat * 2 ^ 3 := by
  have h1 : high.double.toNat = high.toNat * 2 := UInt256.double_toNat _ (by omega)
  have h2 : high.double.double.toNat = high.toNat * 4 := by
    rw [UInt256.double_toNat _ (by rw [h1]; omega), h1]
    omega
  rw [UInt256.double_toNat _ (by rw [h2]; omega), h2]
  omega

/-- A sticky gap splits into three guard positions and the discarded tail. -/
private theorem jam_split (H L g : Nat) (hL : L < H * 2 ^ g) (hg : 3 ≤ g) :
    H * 2 ^ g = H * 2 ^ 3 * 2 ^ (g - 3) ∧ L < H * 2 ^ 3 * 2 ^ (g - 3) ∧
      L / 2 ^ (g - 3) < H * 2 ^ 3 := by
  have hsplit : H * 2 ^ g = H * 2 ^ 3 * 2 ^ (g - 3) := by
    rw [Nat.mul_assoc, ← Nat.pow_add, show 3 + (g - 3) = g by omega]
  refine ⟨hsplit, hsplit ▸ hL, Nat.div_lt_of_lt_mul ?_⟩
  rw [Nat.mul_comm (2 ^ (g - 3))]
  exact hsplit ▸ hL

/-- The sticky magnitude of a product above an addend is the jam of the exact aligned sum. -/
private theorem jammedProductWords_toNat (sameSign : Bool) (high : UInt256) (low : UInt128)
    (gap : UInt64) (hhigh : high.toNat < 2 ^ 252)
    (hlowLt : low.toNat < high.toNat * 2 ^ gap.toNat)
    (hlowNe : low.toNat ≠ 0) (hgap : 3 ≤ gap.toNat) :
    (jammedProductWords sameSign high low gap).toNat =
      Numerics.shiftRightJam
        (if sameSign then high.toNat * 2 ^ gap.toNat + low.toNat
          else high.toNat * 2 ^ gap.toNat - low.toNat)
        (gap.toNat - 3) := by
  have hdiscard : (gap - 3).toNat = gap.toNat - 3 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hgap))
  obtain ⟨hgapSplit, hlowSplit, hquot⟩ := jam_split _ _ _ hlowLt hgap
  set d := gap.toNat - 3 with hd
  have hlowerNat :
      (UInt256.ofUInt128 (low.shiftRight (gap - 3).toNat)).toNat = low.toNat / 2 ^ d := by
    rw [UInt256.toNat_ofUInt128, UInt128.shiftRight_toNat, hdiscard]
  have hexact :
      ((low.shiftRight (gap - 3).toNat).shiftLeft (gap - 3).toNat == low) =
        decide (low.toNat % 2 ^ d = 0) := by
    rw [hdiscard]
    exact UInt128.shiftRight_shiftLeft_beq low d hlowNe
  have hupper := double_three_toNat high hhigh
  unfold jammedProductWords
  simp only [hexact]
  rw [hgapSplit]
  cases sameSign
  · simp only [Bool.false_eq_true, ite_false]
    rw [Numerics.shiftRightJam_mul_two_pow_sub _ _ _ hlowSplit.le]
    have hordered :
        (UInt256.ofUInt128 (low.shiftRight (gap - 3).toNat)).toNat ≤
          high.double.double.double.toNat := by
      rw [hlowerNat, hupper]
      omega
    have hsub := UInt256.sub_toNat _ _ hordered
    rw [hlowerNat, hupper] at hsub
    by_cases hz : low.toNat % 2 ^ d = 0
    · simp only [hz, decide_true, ite_true]
      exact hsub
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      have hunit : (⟨0, 0, 0, 1⟩ : UInt256).toNat = 1 := by simp [UInt256.toNat]
      have hone :
          (⟨0, 0, 0, 1⟩ : UInt256).toNat ≤
            (high.double.double.double.sub
              (UInt256.ofUInt128 (low.shiftRight (gap - 3).toNat))).toNat := by
        rw [hsub, hunit]
        omega
      rw [UInt256.setLowBit_toNat, UInt256.sub_toNat _ _ hone, hsub, hunit]
  · simp only [ite_true]
    rw [Numerics.shiftRightJam_add_mul_two_pow]
    have hsum :
        (add256 high.double.double.double
            (UInt256.ofUInt128 (low.shiftRight (gap - 3).toNat))).value.toNat =
          high.toNat * 2 ^ 3 + low.toNat / 2 ^ d := by
      rw [add256_value_toNat_of_lt _ _ (by rw [hupper, hlowerNat]; omega), hupper, hlowerNat]
    by_cases hz : low.toNat % 2 ^ d = 0
    · simp only [hz, decide_true, ite_true]
      exact hsum
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      rw [UInt256.setLowBit_toNat, hsum]

/-- The sticky magnitude of an addend above a product is the jam of the exact aligned sum. -/
private theorem jammedAddendWords_toNat (sameSign : Bool) (high : UInt128) (low : UInt256)
    (gap : UInt64) (hhigh : high.toNat < 2 ^ 124)
    (hlowLt : low.toNat < high.toNat * 2 ^ gap.toNat)
    (hgap : 3 ≤ gap.toNat) :
    (jammedAddendWords sameSign high low gap).toNat =
      Numerics.shiftRightJam
        (if sameSign then high.toNat * 2 ^ gap.toNat + low.toNat
          else high.toNat * 2 ^ gap.toNat - low.toNat)
        (gap.toNat - 3) := by
  have hdiscard : (gap - 3).toNat = gap.toNat - 3 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hgap))
  obtain ⟨hgapSplit, hlowSplit, hquot⟩ := jam_split _ _ _ hlowLt hgap
  set d := gap.toNat - 3 with hd
  have hlowerNat : (low.shiftRight128 (gap - 3).toNat).toNat = low.toNat / 2 ^ d := by
    rw [hdiscard]
    exact UInt256.shiftRight128_toNat_of_quotient_lt low d (by omega)
  have hexact :
      (!low.hasNonzeroBelow (gap - 3).toNat) = decide (low.toNat % 2 ^ d = 0) := by
    rw [hdiscard, UInt256.hasNonzeroBelow_eq]
    by_cases hz : low.toNat % 2 ^ d = 0 <;> simp [hz]
  have hupper : (high.shiftLeft 3).toNat = high.toNat * 2 ^ 3 := by
    rw [UInt128.shiftLeft_toNat _ _ (by decide) (by rw [Nat.shiftLeft_eq]; omega),
      Nat.shiftLeft_eq]
  unfold jammedAddendWords UInt128.jamCombine
  simp only [hexact]
  rw [hgapSplit]
  cases sameSign
  · simp only [Bool.false_eq_true, ite_false]
    rw [Numerics.shiftRightJam_mul_two_pow_sub _ _ _ hlowSplit.le]
    have hordered :
        (low.shiftRight128 (gap - 3).toNat).toNat ≤ (high.shiftLeft 3).toNat := by
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
            ((high.shiftLeft 3).sub (low.shiftRight128 (gap - 3).toNat)).toNat := by
        rw [hsub, hunit]
        omega
      rw [UInt128.setLowBit_toNat, UInt128.sub_toNat _ _ hone, hsub, hunit]
  · simp only [ite_true]
    rw [Numerics.shiftRightJam_add_mul_two_pow]
    have hsum :
        (add128 (high.shiftLeft 3) (low.shiftRight128 (gap - 3).toNat)).value.toNat =
          high.toNat * 2 ^ 3 + low.toNat / 2 ^ d := by
      rw [add128_value_toNat_of_lt _ _ (by rw [hupper, hlowerNat]; omega), hupper, hlowerNat]
    by_cases hz : low.toNat % 2 ^ d = 0
    · simp only [hz, decide_true, ite_true]
      exact hsum
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      rw [UInt128.setLowBit_toNat, hsum]

/-! ## Field fused multiply-add -/

private theorem toNat_ne_zero_of_ne128 {value : UInt128} (h : value ≠ ⟨0, 0⟩) :
    value.toNat ≠ 0 :=
  fun hzero => h (UInt128.toNat_injective (by rw [hzero]; unfold UInt128.toNat; rfl))

private theorem implicit_le_toNat (h : Eligible fmt) (high : UInt128)
    (himplicit : implicitBit fmt ≤ high.hi) : 2 ^ fmt.fracWidth ≤ high.toNat := by
  have hfrac := h.frac_gt
  have hnat := UInt64.le_iff_toNat_le.mp himplicit
  rw [implicitBit_toNat h] at hnat
  have hsplit : 2 ^ fmt.fracWidth = 2 ^ (fmt.fracWidth - 64) * 2 ^ 64 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  unfold UInt128.toNat
  rw [hsplit]
  exact (Nat.mul_le_mul_right _ hnat).trans (Nat.le_add_left _ _)

private theorem productAtLeastImplicit_le (h : Eligible fmt) (product : UInt256)
    (hproduct : productAtLeastImplicit fmt product = true) :
    2 ^ fmt.fracWidth ≤ product.toNat := by
  have hfrac := h.frac_gt
  have hfracLe := h.frac_le
  unfold productAtLeastImplicit at hproduct
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hproduct
  unfold UInt256.toNat
  rcases hproduct with (h3 | h2) | h1
  · have hpos : 1 ≤ product.limb3.toNat := by
      have := UInt64.toNat_inj.not.mpr h3
      simp only [UInt64.toNat_zero] at this
      omega
    calc 2 ^ fmt.fracWidth ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ product.limb3.toNat * 2 ^ 192 := Nat.le_mul_of_pos_left _ hpos
      _ ≤ _ := Nat.le_add_left _ _
  · have hpos : 1 ≤ product.limb2.toNat := by
      have := UInt64.toNat_inj.not.mpr h2
      simp only [UInt64.toNat_zero] at this
      omega
    calc 2 ^ fmt.fracWidth ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ product.limb2.toNat * 2 ^ 128 := Nat.le_mul_of_pos_left _ hpos
      _ ≤ _ := by omega
  · have hnat := UInt64.le_iff_toNat_le.mp h1
    rw [implicitBit_toNat h] at hnat
    have hsplit : 2 ^ fmt.fracWidth = 2 ^ (fmt.fracWidth - 64) * 2 ^ 64 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hsplit]
    have := Nat.mul_le_mul_right (2 ^ 64) hnat
    omega

/--
An accepted field FMA is the exact kernel's rounded sum of the product and the addend.

The hypotheses give the product at most `2 * fracWidth + 2` bits and the addend at most
`fracWidth + 1`, with both scales below `2 ^ 34` and at most 120 fraction bits.
-/
theorem fmaFieldsWords_refines (h : Eligible fmt) (hfracWidth : fmt.fracWidth ≤ 120)
    (productSign : Bool) (product : UInt256) (productScale : UInt64)
    (addendSign : Bool) (addend : UInt128) (addendScale : UInt64)
    (hproduct : product.toNat < 2 ^ (2 * fmt.fracWidth + 2))
    (haddend : addend.toNat < 2 ^ (fmt.fracWidth + 1))
    (hproductScale : productScale.toNat < 2 ^ 34)
    (haddendScale : addendScale.toNat < 2 ^ 34)
    (words : UInt128)
    (hresult :
      fmaFieldsWords? fmt productSign product productScale addendSign addend addendScale =
        some words) :
    ofWords fmt words =
      FiniteScaleAdd.roundSum fmt 0 productSign addendSign
        product.toNat productScale.toNat addend.toNat addendScale.toNat := by
  have hfrac := h.frac_gt
  have hproduct242 : product.toNat < 2 ^ 242 :=
    hproduct.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have haddend121 : addend.toNat < 2 ^ 121 :=
    haddend.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hlimitWord : (UInt64.ofNat (fmt.fracWidth + 2)).toNat = fmt.fracWidth + 2 := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  unfold fmaFieldsWords? at hresult
  unfold FiniteScaleAdd.roundSum
  by_cases hp : product = ⟨0, 0, 0, 0⟩
  · simp [hp] at hresult
  have hpNat := toNat_ne_zero_of_ne256 hp
  rw [ite_eq_right (by simpa using hp)] at hresult
  rw [ite_eq_right (by simpa using hpNat)]
  by_cases ha : addend = ⟨0, 0⟩
  · subst ha
    simp only [beq_self_eq_true, ite_true] at hresult
    have hzero : (⟨0, 0⟩ : UInt128).toNat = 0 := by unfold UInt128.toNat; rfl
    rw [hzero]
    simp only [beq_self_eq_true, ite_true]
    exact roundProductWords_refines h productSign product productScale hpNat (by omega) words
      hresult
  have haNat := toNat_ne_zero_of_ne128 ha
  rw [ite_eq_right (by simpa using ha)] at hresult
  rw [ite_eq_right (by simpa using haNat)]
  by_cases hle : productScale ≤ addendScale
  · have hleNat : productScale.toNat ≤ addendScale.toNat := UInt64.le_iff_toNat_le.mp hle
    have hshiftNat : (addendScale - productScale).toNat =
        addendScale.toNat - productScale.toNat :=
      UInt64.toNat_sub_of_le _ _ hle
    rw [ite_eq_left hle] at hresult
    rw [ite_eq_left hleNat, FiniteScaleAdd.roundAligned_eq]
    by_cases hshift : addendScale - productScale ≤ UInt64.ofNat (fmt.fracWidth + 2)
    · rw [ite_eq_left hshift] at hresult
      have hshiftLe : (addendScale - productScale).toNat ≤ fmt.fracWidth + 2 := by
        have := UInt64.le_iff_toNat_le.mp hshift
        rwa [hlimitWord] at this
      have hshifted :=
        UInt128.shiftLeft256_toNat addend (addendScale - productScale).toNat
          (by omega)
      have hshiftedLt :
          addend.toNat <<< (addendScale - productScale).toNat < 2 ^ 243 := by
        have hlt := Nat.shiftLeft_lt (m := (addendScale - productScale).toNat) haddend
        exact hlt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      have hsum : product.toNat +
          (addend.shiftLeft256 (addendScale - productScale).toNat).toNat <
            2 ^ 256 := by
        rw [hshifted]
        norm_num at hproduct242 hshiftedLt ⊢
        omega
      have hshiftedNe :
          (addend.shiftLeft256 (addendScale - productScale).toNat).toNat ≠
            0 := by
        rw [hshifted, Nat.shiftLeft_eq]
        exact Nat.mul_ne_zero haNat (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
      rw [FiniteScaleAdd.roundMagnitudes_comm,
        roundAlignedProductWords_refines h productSign addendSign product _ productScale
          hshiftedNe hsum (by omega) words hresult, hshifted, hshiftNat]
    · rw [ite_eq_right hshift] at hresult
      split at hresult
      · rename_i himplicit
        have hgt : fmt.fracWidth + 2 < (addendScale - productScale).toNat := by
          have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hshift)
          rwa [hlimitWord] at this
        set gap := addendScale - productScale with hgapDef
        have hgap3 : 3 ≤ gap.toNat := by omega
        have haddendLower := implicit_le_toNat h addend himplicit
        have hlow : product.toNat ≤ 2 ^ (fmt.fracWidth + gap.toNat - 1) :=
          hproduct.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
        have hlowLt : product.toNat < addend.toNat * 2 ^ gap.toNat := by
          calc product.toNat < 2 ^ (2 * fmt.fracWidth + 2) := hproduct
            _ ≤ 2 ^ (fmt.fracWidth + gap.toNat) := Nat.pow_le_pow_right (by decide) (by omega)
            _ = 2 ^ fmt.fracWidth * 2 ^ gap.toNat := Nat.pow_add _ _ _
            _ ≤ addend.toNat * 2 ^ gap.toNat := Nat.mul_le_mul_right _ haddendLower
        have hmag := jammedAddendWords_toNat (addendSign == productSign) addend product gap
          (haddend121.trans (by norm_num)) hlowLt hgap3
        have hdiscard : (gap - 3).toNat = gap.toNat - 3 :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hgap3))
        have hscaleSum :
            (productScale + (gap - 3)).toNat = productScale.toNat + (gap.toNat - 3) := by
          rw [UInt64.toNat_add, hdiscard]
          exact Nat.mod_eq_of_lt (by omega)
        have hmagNe : (jammedAddendWords (addendSign == productSign) addend product gap).toNat ≠
            0 := by
          rw [hmag]
          refine Numerics.shiftRightJam_ne_zero _ _ ?_
          exact (Nat.pow_le_pow_right (by decide) (by omega)).trans
            (NativeSmallWordAdd.alignedMagnitude_lower fmt.fracWidth addend.toNat product.toNat
              gap.toNat _ haddendLower hlow hgap3)
        rw [roundMagnitudeWords_refines h 0 addendSign _ _ hmagNe
            (by rw [hscaleSum, UInt64.toNat_zero]; omega) words hresult,
          hmag, hscaleSum, UInt64.toNat_zero, ← hshiftNat]
        exact FiniteScaleAdd.roundMagnitude_shiftRightJam fmt 0 addendSign productSign addend.toNat
          product.toNat gap.toNat productScale.toNat haddendLower hlow hgap3
      · simp at hresult
  · have hleNat : ¬productScale.toNat ≤ addendScale.toNat :=
      fun hk => hle (UInt64.le_iff_toNat_le.mpr hk)
    have hge : addendScale ≤ productScale := by
      apply UInt64.le_iff_toNat_le.mpr
      omega
    have hshiftNat : (productScale - addendScale).toNat =
        productScale.toNat - addendScale.toNat :=
      UInt64.toNat_sub_of_le _ _ hge
    rw [ite_eq_right hle] at hresult
    rw [ite_eq_right hleNat, FiniteScaleAdd.roundAligned_eq]
    set gap := productScale - addendScale with hgapDef
    have haddendWide : (UInt256.ofUInt128 addend).toNat = addend.toNat :=
      UInt256.toNat_ofUInt128 addend
    by_cases hsmall : gap < 3
    · rw [ite_eq_left hsmall] at hresult
      have hgapSmall : gap.toNat < 3 := by simpa using UInt64.lt_iff_toNat_lt.mp hsmall
      have hgapPos : 0 < gap.toNat := by omega
      have hd1 := UInt256.double_toNat product (by omega)
      have hd2 := UInt256.double_toNat product.double (by rw [hd1]; omega)
      have hshifted :
          (if gap == 0 then product else if gap == 1 then product.double
            else product.double.double).toNat = product.toNat <<< gap.toNat := by
        rw [Nat.shiftLeft_eq]
        by_cases h1 : gap.toNat = 1
        · have hgap1 : gap = 1 := UInt64.toNat_inj.mp h1
          rw [hgap1]
          simp [hd1]
        · have h2 : gap.toNat = 2 := by omega
          have hgap2 : gap = 2 := UInt64.toNat_inj.mp h2
          rw [hgap2]
          simp only [show ((2 : UInt64) == 0) = false by decide,
            show ((2 : UInt64) == 1) = false by decide, Bool.false_eq_true, ite_false]
          rw [hd2, hd1]
          simp only [UInt64.reduceToNat]
          omega
      have hsum :
          (if gap == 0 then product else if gap == 1 then product.double
            else product.double.double).toNat + (UInt256.ofUInt128 addend).toNat < 2 ^ 256 := by
        rw [hshifted, haddendWide, Nat.shiftLeft_eq]
        have : 2 ^ gap.toNat ≤ 4 := by
          calc 2 ^ gap.toNat ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
            _ = 4 := by norm_num
        have := Nat.mul_le_mul_left product.toNat this
        omega
      rw [roundAlignedProductWords_refines h productSign addendSign _ _ addendScale
          (by rw [haddendWide]; exact haNat) hsum (by omega) words hresult,
        hshifted, haddendWide, hshiftNat]
    · rw [ite_eq_right hsmall] at hresult
      split at hresult
      · rename_i hproductBig
        have hgap3 : 3 ≤ gap.toNat := by
          have := UInt64.not_lt.mp hsmall
          simpa using UInt64.le_iff_toNat_le.mp this
        have hproductLower := productAtLeastImplicit_le h product hproductBig
        have hlow : addend.toNat ≤ 2 ^ (fmt.fracWidth + gap.toNat - 1) :=
          haddend.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
        have hlowLt : addend.toNat < product.toNat * 2 ^ gap.toNat := by
          calc addend.toNat < 2 ^ (fmt.fracWidth + 1) := haddend
            _ ≤ 2 ^ (fmt.fracWidth + gap.toNat) := Nat.pow_le_pow_right (by decide) (by omega)
            _ = 2 ^ fmt.fracWidth * 2 ^ gap.toNat := Nat.pow_add _ _ _
            _ ≤ product.toNat * 2 ^ gap.toNat := Nat.mul_le_mul_right _ hproductLower
        have hmag := jammedProductWords_toNat (productSign == addendSign) product addend gap
          (hproduct242.trans (by norm_num)) hlowLt haNat hgap3
        have hdiscard : (gap - 3).toNat = gap.toNat - 3 :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hgap3))
        have hscaleSum :
            (addendScale + (gap - 3)).toNat = addendScale.toNat + (gap.toNat - 3) := by
          rw [UInt64.toNat_add, hdiscard]
          exact Nat.mod_eq_of_lt (by omega)
        have hmagNe :
            (jammedProductWords (productSign == addendSign) product addend gap).toNat ≠ 0 := by
          rw [hmag]
          refine Numerics.shiftRightJam_ne_zero _ _ ?_
          exact (Nat.pow_le_pow_right (by decide) (by omega)).trans
            (NativeSmallWordAdd.alignedMagnitude_lower fmt.fracWidth product.toNat addend.toNat
              gap.toNat _ hproductLower hlow hgap3)
        rw [roundProductWords_refines h productSign _ _ hmagNe (by rw [hscaleSum]; omega) words
            hresult, hmag, hscaleSum, ← hshiftNat]
        exact FiniteScaleAdd.roundMagnitude_shiftRightJam fmt 0 productSign addendSign product.toNat
          addend.toNat gap.toNat addendScale.toNat hproductLower hlow hgap3
      · simp at hresult

/-! ## Storage words and model entry points -/

private theorem scale_lt_two_pow (hexpWidth : fmt.expWidth ≤ 32)
    (exponent : UInt64) (hexponent : exponent.toNat < 2 ^ fmt.expWidth) :
    FiniteKernel.scale exponent.toNat < 2 ^ 32 := by
  have hpow : 2 ^ fmt.expWidth ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hexpWidth
  unfold FiniteKernel.scale
  split <;> omega

/-- An accepted two-word FMA is the exact compact finite kernel's answer. -/
theorem fmaFiniteWords_refines (h : Eligible fmt) (x y z : Model fmt) (words : UInt128)
    (hresult : fmaFiniteWords? fmt (toWords x) (toWords y) (toWords z) = some words) :
    FiniteKernel.fma? x y z = some (ofWords fmt words) := by
  have hbias := h.bias_lt
  unfold fmaFiniteWords? at hresult
  split at hresult
  · simp at hresult
  rename_i hcapacity
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hcapacity
  obtain ⟨hfracWidth, hexpWidth⟩ := hcapacity
  by_cases hexceptional :
      (expField fmt (toWords x).hi == expAllOnes fmt ||
        expField fmt (toWords y).hi == expAllOnes fmt ||
        expField fmt (toWords z).hi == expAllOnes fmt) = true
  · simp [hexceptional] at hresult
  rw [ite_eq_right hexceptional] at hresult
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hexceptional
  obtain ⟨⟨hxFinite, hyFinite⟩, hzFinite⟩ := hexceptional
  set xExponent := expField fmt (toWords x).hi
  set yExponent := expField fmt (toWords y).hi
  set zExponent := expField fmt (toWords z).hi
  set xMantissa := finiteMantissaWords fmt xExponent (toWords x).hi (toWords x).lo
  set yMantissa := finiteMantissaWords fmt yExponent (toWords y).hi (toWords y).lo
  set zMantissa := finiteMantissaWords fmt zExponent (toWords z).hi (toWords z).lo
  have hxMantissa := finiteMantissaWords_lt h xExponent (toWords x).hi (toWords x).lo
  have hyMantissa := finiteMantissaWords_lt h yExponent (toWords y).hi (toWords y).lo
  have hzMantissa := finiteMantissaWords_lt h zExponent (toWords z).hi (toWords z).lo
  have hxScale := scale_lt_two_pow hexpWidth xExponent (expField_lt h _)
  have hyScale := scale_lt_two_pow hexpWidth yExponent (expField_lt h _)
  have hzScale := scale_lt_two_pow hexpWidth zExponent (expField_lt h _)
  have hbias32 : fmt.exponentBias < 2 ^ 32 := by
    have := FloatFormat.exponentBias_lt_two_pow fmt
    have hpow : 2 ^ fmt.expWidth ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hexpWidth
    omega
  have hproduct : (mul128 xMantissa yMantissa).toNat = xMantissa.toNat * yMantissa.toNat :=
    mul128_toNat xMantissa yMantissa
  have hproductLt : xMantissa.toNat * yMantissa.toNat < 2 ^ (2 * fmt.fracWidth + 2) := by
    rw [show 2 * fmt.fracWidth + 2 = (fmt.fracWidth + 1) + (fmt.fracWidth + 1) by omega,
      Nat.pow_add]
    exact Nat.mul_lt_mul'' hxMantissa hyMantissa
  have hproductScale :
      (finiteScale xExponent + finiteScale yExponent).toNat =
        FiniteKernel.scale xExponent.toNat + FiniteKernel.scale yExponent.toNat := by
    rw [UInt64.toNat_add, NativeSmallWordAdd.finiteScale_toNat_eq_scale,
      NativeSmallWordAdd.finiteScale_toNat_eq_scale, Nat.mod_eq_of_lt (by omega)]
  have haddendScale :
      (finiteScale zExponent + alignOffset fmt).toNat =
        FiniteKernel.scale zExponent.toNat + FiniteKernel.finiteScaleOffset fmt := by
    have hoffset := alignOffset_toNat h
    have hoffsetLt : FiniteKernel.finiteScaleOffset fmt < 2 ^ 33 := by
      unfold FiniteKernel.finiteScaleOffset
      omega
    rw [UInt64.toNat_add, NativeSmallWordAdd.finiteScale_toNat_eq_scale, hoffset,
      Nat.mod_eq_of_lt (by omega)]
  have hk := fmaFieldsWords_refines h hfracWidth _ _ _ _ _ _
    (by rw [hproduct]; exact hproductLt) hzMantissa
    (by rw [hproductScale]; omega)
    (by rw [haddendScale]; unfold FiniteKernel.finiteScaleOffset; omega)
    words hresult
  rw [hproduct, hproductScale, haddendScale] at hk
  unfold FiniteKernel.fma?
  rw [decode_of_finite h x hxFinite, decode_of_finite h y hyFinite,
    decode_of_finite h z hzFinite]
  simp only
  rw [← FiniteKernel.Internal.fmaComponents_eq]
  unfold FiniteKernel.Internal.fmaComponents
  rw [ite_eq_left h.isIEEE, hk]

/-- An accepted storage-word FMA is the model-level two-word FMA. -/
theorem fmaFinite?_of_words (x y z : Model fmt) (words : UInt128)
    (hwords : fmaFiniteWords? fmt (toWords x) (toWords y) (toWords z) = some words) :
    fmaFinite? x y z = some (ofWords fmt words) := by
  unfold fmaFinite?
  rw [hwords]

/-- Two-word fused multiply-add and the generic finite kernel agree on every input. -/
theorem fmaFinite_eq (h : Eligible fmt) (x y z : Model fmt) :
    fmaFinite? x y z = FiniteKernel.fma? x y z := by
  unfold fmaFinite?
  cases hfast : fmaFiniteWords? fmt (toWords x) (toWords y) (toWords z) with
  | none =>
      exact (FiniteKernel.fmaRuntimeFlat_eq x y z).trans (FiniteKernel.fmaRuntime_eq x y z)
  | some words => exact (fmaFiniteWords_refines h x y z words hfast).symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
