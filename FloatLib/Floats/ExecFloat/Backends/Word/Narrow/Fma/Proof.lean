/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.AddDyadic.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Finite.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Fma.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Packing
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.SignedMagnitude.Proof
import FloatLib.Floats.Formats.BinaryInterchange.ModelRounding.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Base.Proof
import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.ModelBridge
import FloatLib.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
import FloatLib.Numerics.ShiftRightJam.Proof
import FloatLib.Kernels.FixedWord.Core.Proof.Rounding

/-!
# Correctness of native-word fused multiply-add for generic binary32

The `UInt64` fused multiply-add kernel agrees with its exact-dyadic finite specification.
Runtime clients can import `Fma.Runtime` without the alignment, packing and rounding proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

open FloatLib.Numerics.FixedWord (shiftRightWord jamCombine jamCombine_toNat)

private theorem roundFmaAlignedRight_eq
    (productSign zSign : Bool)
    (product zMantissa productScale zProductScale : UInt64)
    (hproduct : product ≠ 0) (hz : zMantissa ≠ 0)
    (hproductBound : product.toNat < 2 ^ 48)
    (hzBound : zMantissa.toNat < 2 ^ 24)
    (hproductScaleBound : productScale.toNat ≤ 506)
    (hscale : productScale ≤ zProductScale)
    (hshift : zProductScale - productScale ≤ 39) :
    roundProduct
        (FloatLib.Numerics.FixedWord.addSignedMagnitudes
          productSign zSign product
          (zMantissa <<< (zProductScale - productScale))).1
        (FloatLib.Numerics.FixedWord.addSignedMagnitudes
          productSign zSign product
          (zMantissa <<< (zProductScale - productScale))).2
        productScale =
      roundDyadic
        (Model.addDyadic
          { negative := productSign
            significand := product.toNat
            exponent := Int.ofNat productScale.toNat - 298 }
          { negative := zSign
            significand := zMantissa.toNat
            exponent := Int.ofNat zProductScale.toNat - 298 }) := by
  have hscaleNat : productScale.toNat ≤ zProductScale.toNat :=
    UInt64.le_iff_toNat_le.mp hscale
  have hshiftToNat :
      (zProductScale - productScale).toNat =
        zProductScale.toNat - productScale.toNat := by
    rw [UInt64.toNat_sub_of_le zProductScale productScale hscale]
  have hshiftNatLe : (zProductScale - productScale).toNat ≤ 39 := by
    have h := UInt64.le_iff_toNat_le.mp hshift
    simpa using h
  have hshiftNatLt : (zProductScale - productScale).toNat < 64 := by
    omega
  have hzNat : zMantissa.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hz
  have hzLogLt : zMantissa.toNat.log2 < 24 := by
    rw [Nat.log2_lt hzNat]
    exact hzBound
  have hzShiftedBound :
      zMantissa.toNat <<< (zProductScale - productScale).toNat < 2 ^ 63 := by
    calc
      zMantissa.toNat <<< (zProductScale - productScale).toNat <
          2 ^ (zMantissa.toNat.log2 + 1 +
            (zProductScale - productScale).toNat) :=
        Nat.shiftLeft_lt Nat.lt_log2_self
      _ ≤ 2 ^ 63 := by
        apply Nat.pow_le_pow_right
        · decide
        · omega
  have hzShiftedFit :
      zMantissa.toNat <<< (zProductScale - productScale).toNat < 2 ^ 64 :=
    lt_trans hzShiftedBound (by norm_num)
  have hzShiftedToNat :
      (zMantissa <<< (zProductScale - productScale)).toNat =
        zMantissa.toNat <<< (zProductScale - productScale).toNat := by
    rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hshiftNatLt,
      Nat.mod_eq_of_lt hzShiftedFit]
  have hzShiftedNatNonzero :
      zMantissa.toNat <<< (zProductScale - productScale).toNat ≠ 0 := by
    simp [Nat.shiftLeft_eq, hzNat]
  have hzShiftedNonzero :
      zMantissa <<< (zProductScale - productScale) ≠ 0 := by
    intro h
    have hnat := congrArg UInt64.toNat h
    rw [hzShiftedToNat] at hnat
    exact hzShiftedNatNonzero hnat
  have hsum :
      product.toNat +
          (zMantissa <<< (zProductScale - productScale)).toNat <
        2 ^ 64 := by
    rw [hzShiftedToNat]
    norm_num at hproductBound hzShiftedBound ⊢
    omega
  have hround := roundAddMagnitudesAtScale_eq_roundDyadic
    productSign zSign product
      (zMantissa <<< (zProductScale - productScale))
      productScale hproduct hzShiftedNonzero hsum hproductScaleBound
  rw [hzShiftedToNat, hshiftToNat] at hround
  have halign := addDyadic_alignRightOffset 298
    productSign zSign product.toNat zMantissa.toNat
    productScale.toNat zProductScale.toNat
    (by simpa [← UInt64.toNat_inj] using hproduct) hzNat hscaleNat
  norm_num at halign
  exact hround.trans (congrArg roundDyadic halign.symm)

private theorem roundFmaAlignedLeft_eq
    (productSign zSign : Bool)
    (product zMantissa productScale zProductScale : UInt64)
    (hproduct : product ≠ 0) (hz : zMantissa ≠ 0)
    (hproductBound : product.toNat < 2 ^ 48)
    (hzBound : zMantissa.toNat < 2 ^ 24)
    (hzScaleBound : zProductScale.toNat ≤ 506)
    (hscale : ¬productScale ≤ zProductScale)
    (hshift : productScale - zProductScale ≤ 15) :
    roundProduct
        (FloatLib.Numerics.FixedWord.addSignedMagnitudes
          productSign zSign
          (product <<< (productScale - zProductScale)) zMantissa).1
        (FloatLib.Numerics.FixedWord.addSignedMagnitudes
          productSign zSign
          (product <<< (productScale - zProductScale)) zMantissa).2
        zProductScale =
      roundDyadic
        (Model.addDyadic
          { negative := productSign
            significand := product.toNat
            exponent := Int.ofNat productScale.toNat - 298 }
          { negative := zSign
            significand := zMantissa.toNat
            exponent := Int.ofNat zProductScale.toNat - 298 }) := by
  have hscaleNat : zProductScale.toNat < productScale.toNat := by
    have hnot : ¬productScale.toNat ≤ zProductScale.toNat := by
      intro hle
      exact hscale (UInt64.le_iff_toNat_le.mpr hle)
    omega
  have hscaleWord : zProductScale ≤ productScale :=
    UInt64.le_iff_toNat_le.mpr hscaleNat.le
  have hshiftToNat :
      (productScale - zProductScale).toNat =
        productScale.toNat - zProductScale.toNat := by
    rw [UInt64.toNat_sub_of_le productScale zProductScale hscaleWord]
  have hshiftNatLe : (productScale - zProductScale).toNat ≤ 15 := by
    have h := UInt64.le_iff_toNat_le.mp hshift
    simpa using h
  have hshiftNatLt : (productScale - zProductScale).toNat < 64 := by
    omega
  have hproductNat : product.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hproduct
  have hproductLogLt : product.toNat.log2 < 48 := by
    rw [Nat.log2_lt hproductNat]
    exact hproductBound
  have hproductShiftedBound :
      product.toNat <<< (productScale - zProductScale).toNat < 2 ^ 63 := by
    calc
      product.toNat <<< (productScale - zProductScale).toNat <
          2 ^ (product.toNat.log2 + 1 +
            (productScale - zProductScale).toNat) :=
        Nat.shiftLeft_lt Nat.lt_log2_self
      _ ≤ 2 ^ 63 := by
        apply Nat.pow_le_pow_right
        · decide
        · omega
  have hproductShiftedFit :
      product.toNat <<< (productScale - zProductScale).toNat < 2 ^ 64 :=
    lt_trans hproductShiftedBound (by norm_num)
  have hproductShiftedToNat :
      (product <<< (productScale - zProductScale)).toNat =
        product.toNat <<< (productScale - zProductScale).toNat := by
    rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hshiftNatLt,
      Nat.mod_eq_of_lt hproductShiftedFit]
  have hproductShiftedNatNonzero :
      product.toNat <<< (productScale - zProductScale).toNat ≠ 0 := by
    simp [Nat.shiftLeft_eq, hproductNat]
  have hproductShiftedNonzero :
      product <<< (productScale - zProductScale) ≠ 0 := by
    intro h
    have hnat := congrArg UInt64.toNat h
    rw [hproductShiftedToNat] at hnat
    exact hproductShiftedNatNonzero hnat
  have hsum :
      (product <<< (productScale - zProductScale)).toNat +
          zMantissa.toNat <
        2 ^ 64 := by
    rw [hproductShiftedToNat]
    norm_num at hzBound hproductShiftedBound ⊢
    omega
  have hround := roundAddMagnitudesAtScale_eq_roundDyadic
    productSign zSign
      (product <<< (productScale - zProductScale)) zMantissa
      zProductScale hproductShiftedNonzero hz hsum hzScaleBound
  rw [hproductShiftedToNat, hshiftToNat] at hround
  have halign := addDyadic_alignLeftOffset 298
    productSign zSign product.toNat zMantissa.toNat
    productScale.toNat zProductScale.toNat hproductNat
    (by simpa [← UInt64.toNat_inj] using hz) hscaleNat
  norm_num at halign
  exact hround.trans (congrArg roundDyadic halign.symm)

private theorem roundFmaFarAddNormal
    (sign : Bool) (small large smallScale dominantScale gap : Nat)
    (hsmall : small < 2 ^ 48)
    (hlargeLow : 2 ^ 23 ≤ large)
    (hlargeHigh : large < 2 ^ 24)
    (hgap : 48 < gap)
    (hscale : smallScale + gap = dominantScale + 149)
    (hdominantScale : dominantScale ≤ 253) :
    roundDyadic
        { negative := sign
          significand := (large <<< gap) + small
          exponent := Int.ofNat smallScale - 298 } =
      mkBits sign (dominantScale + 1) (large - 2 ^ 23) := by
  have hsmallHalf : small < 2 ^ (gap - 1) :=
    hsmall.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  rw [roundDyadic_shiftLeft_add_of_lt_half sign small large gap
    (Int.ofNat smallScale - 298) hlargeLow hlargeHigh (by omega) hsmallHalf
    (by simp only [Int.ofNat_eq_natCast]; omega)
    (by simp only [Int.ofNat_eq_natCast]; omega)]
  congr 1
  simp only [Int.ofNat_eq_natCast]
  omega

private theorem roundFmaFarAddSubnormal
    (sign : Bool) (small large smallScale gap : Nat)
    (hsmall : small < 2 ^ 48)
    (hlargePos : 0 < large)
    (hlargeHigh : large < 2 ^ 23)
    (hgap : 48 < gap)
    (hscale : smallScale + gap = 149) :
    roundDyadic
        { negative := sign
          significand := (large <<< gap) + small
          exponent := Int.ofNat smallScale - 298 } =
      mkBits sign 0 large := by
  have hlargeNe : large ≠ 0 := Nat.ne_of_gt hlargePos
  have hcombinedPos : 0 < (large <<< gap) + small := by
    simp only [Nat.shiftLeft_eq]
    positivity
  have hcombinedNe : (large <<< gap) + small ≠ 0 :=
    Nat.ne_of_gt hcombinedPos
  have hsmallGap : small < 2 ^ gap := by
    exact hsmall.trans_le <|
      Nat.pow_le_pow_right (by decide) (by omega)
  have hcombinedUpper :
      (large <<< gap) + small < 2 ^ (23 + gap) := by
    have hlargeSucc : large + 1 ≤ 2 ^ 23 := by omega
    calc
      (large <<< gap) + small = large * 2 ^ gap + small := by
        rw [Nat.shiftLeft_eq]
      _ < large * 2 ^ gap + 2 ^ gap := Nat.add_lt_add_left hsmallGap _
      _ = (large + 1) * 2 ^ gap := by ring
      _ ≤ 2 ^ 23 * 2 ^ gap := Nat.mul_le_mul_right _ hlargeSucc
      _ = 2 ^ (23 + gap) := by rw [pow_add]
  have hcombinedLog :
      ((large <<< gap) + small).log2 < 23 + gap := by
    rw [Nat.log2_lt hcombinedNe]
    exact hcombinedUpper
  have hcombinedSubnormal :
      Int.ofNat ((large <<< gap) + small).log2 +
          (Int.ofNat smallScale - 298) < -126 := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hgapPos : 0 < gap := by omega
  have hsmallHalf : small < Model.pow2 (gap - 1) := by
    rw [Model.pow2_eq_two_pow]
    exact hsmall.trans_le <|
      Nat.pow_le_pow_right (by decide) (by omega)
  have hround :
      Numerics.roundShiftRightEven ((large <<< gap) + small) gap = large :=
    Model.roundShiftRightEven_shiftLeft_add_of_lt_half
      large small gap hgapPos hsmallHalf
  have hcombinedExponent :
      Int.ofNat smallScale - 298 + 149 =
        Int.negSucc (gap - 1) := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hlargePow : large ≠ Model.pow2 23 := by
    rw [Model.pow2_eq_two_pow]
    omega
  have hshift : gap - 1 + 1 = gap := by omega
  unfold roundDyadic
  simp only [beq_iff_eq, hcombinedNe, ite_false,
    hcombinedSubnormal, hcombinedExponent]
  rw [hshift, hround]
  simp [hlargeNe, hlargePow]

private theorem roundFmaFarAddValue
    (z : Value) (small smallScale gap : Nat)
    (hsmall : small < 2 ^ 48)
    (hzFinite : expField (toUInt32 z) ≠ 0xff)
    (hzNonzero :
      finiteMantissa
        (expField (toUInt32 z)) (fracField (toUInt32 z)) ≠ 0)
    (hgap : 48 < gap)
    (hscale :
      smallScale + gap =
        (finiteScale (expField (toUInt32 z))).toNat + 149) :
    roundDyadic
        { negative := signBit (toUInt32 z)
          significand :=
            (finiteMantissa
                (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat <<< gap +
              small
          exponent := Int.ofNat smallScale - 298 } =
      toUInt32 z := by
  have hfraction := fracField_lt z
  have hlargeNonzero :
      (finiteMantissa
          (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hzNonzero
  have hscaleBound :
      (finiteScale (expField (toUInt32 z))).toNat ≤ 253 :=
    finiteScale_le
      (expField (toUInt32 z)) (expField_lt z) hzFinite
  by_cases hexponent : expField (toUInt32 z) = 0
  · have hlarge :
        (finiteMantissa
            (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat =
          (fracField (toUInt32 z)).toNat := by
      rw [finiteMantissa_toNat
        (expField (toUInt32 z)) (fracField (toUInt32 z)) hfraction]
      simp [hexponent]
    have hlargePos : 0 < (fracField (toUInt32 z)).toNat := by
      rw [← hlarge]
      exact Nat.pos_of_ne_zero hlargeNonzero
    have hscaleZero :
        (finiteScale (expField (toUInt32 z))).toNat = 0 := by
      rw [finiteScale_toNat]
      simp [hexponent]
    have hscale' : smallScale + gap = 149 := by
      rw [hscale, hscaleZero]
    rw [hlarge]
    rw [roundFmaFarAddSubnormal
      (signBit (toUInt32 z)) small (fracField (toUInt32 z)).toNat
      smallScale gap hsmall hlargePos hfraction hgap hscale']
    simpa [hexponent] using mkBits_fields (toUInt32 z)
  · have hlarge :
        (finiteMantissa
            (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat =
          Model.pow2 23 + (fracField (toUInt32 z)).toNat := by
      simpa [hexponent] using
        finiteMantissa_toNat
          (expField (toUInt32 z)) (fracField (toUInt32 z)) hfraction
    have hlargeLow :
        2 ^ 23 ≤
          (finiteMantissa
            (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat := by
      rw [hlarge, Model.pow2_eq_two_pow]
      omega
    have hlargeHigh :
        (finiteMantissa
            (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat <
          2 ^ 24 :=
      finiteMantissa_lt
        (expField (toUInt32 z)) (fracField (toUInt32 z)) hfraction
    have hscaleToNat :
        (finiteScale (expField (toUInt32 z))).toNat =
          (expField (toUInt32 z)).toNat - 1 := by
      rw [finiteScale_toNat]
      simp [hexponent]
    have hexponentNatNonzero :
        (expField (toUInt32 z)).toNat ≠ 0 := by
      intro h
      apply hexponent
      apply UInt32.toNat_inj.mp
      simpa using h
    have hexponentValue :
        (finiteScale (expField (toUInt32 z))).toNat + 1 =
          (expField (toUInt32 z)).toNat := by
      rw [hscaleToNat]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hexponentNatNonzero)
    have hfractionValue :
        (finiteMantissa
            (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat -
            2 ^ 23 =
          (fracField (toUInt32 z)).toNat := by
      rw [hlarge, Model.pow2_eq_two_pow]
      omega
    rw [roundFmaFarAddNormal
      (signBit (toUInt32 z)) small
      (finiteMantissa
        (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat
      smallScale (finiteScale (expField (toUInt32 z))).toNat gap
      hsmall hlargeLow hlargeHigh hgap hscale hscaleBound]
    rw [hexponentValue, hfractionValue]
    exact mkBits_fields (toUInt32 z)

/-! ## Sticky alignment outside the exact windows -/

private theorem shiftRightWord_toNat_eq_div (value shift : UInt64) :
    (shiftRightWord value shift).toNat = value.toNat / 2 ^ shift.toNat := by
  unfold shiftRightWord
  split
  · rename_i h
    have hs : shift.toNat < 64 := by simpa using UInt64.lt_iff_toNat_lt.mp h
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hs]
  · rename_i h
    have hs : 64 ≤ shift.toNat := by simpa using UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h)
    rw [UInt64.toNat_zero, eq_comm, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
    exact value.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) hs)

private theorem isExactShift_eq (value shift : UInt64) (hvalue : value.toNat ≠ 0) :
    isExactShift value shift = decide (value.toNat % 2 ^ shift.toNat = 0) := by
  unfold isExactShift
  by_cases h : shift < 64
  · have hs : shift.toNat < 64 := by simpa using UInt64.lt_iff_toNat_lt.mp h
    simp only [h, decide_true, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftLeft,
      UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have hle : value.toNat / 2 ^ shift.toNat * 2 ^ shift.toNat ≤ value.toNat :=
      Nat.div_mul_le_self _ _
    rw [Nat.mod_eq_of_lt (hle.trans_lt value.toNat_lt)]
    have := Nat.div_add_mod' value.toNat (2 ^ shift.toNat)
    omega
  · have hs : 64 ≤ shift.toNat := by simpa using UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h)
    simp only [h, decide_false, Bool.false_and]
    symm
    rw [decide_eq_false_iff_not, Nat.mod_eq_of_lt
      (value.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) hs))]
    exact hvalue

/-- A sticky quotient rounds like the exact magnitude once 25 bits stay above it. -/
private theorem roundDyadic_shiftRightJam (sign : Bool) (magnitude scale d : Nat)
    (hleading : d + 25 ≤ magnitude.log2) :
    roundDyadic
        { negative := sign
          significand := Numerics.shiftRightJam magnitude d
          exponent := Int.ofNat (scale + d) - 298 } =
      roundDyadic
        { negative := sign
          significand := magnitude
          exponent := Int.ofNat scale - 298 } := by
  have hinj : ∀ a b : UInt32, ofUInt32 a = ofUInt32 b → a = b := fun a b h => by
    simpa using congrArg toUInt32 h
  apply hinj
  rw [ofUInt32_roundDyadic, ofUInt32_roundDyadic]
  have h298 : (298 : Int) =
      Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp FloatFormat.binary32) := by decide
  rw [h298, ← FiniteProductRound.round_eq_roundDyadic FloatFormat.binary32 (by decide),
    ← FiniteProductRound.round_eq_roundDyadic FloatFormat.binary32 (by decide)]
  exact FiniteProductRound.round_shiftRightJam FloatFormat.binary32 sign magnitude scale d (by
    have : FloatFormat.binary32.fracWidth = 23 := by decide
    rw [this]
    omega)

/-- A normal addend far above the product rounds through three guard bits and a sticky product. -/
private theorem roundFmaJamAbove_eq
    (productSign zSign : Bool)
    (product zMantissa productScale zProductScale : UInt64)
    (hproduct : product ≠ 0)
    (hproductBound : product.toNat < 2 ^ 48)
    (hzLower : 0x800000 ≤ zMantissa)
    (hzBound : zMantissa.toNat < 2 ^ 24)
    (hzProductScaleBound : zProductScale.toNat ≤ 506)
    (hscale : productScale ≤ zProductScale)
    (hshift : ¬zProductScale - productScale ≤ 39) :
    roundProduct zSign
        (jamCombine (productSign == zSign)
          (isExactShift product (zProductScale - productScale - 3))
          (zMantissa <<< 3) (shiftRightWord product (zProductScale - productScale - 3)))
        (productScale + (zProductScale - productScale - 3)) =
      roundDyadic
        (Model.addDyadic
          { negative := productSign
            significand := product.toNat
            exponent := Int.ofNat productScale.toNat - 298 }
          { negative := zSign
            significand := zMantissa.toNat
            exponent := Int.ofNat zProductScale.toNat - 298 }) := by
  have hscaleNat : productScale.toNat ≤ zProductScale.toNat := UInt64.le_iff_toNat_le.mp hscale
  have hsWord : (zProductScale - productScale).toNat = zProductScale.toNat - productScale.toNat :=
    UInt64.toNat_sub_of_le _ _ hscale
  have hsBig : 39 < zProductScale.toNat - productScale.toNat := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hshift)
    rw [hsWord] at this
    simpa using this
  set s := zProductScale.toNat - productScale.toNat with hs
  have hdiscard : (zProductScale - productScale - 3).toNat = s - 3 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hsWord]; simp; omega)),
      hsWord]
    rfl
  set d := s - 3 with hd
  have hproductNe : product.toNat ≠ 0 := by simpa [← UInt64.toNat_inj] using hproduct
  have hzLowerNat : 2 ^ 23 ≤ zMantissa.toNat := by
    simpa using UInt64.le_iff_toNat_le.mp hzLower
  have hzNe : zMantissa.toNat ≠ 0 := by omega
  have hzShift : (zMantissa <<< 3).toNat = zMantissa.toNat * 2 ^ 3 := by
    have hfit : zMantissa.toNat <<< 3 < 2 ^ 64 := by
      rw [Nat.shiftLeft_eq]
      calc zMantissa.toNat * 2 ^ 3 < 2 ^ 24 * 2 ^ 3 :=
            Nat.mul_lt_mul_of_pos_right hzBound (by decide)
        _ ≤ 2 ^ 64 := by norm_num
    have h := FloatLib.Numerics.FixedWord.shiftLeft_toNat zMantissa 3 (by decide) hfit
    simpa [Nat.shiftLeft_eq] using h
  have hq : (shiftRightWord product (zProductScale - productScale - 3)).toNat =
      product.toNat / 2 ^ d := by
    rw [shiftRightWord_toNat_eq_div, hdiscard]
  have hqSmall : product.toNat / 2 ^ d < 2 ^ 11 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact hproductBound.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hexact : isExactShift product (zProductScale - productScale - 3) =
      decide (product.toNat % 2 ^ d = 0) := by
    rw [isExactShift_eq _ _ hproductNe, hdiscard]
  have hproductLe : product.toNat ≤ (zMantissa <<< 3).toNat * 2 ^ d := by
    rw [hzShift]
    calc product.toNat ≤ 2 ^ 48 := hproductBound.le
      _ ≤ 2 ^ 23 * 2 ^ 3 * 2 ^ d := by
        rw [← Nat.pow_add, ← Nat.pow_add]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ zMantissa.toNat * 2 ^ 3 * 2 ^ d :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hzLowerNat)
  have hmag := jamCombine_toNat (productSign == zSign)
    (isExactShift product (zProductScale - productScale - 3))
    (zMantissa <<< 3) (shiftRightWord product (zProductScale - productScale - 3))
    product.toNat d hq hexact (by rw [hzShift, hq]; omega)
    (fun _ => ⟨by rw [hzShift, hq]; omega, hproductLe⟩)
  have hscaleSum : (productScale + (zProductScale - productScale - 3)).toNat =
      productScale.toNat + d := by
    rw [UInt64.toNat_add, hdiscard]
    exact Nat.mod_eq_of_lt (by change _ < 18446744073709551616; omega)
  have hpowS : zMantissa.toNat * 2 ^ 3 * 2 ^ d = zMantissa.toNat * 2 ^ s := by
    rw [Nat.mul_assoc, ← Nat.pow_add, show 3 + d = s by omega]
  have hzS : 2 ^ (23 + s) ≤ zMantissa.toNat * 2 ^ s := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_right _ hzLowerNat
  have hp22 : product.toNat ≤ 2 ^ (22 + s) :=
    hproductBound.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hpow22 : 2 ^ (22 + s) * 2 = 2 ^ (23 + s) := by
    rw [show 23 + s = (22 + s) + 1 by omega, Nat.pow_succ]
  have hbound : 2 ^ (22 + s) ≤
      (if (productSign == zSign) = true then zMantissa.toNat * 2 ^ s + product.toNat
        else zMantissa.toNat * 2 ^ s - product.toNat) := by
    split <;> omega
  have hlhs : roundProduct zSign
        (jamCombine (productSign == zSign)
          (isExactShift product (zProductScale - productScale - 3))
          (zMantissa <<< 3) (shiftRightWord product (zProductScale - productScale - 3)))
        (productScale + (zProductScale - productScale - 3)) =
      roundDyadic
        { negative := zSign
          significand :=
            if (productSign == zSign) = true then zMantissa.toNat * 2 ^ s + product.toNat
            else zMantissa.toNat * 2 ^ s - product.toNat
          exponent := Int.ofNat productScale.toNat - 298 } := by
    rw [roundProduct_eq_roundDyadic _ _ _ (by rw [hscaleSum]; omega), hscaleSum, hmag, hzShift,
      hpowS]
    exact roundDyadic_shiftRightJam _ _ _ _ (by
      have hpositive := (Nat.two_pow_pos _).trans_le hbound
      have := (Nat.le_log2 hpositive.ne').2 hbound
      omega)
  have halign := addDyadic_alignRightOffset 298 productSign zSign product.toNat zMantissa.toNat
    productScale.toNat zProductScale.toNat hproductNe hzNe hscaleNat
  norm_num at halign
  rw [hlhs]
  simp only [Int.ofNat_eq_natCast]
  rw [halign, ← hs, Nat.shiftLeft_eq]
  have hzShiftedNe : zMantissa.toNat * 2 ^ s ≠ 0 := by positivity
  by_cases hsign : productSign = zSign
  · subst hsign
    rw [addDyadic_sameSign_sameExponent _ _ _ _ hproductNe hzShiftedNe]
    simp only [beq_self_eq_true, ite_true, Nat.add_comm]
  · have hsignBeq : (productSign == zSign) = false := by simpa using hsign
    rw [addDyadic_oppositeSign_sameExponent_largeRight _ _ _ _ _ hproductNe hzShiftedNe hsign
      (by omega)]
    simp only [hsignBeq, Bool.false_eq_true, ite_false]

/-- A product of at least `2^46` absorbs a far-below addend through a sticky bit. -/
private theorem roundFmaJamBelow_eq
    (productSign zSign : Bool)
    (product zMantissa productScale zProductScale : UInt64)
    (hproductLower : 0x400000000000 ≤ product)
    (hproductBound : product.toNat < 2 ^ 48)
    (hz : zMantissa ≠ 0)
    (hzBound : zMantissa.toNat < 2 ^ 24)
    (hproductScaleBound : productScale.toNat ≤ 506)
    (hscale : ¬productScale ≤ zProductScale)
    (hshift : ¬productScale - zProductScale ≤ 15) :
    roundProduct productSign
        (jamCombine (productSign == zSign)
          (isExactShift zMantissa (productScale - zProductScale))
          product (shiftRightWord zMantissa (productScale - zProductScale)))
        productScale =
      roundDyadic
        (Model.addDyadic
          { negative := productSign
            significand := product.toNat
            exponent := Int.ofNat productScale.toNat - 298 }
          { negative := zSign
            significand := zMantissa.toNat
            exponent := Int.ofNat zProductScale.toNat - 298 }) := by
  have hlt : zProductScale < productScale := UInt64.not_le.mp hscale
  have hltNat : zProductScale.toNat < productScale.toNat := UInt64.lt_iff_toNat_lt.mp hlt
  have htWord : (productScale - zProductScale).toNat = productScale.toNat - zProductScale.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hlt)
  set t := productScale.toNat - zProductScale.toNat with ht
  have htBig : 15 < t := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hshift)
    rw [htWord] at this
    simpa using this
  have hproductLowerNat : 2 ^ 46 ≤ product.toNat := by
    simpa using UInt64.le_iff_toNat_le.mp hproductLower
  have hproductNe : product.toNat ≠ 0 := by omega
  have hzNe : zMantissa.toNat ≠ 0 := by simpa [← UInt64.toNat_inj] using hz
  have hq : (shiftRightWord zMantissa (productScale - zProductScale)).toNat =
      zMantissa.toNat / 2 ^ t := by
    rw [shiftRightWord_toNat_eq_div, htWord]
  have hqLe : zMantissa.toNat / 2 ^ t ≤ zMantissa.toNat := Nat.div_le_self _ _
  have hexact : isExactShift zMantissa (productScale - zProductScale) =
      decide (zMantissa.toNat % 2 ^ t = 0) := by
    rw [isExactShift_eq _ _ hzNe, htWord]
  have hzLe : zMantissa.toNat ≤ product.toNat * 2 ^ t :=
    (hzBound.le.trans (by omega)).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have hmag := jamCombine_toNat (productSign == zSign)
    (isExactShift zMantissa (productScale - zProductScale))
    product (shiftRightWord zMantissa (productScale - zProductScale))
    zMantissa.toNat t hq hexact (by rw [hq]; omega)
    (fun _ => ⟨by rw [hq]; omega, hzLe⟩)
  have hscaleSplit : productScale.toNat = zProductScale.toNat + t := by omega
  have hpowT : 2 ^ (46 + t) ≤ product.toNat * 2 ^ t := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_right _ hproductLowerNat
  have hz45 : zMantissa.toNat ≤ 2 ^ (45 + t) :=
    hzBound.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hpow45 : 2 ^ (45 + t) * 2 = 2 ^ (46 + t) := by
    rw [show 46 + t = (45 + t) + 1 by omega, Nat.pow_succ]
  have hbound : 2 ^ (45 + t) ≤
      (if (productSign == zSign) = true then product.toNat * 2 ^ t + zMantissa.toNat
        else product.toNat * 2 ^ t - zMantissa.toNat) := by
    split <;> omega
  have hlhs : roundProduct productSign
        (jamCombine (productSign == zSign)
          (isExactShift zMantissa (productScale - zProductScale))
          product (shiftRightWord zMantissa (productScale - zProductScale)))
        productScale =
      roundDyadic
        { negative := productSign
          significand :=
            if (productSign == zSign) = true then product.toNat * 2 ^ t + zMantissa.toNat
            else product.toNat * 2 ^ t - zMantissa.toNat
          exponent := Int.ofNat zProductScale.toNat - 298 } := by
    rw [roundProduct_eq_roundDyadic _ _ _ hproductScaleBound, hmag, hscaleSplit]
    exact roundDyadic_shiftRightJam _ _ _ _ (by
      have hpositive := (Nat.two_pow_pos _).trans_le hbound
      have := (Nat.le_log2 hpositive.ne').2 hbound
      omega)
  have halign := addDyadic_alignLeftOffset 298 productSign zSign product.toNat zMantissa.toNat
    productScale.toNat zProductScale.toNat hproductNe hzNe hltNat
  norm_num at halign
  rw [hlhs]
  simp only [Int.ofNat_eq_natCast]
  rw [halign, ← ht, Nat.shiftLeft_eq]
  have hproductShiftedNe : product.toNat * 2 ^ t ≠ 0 := by positivity
  by_cases hsign : productSign = zSign
  · subst hsign
    rw [addDyadic_sameSign_sameExponent _ _ _ _ hproductShiftedNe hzNe]
    simp only [beq_self_eq_true, ite_true]
  · have hsignBeq : (productSign == zSign) = false := by simpa using hsign
    rw [addDyadic_oppositeSign_sameExponent_largeLeft _ _ _ _ _ hproductShiftedNe hzNe hsign
      (by omega)]
    simp only [hsignBeq, Bool.false_eq_true, ite_false]

/--
Word-level fused multiply-add equals the exact-dyadic `fmaFinite?`.
-/
theorem fmaFiniteWord_eq (x y z : Value) :
    fmaFiniteWord? x y z = fmaFinite? x y z := by
  unfold fmaFiniteWord? fmaFinite?
  rw [toDyadic_eq_finiteComponents x, toDyadic_eq_finiteComponents y,
    toDyadic_eq_finiteComponents z]
  dsimp only
  simp only [Bool.or_eq_true, beq_iff_eq]
  set xExponent := expField (toUInt32 x) with hxExponent
  set yExponent := expField (toUInt32 y) with hyExponent
  set zExponent := expField (toUInt32 z) with hzExponent
  set xFraction := fracField (toUInt32 x) with hxFraction
  set yFraction := fracField (toUInt32 y) with hyFraction
  set zFraction := fracField (toUInt32 z) with hzFraction
  set xMantissa := finiteMantissa xExponent xFraction with hxMantissa
  set yMantissa := finiteMantissa yExponent yFraction with hyMantissa
  set zMantissa := finiteMantissa zExponent zFraction with hzMantissa
  set xScale := finiteScale xExponent with hxScale
  set yScale := finiteScale yExponent with hyScale
  set zScale := finiteScale zExponent with hzScale
  set product : UInt64 := xMantissa * yMantissa with hproductDef
  set productScale : UInt64 := xScale + yScale with hproductScaleDef
  set zProductScale : UInt64 := zScale + 149 with hzProductScaleDef
  by_cases hxExceptional : xExponent = 0xff
  · simp [hxExceptional]
  by_cases hyExceptional : yExponent = 0xff
  · simp [hxExceptional, hyExceptional]
  by_cases hzExceptional : zExponent = 0xff
  · simp [hxExceptional, hyExceptional, hzExceptional]
  by_cases hproductZero : product = 0
  · simp [hxExceptional, hyExceptional, hzExceptional, hproductZero]
  by_cases hzZero : zMantissa = 0
  · simp [hxExceptional, hyExceptional, hzExceptional, hproductZero, hzZero]
  have hxZero : xMantissa ≠ 0 := by
    intro h
    apply hproductZero
    rw [hproductDef, h]
    simp
  have hyZero : yMantissa ≠ 0 := by
    intro h
    apply hproductZero
    rw [hproductDef, h]
    simp
  simp only [hxExceptional, hyExceptional, hzExceptional, hxZero, hyZero, hzZero,
    hproductZero, or_false, ite_false]
  have hxMantissaLt :=
    finiteMantissa_lt_of_components x hxExponent hxFraction hxMantissa
  have hyMantissaLt :=
    finiteMantissa_lt_of_components y hyExponent hyFraction hyMantissa
  have hzMantissaLt :=
    finiteMantissa_lt_of_components z hzExponent hzFraction hzMantissa
  have hproductNatBound :
      xMantissa.toNat * yMantissa.toNat < 2 ^ 48 := by
    norm_num at hxMantissaLt hyMantissaLt ⊢
    nlinarith
  have hproductToNat :
      product.toNat = xMantissa.toNat * yMantissa.toNat := by
    rw [hproductDef, UInt64.toNat_mul]
    apply Nat.mod_eq_of_lt
    exact lt_trans hproductNatBound (by norm_num)
  have hproductBound : product.toNat < 2 ^ 48 := by
    rw [hproductToNat]
    exact hproductNatBound
  have hxScaleLe :=
    finiteScale_le_of_components x hxExponent hxScale hxExceptional
  have hyScaleLe :=
    finiteScale_le_of_components y hyExponent hyScale hyExceptional
  have hzScaleLe :=
    finiteScale_le_of_components z hzExponent hzScale hzExceptional
  have hproductScaleToNat :
      productScale.toNat = xScale.toNat + yScale.toNat := by
    rw [hproductScaleDef, UInt64.toNat_add]
    apply Nat.mod_eq_of_lt
    omega
  have hzProductScaleToNat :
      zProductScale.toNat = zScale.toNat + 149 := by
    rw [hzProductScaleDef, UInt64.toNat_add]
    rw [show (149 : UInt64).toNat = 149 by decide]
    apply Nat.mod_eq_of_lt
    omega
  have hproductScaleLe : productScale.toNat ≤ 506 := by
    rw [hproductScaleToNat]
    omega
  have hzProductScaleLe : zProductScale.toNat ≤ 506 := by
    rw [hzProductScaleToNat]
    omega
  have hproductExponent :
      Int.ofNat productScale.toNat - 298 =
        (Int.ofNat xScale.toNat - 149) +
          (Int.ofNat yScale.toNat - 149) := by
    rw [hproductScaleToNat]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    omega
  have hzExponentValue :
      Int.ofNat zProductScale.toNat - 298 =
        Int.ofNat zScale.toNat - 149 := by
    rw [hzProductScaleToNat]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_ofNat]
    omega
  by_cases hscale : productScale ≤ zProductScale
  · rw [ite_eq_left hscale]
    by_cases hshift : zProductScale - productScale ≤ 39
    · rw [ite_eq_left hshift]
      have hround := roundFmaAlignedRight_eq
        (signBit (toUInt32 x) ^^ signBit (toUInt32 y))
        (signBit (toUInt32 z))
        product zMantissa productScale zProductScale
        hproductZero hzZero hproductBound hzMantissaLt hproductScaleLe hscale hshift
      rw [hproductToNat, hproductExponent, hzExponentValue] at hround
      exact congrArg (fun bits => some (ofUInt32 bits)) hround
    · rw [ite_eq_right hshift]
      by_cases hfar : 48 < zProductScale - productScale
      · by_cases hsign :
          (signBit (toUInt32 x) ^^ signBit (toUInt32 y)) =
            signBit (toUInt32 z)
        · have hcondition :
              (decide (48 < zProductScale - productScale) &&
                ((signBit (toUInt32 x) ^^ signBit (toUInt32 y)) ==
                  signBit (toUInt32 z))) = true := by
            simp [hfar, hsign]
          rw [ite_eq_left hcondition]
          have hscaleNat : productScale.toNat ≤ zProductScale.toNat :=
            UInt64.le_iff_toNat_le.mp hscale
          have hshiftToNat :
              (zProductScale - productScale).toNat =
                zProductScale.toNat - productScale.toNat := by
            rw [UInt64.toNat_sub_of_le zProductScale productScale hscale]
          have hfarNat :
              48 < zProductScale.toNat - productScale.toNat := by
            rw [← hshiftToNat]
            have h := UInt64.lt_iff_toNat_lt.mp hfar
            simpa using h
          have hproductNatNonzero : product.toNat ≠ 0 := by
            simpa [← UInt64.toNat_inj] using hproductZero
          have hzNatNonzero : zMantissa.toNat ≠ 0 := by
            simpa [← UInt64.toNat_inj] using hzZero
          have hzShiftedNonzero :
              zMantissa.toNat <<<
                  (zProductScale.toNat - productScale.toNat) ≠ 0 := by
            simp [Nat.shiftLeft_eq, hzNatNonzero]
          have hzMantissaValue :
              zMantissa =
                finiteMantissa
                  (expField (toUInt32 z)) (fracField (toUInt32 z)) := by
            rw [hzMantissa, hzExponent, hzFraction]
          have hzScaleValue :
              zScale = finiteScale (expField (toUInt32 z)) := by
            rw [hzScale, hzExponent]
          have hzActualFinite :
              expField (toUInt32 z) ≠ 0xff := by
            rw [← hzExponent]
            exact hzExceptional
          have hscaleValue :
              productScale.toNat +
                  (zProductScale.toNat - productScale.toNat) =
                (finiteScale (expField (toUInt32 z))).toNat + 149 := by
            rw [← hzScaleValue, ← hzProductScaleToNat]
            omega
          have halign := addDyadic_alignRightOffset 298
            (signBit (toUInt32 x) ^^ signBit (toUInt32 y))
            (signBit (toUInt32 z))
            product.toNat zMantissa.toNat
            productScale.toNat zProductScale.toNat
            hproductNatNonzero hzNatNonzero hscaleNat
          norm_num at halign
          have hround :
              roundDyadic
                  (Model.addDyadic
                    { negative :=
                        signBit (toUInt32 x) ^^ signBit (toUInt32 y)
                      significand := product.toNat
                      exponent := Int.ofNat productScale.toNat - 298 }
                    { negative := signBit (toUInt32 z)
                      significand := zMantissa.toNat
                      exponent := Int.ofNat zProductScale.toNat - 298 }) =
                toUInt32 z := by
            simp only [Int.ofNat_eq_natCast] at halign ⊢
            rw [halign, hsign]
            rw [addDyadic_sameSign_sameExponent
              (signBit (toUInt32 z)) product.toNat
              (zMantissa.toNat <<<
                (zProductScale.toNat - productScale.toNat))
              ((productScale.toNat : Int) - 298)
              hproductNatNonzero hzShiftedNonzero, Nat.add_comm product.toNat]
            rw [hzMantissaValue]
            exact roundFmaFarAddValue z product.toNat productScale.toNat
              (zProductScale.toNat - productScale.toNat)
              hproductBound hzActualFinite
              (by simpa [hzMantissaValue] using hzZero)
              hfarNat hscaleValue
          rw [hproductToNat, hproductExponent, hzExponentValue] at hround
          have hresult :
              ofUInt32
                  (roundDyadic
                    (Model.addDyadic
                      { negative :=
                          signBit (toUInt32 x) ^^ signBit (toUInt32 y)
                        significand := xMantissa.toNat * yMantissa.toNat
                        exponent :=
                          (Int.ofNat xScale.toNat - 149) +
                            (Int.ofNat yScale.toNat - 149) }
                      { negative := signBit (toUInt32 z)
                        significand := zMantissa.toNat
                        exponent := Int.ofNat zScale.toNat - 149 })) =
                z := by
            rw [hround]
            exact ofUInt32_toUInt32 z
          exact congrArg some hresult.symm
        · have hcondition :
              ¬(decide (48 < zProductScale - productScale) &&
                ((signBit (toUInt32 x) ^^ signBit (toUInt32 y)) ==
                  signBit (toUInt32 z))) = true := by
            simpa [hfar] using hsign
          rw [ite_eq_right hcondition]
          by_cases hzNormal : 0x800000 ≤ zMantissa
          · rw [ite_eq_left hzNormal]
            have hround := roundFmaJamAbove_eq
              (signBit (toUInt32 x) ^^ signBit (toUInt32 y)) (signBit (toUInt32 z))
              product zMantissa productScale zProductScale
              hproductZero hproductBound hzNormal hzMantissaLt hzProductScaleLe hscale hshift
            rw [hproductToNat, hproductExponent, hzExponentValue] at hround
            exact congrArg (fun bits => some (ofUInt32 bits)) hround
          · rw [ite_eq_right hzNormal]
            unfold fmaExactFinite?
            rw [hproductToNat, hproductExponent, hzExponentValue]
      · have hcondition :
            ¬(decide (48 < zProductScale - productScale) &&
              ((signBit (toUInt32 x) ^^ signBit (toUInt32 y)) ==
                signBit (toUInt32 z))) = true := by
          simp [hfar]
        rw [ite_eq_right hcondition]
        by_cases hzNormal : 0x800000 ≤ zMantissa
        · rw [ite_eq_left hzNormal]
          have hround := roundFmaJamAbove_eq
            (signBit (toUInt32 x) ^^ signBit (toUInt32 y)) (signBit (toUInt32 z))
            product zMantissa productScale zProductScale
            hproductZero hproductBound hzNormal hzMantissaLt hzProductScaleLe hscale hshift
          rw [hproductToNat, hproductExponent, hzExponentValue] at hround
          exact congrArg (fun bits => some (ofUInt32 bits)) hround
        · rw [ite_eq_right hzNormal]
          unfold fmaExactFinite?
          rw [hproductToNat, hproductExponent, hzExponentValue]
  · rw [ite_eq_right hscale]
    by_cases hshift : productScale - zProductScale ≤ 15
    · rw [ite_eq_left hshift]
      have hround := roundFmaAlignedLeft_eq
        (signBit (toUInt32 x) ^^ signBit (toUInt32 y))
        (signBit (toUInt32 z))
        product zMantissa productScale zProductScale
        hproductZero hzZero hproductBound hzMantissaLt hzProductScaleLe hscale hshift
      rw [hproductToNat, hproductExponent, hzExponentValue] at hround
      exact congrArg (fun bits => some (ofUInt32 bits)) hround
    · rw [ite_eq_right hshift]
      by_cases hproductNormal : 0x400000000000 ≤ product
      · rw [ite_eq_left hproductNormal]
        have hround := roundFmaJamBelow_eq
          (signBit (toUInt32 x) ^^ signBit (toUInt32 y)) (signBit (toUInt32 z))
          product zMantissa productScale zProductScale
          hproductNormal hproductBound hzZero hzMantissaLt hproductScaleLe hscale hshift
        rw [hproductToNat, hproductExponent, hzExponentValue] at hround
        exact congrArg (fun bits => some (ofUInt32 bits)) hround
      · rw [ite_eq_right hproductNormal]
        unfold fmaExactFinite?
        rw [hproductToNat, hproductExponent, hzExponentValue]

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
