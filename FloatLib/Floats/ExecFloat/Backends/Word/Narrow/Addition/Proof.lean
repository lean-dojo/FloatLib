/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.AddDyadic.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Addition.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Finite.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Packing
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.SignedMagnitude.Proof
import FloatLib.Floats.Formats.BinaryInterchange.ModelRounding.Proof
import FloatLib.Floats.ExecFloat.Backends.Word.Small.Core.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Base.Proof

/-!
# Correctness of native-word addition for generic binary32

This `UInt64` addition kernel equals its exact-dyadic finite specification. For exponent gaps of at
most 39, alignment and signed addition are exact in one word, while a larger gap means the smaller
operand can't change the nearest-even rounding of the larger one, even at a binade boundary.
`Addition.Runtime` can be imported without the alignment, packing, and rounding proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

private theorem roundAddMagnitudes_eq_roundDyadic
    (xSign ySign : Bool) (xMagnitude yMagnitude scale : UInt64)
    (hx : xMagnitude ≠ 0) (hy : yMagnitude ≠ 0)
    (hsum : xMagnitude.toNat + yMagnitude.toNat < 2 ^ 64)
    (hscale : scale.toNat ≤ 253) :
    roundProduct
        (FloatLib.Numerics.FixedWord.addSignedMagnitudes
          xSign ySign xMagnitude yMagnitude).1
        (FloatLib.Numerics.FixedWord.addSignedMagnitudes
          xSign ySign xMagnitude yMagnitude).2
        (scale + 149) =
      roundDyadic
        (Model.addDyadic
          { negative := xSign
            significand := xMagnitude.toNat
            exponent := Int.ofNat scale.toNat - 149 }
          { negative := ySign
            significand := yMagnitude.toNat
            exponent := Int.ofNat scale.toNat - 149 }) := by
  have hscaleAdd :
      (scale + (149 : UInt64)).toNat = scale.toNat + 149 := by
    rw [UInt64.toNat_add]
    rw [show (149 : UInt64).toNat = 149 by decide]
    apply Nat.mod_eq_of_lt
    omega
  have hscaleBound : (scale + (149 : UInt64)).toNat ≤ 506 := by
    rw [hscaleAdd]
    omega
  have hround := roundAddMagnitudesAtScale_eq_roundDyadic
    xSign ySign xMagnitude yMagnitude (scale + 149)
    hx hy (fun _ => hsum) hscaleBound
  rw [hscaleAdd] at hround
  have hexponent :
      Int.ofNat (scale.toNat + 149) - 298 =
        Int.ofNat scale.toNat - 149 := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_ofNat]
    omega
  simpa only [hexponent] using hround

private theorem addDyadic_alignRight
    (xSign ySign : Bool) (xMagnitude yMagnitude xScale yScale : Nat)
    (hx : xMagnitude ≠ 0)
    (hscale : xScale ≤ yScale) :
    Model.addDyadic
        { negative := xSign
          significand := xMagnitude
          exponent := Int.ofNat xScale - 149 }
        { negative := ySign
          significand := yMagnitude
          exponent := Int.ofNat yScale - 149 } =
      Model.addDyadic
        { negative := xSign
          significand := xMagnitude
          exponent := Int.ofNat xScale - 149 }
        { negative := ySign
          significand := yMagnitude <<< (yScale - xScale)
          exponent := Int.ofNat xScale - 149 } := by
  have h := addDyadic_alignRightOffset 149 xSign ySign
    xMagnitude yMagnitude xScale yScale hx hscale
  norm_num at h
  exact h

private theorem addDyadic_alignLeft
    (xSign ySign : Bool) (xMagnitude yMagnitude xScale yScale : Nat)
    (hy : yMagnitude ≠ 0)
    (hscale : yScale < xScale) :
    Model.addDyadic
        { negative := xSign
          significand := xMagnitude
          exponent := Int.ofNat xScale - 149 }
        { negative := ySign
          significand := yMagnitude
          exponent := Int.ofNat yScale - 149 } =
      Model.addDyadic
        { negative := xSign
          significand := xMagnitude <<< (xScale - yScale)
          exponent := Int.ofNat yScale - 149 }
        { negative := ySign
          significand := yMagnitude
          exponent := Int.ofNat yScale - 149 } := by
  have h := addDyadic_alignLeftOffset 149 xSign ySign
    xMagnitude yMagnitude xScale yScale hy hscale
  norm_num at h
  exact h

private theorem roundDyadic_shiftLeft_add_small
    (sign : Bool) (small large smallScale gap : Nat)
    (hsmall : small < 2 ^ 24)
    (hlargeLow : 2 ^ 23 ≤ large)
    (hlargeHigh : large < 2 ^ 24)
    (hgap : 39 < gap)
    (hscale : smallScale + gap ≤ 253) :
    roundDyadic {
        negative := sign
        significand := (large <<< gap) + small
        exponent := Int.ofNat smallScale - 149 } =
      mkBits sign (smallScale + gap + 1) (large - 2 ^ 23) := by
  have hsmallHalf : small < 2 ^ (gap - 1) :=
    hsmall.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  rw [roundDyadic_shiftLeft_add_of_lt_half sign small large gap
    (Int.ofNat smallScale - 149) hlargeLow hlargeHigh hsmallHalf
    (by simp only [Int.ofNat_eq_natCast]; omega)
    (by simp only [Int.ofNat_eq_natCast]; omega)]
  congr 1
  simp only [Int.ofNat_eq_natCast]
  omega

private theorem roundDyadic_shiftLeft_sub_small
    (sign : Bool) (small large smallScale gap : Nat)
    (hsmallPos : 0 < small)
    (hsmall : small < 2 ^ 24)
    (hlargeLow : 2 ^ 23 ≤ large)
    (hlargeHigh : large < 2 ^ 24)
    (hgap : 39 < gap)
    (hscale : smallScale + gap ≤ 253) :
    roundDyadic {
        negative := sign
        significand := (large <<< gap) - small
        exponent := Int.ofNat smallScale - 149 } =
      mkBits sign (smallScale + gap + 1) (large - 2 ^ 23) := by
  have hgapPos : 0 < gap := by omega
  have hsmallGap : small < 2 ^ gap := by
    exact hsmall.trans_le <|
      Nat.pow_le_pow_right (by decide) (by omega)
  have hsmallHalf : small < Model.pow2 (gap - 1) := by
    rw [Model.pow2_eq_two_pow]
    exact hsmall.trans_le <|
      Nat.pow_le_pow_right (by decide) (by omega)
  by_cases hlargeMin : large = 2 ^ 23
  · subst large
    have htop :
        2 ^ (23 + gap) =
          2 ^ (22 + gap) + 2 ^ (22 + gap) := by
      rw [show 23 + gap = (22 + gap) + 1 by omega, pow_succ]
      ring
    have hcombined :
        (2 ^ 23 <<< gap) - small =
          2 ^ (23 + gap) - small := by
      rw [Nat.shiftLeft_eq, pow_add]
    have hsmallBase : small ≤ 2 ^ (22 + gap) := by
      exact hsmall.le.trans <|
        Nat.pow_le_pow_right (by decide) (by omega)
    have hlower :
        2 ^ (22 + gap) ≤ (2 ^ 23 <<< gap) - small := by
      rw [hcombined, htop]
      omega
    have hupper :
        (2 ^ 23 <<< gap) - small < 2 ^ ((22 + gap) + 1) := by
      rw [hcombined, show (22 + gap) + 1 = 23 + gap by omega]
      exact Nat.sub_lt (Nat.pow_pos (by decide)) hsmallPos
    have hcombinedPos : 0 < (2 ^ 23 <<< gap) - small :=
      lt_of_lt_of_le (Nat.pow_pos (by decide)) hlower
    have hcombinedNe : (2 ^ 23 <<< gap) - small ≠ 0 :=
      Nat.ne_of_gt hcombinedPos
    have hleading :
        ((2 ^ 23 <<< gap) - small).log2 = 22 + gap :=
      (Nat.log2_eq_iff hcombinedNe).2 ⟨hlower, hupper⟩
    have hshiftPos : 0 < gap - 1 := by omega
    have hsmallHalf' :
        small < Model.pow2 ((gap - 1) - 1) := by
      rw [Model.pow2_eq_two_pow]
      exact hsmall.trans_le <|
        Nat.pow_le_pow_right (by decide) (by omega)
    have hmantissa :
        (2 ^ 23 <<< gap) - small =
          (2 ^ 24 <<< (gap - 1)) - small := by
      congr 1
      simp only [Nat.shiftLeft_eq]
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have hround :
        Numerics.roundShiftRightEven
            ((2 ^ 23 <<< gap) - small) (gap - 1) =
          2 ^ 24 := by
      rw [hmantissa]
      exact Model.roundShiftRightEven_shiftLeft_sub_of_lt_half
        (2 ^ 24) small (gap - 1) hsmallHalf'
    rw [roundDyadic_normal_carry_of_log2 sign _ (22 + gap) _ hcombinedNe hleading (by omega)
      (by simp only [Int.ofNat_eq_natCast]; omega) (by simp only [Int.ofNat_eq_natCast]; omega)
      (by rw [show 22 + gap - 23 = gap - 1 by omega]; exact hround)]
    congr 1
    simp only [Int.ofNat_eq_natCast]
    omega
  · have hlargeStrict : 2 ^ 23 < large := by omega
    have hcombinedPos : 0 < (large <<< gap) - small := by
      rw [Nat.shiftLeft_eq]
      have hpowPos : 0 < 2 ^ gap := Nat.pow_pos (by decide)
      have hlargeMul : 2 ^ gap ≤ large * 2 ^ gap := by
        nlinarith
      omega
    have hcombinedNe : (large <<< gap) - small ≠ 0 :=
      Nat.ne_of_gt hcombinedPos
    have hlower : 2 ^ (23 + gap) ≤ (large <<< gap) - small := by
      calc
        2 ^ (23 + gap) = 2 ^ 23 * 2 ^ gap := by rw [pow_add]
        _ ≤ (large - 1) * 2 ^ gap :=
          Nat.mul_le_mul_right _ (by omega)
        _ = large * 2 ^ gap - 2 ^ gap := by
          rw [Nat.sub_mul]
          simp
        _ ≤ large * 2 ^ gap - small :=
          Nat.sub_le_sub_left hsmallGap.le _
        _ = (large <<< gap) - small := by rw [Nat.shiftLeft_eq]
    have hupper : (large <<< gap) - small < 2 ^ ((23 + gap) + 1) := by
      calc
        (large <<< gap) - small ≤ large <<< gap := Nat.sub_le _ _
        _ = large * 2 ^ gap := by rw [Nat.shiftLeft_eq]
        _ < 2 ^ 24 * 2 ^ gap :=
          Nat.mul_lt_mul_of_pos_right hlargeHigh
            (Nat.pow_pos (by decide))
        _ = 2 ^ (24 + gap) := by rw [pow_add]
        _ = 2 ^ ((23 + gap) + 1) := by congr 1; omega
    have hleading :
        ((large <<< gap) - small).log2 = 23 + gap :=
      (Nat.log2_eq_iff hcombinedNe).2 ⟨hlower, hupper⟩
    have hlargePos : 0 < large :=
      lt_of_lt_of_le (by norm_num) hlargeLow
    have hround :
        Numerics.roundShiftRightEven ((large <<< gap) - small) gap = large :=
      Model.roundShiftRightEven_shiftLeft_sub_of_lt_half
        large small gap hsmallHalf
    rw [roundDyadic_normal_of_log2 sign _ (23 + gap) _ large hcombinedNe hleading (by omega)
      (by simp only [Int.ofNat_eq_natCast]; omega) (by simp only [Int.ofNat_eq_natCast]; omega)
      (by rw [Nat.add_sub_cancel_left]; exact hround) hlargeHigh.ne]
    congr 1
    simp only [Int.ofNat_eq_natCast]
    omega

/--
The far case of finite addition. When the exponent gap exceeds 39 bits the smaller operand lies
strictly below half an ulp of the larger one, so nearest-even rounding of the exact sum returns the
larger operand `z` whatever the signs are.
-/
private theorem roundDyadic_addDyadic_far
    (z : Value) {exponent fraction : UInt32} {mantissa scale : UInt64}
    (hexponent : exponent = expField (toUInt32 z))
    (hfraction : fraction = fracField (toUInt32 z))
    (hmantissa : mantissa = finiteMantissa exponent fraction)
    (hscale : scale = finiteScale exponent)
    (hfinite : exponent ≠ 0xff)
    (smallSign : Bool) (small smallScale : Nat)
    (hsmall : small ≠ 0) (hsmallLt : small < 2 ^ 24)
    (hgap : smallScale + 39 < scale.toNat) :
    roundDyadic (Model.addDyadic
      { negative := smallSign, significand := small, exponent := Int.ofNat smallScale - 149 }
      { negative := signBit (toUInt32 z), significand := mantissa.toNat
        exponent := Int.ofNat scale.toNat - 149 }) = toUInt32 z := by
  subst hexponent hfraction hmantissa hscale
  have hscaleLe := finiteScale_le_of_components z rfl rfl hfinite
  have hexponentNonzero : expField (toUInt32 z) ≠ 0 := by
    intro h
    rw [finiteScale_toNat, ite_eq_left h] at hgap
    omega
  have hexponentNat :
      (expField (toUInt32 z)).toNat =
        smallScale + ((finiteScale (expField (toUInt32 z))).toNat - smallScale) + 1 := by
    have h := finiteScale_toNat (expField (toUInt32 z))
    rw [ite_eq_right hexponentNonzero] at h
    have : (expField (toUInt32 z)).toNat ≠ 0 := fun h0 =>
      hexponentNonzero (UInt32.toNat_inj.mp (by simpa using h0))
    omega
  obtain ⟨hlargeLow, hlargeHigh, hfractionValue⟩ :=
    finiteMantissa_bounds _ _ hexponentNonzero (fracField_lt z)
  have hmantissaNonzero :
      (finiteMantissa (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat ≠ 0 := by
    omega
  set gap := (finiteScale (expField (toUInt32 z))).toNat - smallScale with hgapDef
  have hshiftedNonzero :
      (finiteMantissa (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat <<< gap ≠ 0 := by
    simp [Nat.shiftLeft_eq, hmantissaNonzero]
  rw [addDyadic_alignRight _ _ _ _ _ _ hsmall (by omega)]
  by_cases hsign : smallSign = signBit (toUInt32 z)
  · subst hsign
    rw [addDyadic_sameSign_sameExponent _ _ _ _ hsmall hshiftedNonzero, Nat.add_comm small,
      roundDyadic_shiftLeft_add_small _ small _ smallScale gap hsmallLt hlargeLow hlargeHigh
        (by omega) (by omega), ← hexponentNat, hfractionValue]
    exact mkBits_fields (toUInt32 z)
  · have hlt :
        small < (finiteMantissa (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat <<< gap := by
      rw [Nat.shiftLeft_eq]
      calc small < 2 ^ 24 := hsmallLt
        _ ≤ 2 ^ gap := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ _ * 2 ^ gap := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hmantissaNonzero)
    rw [Model.addDyadic_oppositeSign_sameExponent_largeRight _ _ _ _ _ hsign hlt,
      roundDyadic_shiftLeft_sub_small _ small _ smallScale gap
        (Nat.pos_of_ne_zero hsmall) hsmallLt hlargeLow hlargeHigh (by omega) (by omega),
      ← hexponentNat, hfractionValue]
    exact mkBits_fields (toUInt32 z)

/--
Word-level finite addition equals the exact-dyadic `addFinite?`.

Non-finite operands give `none` on both sides, and zero operands take the exact-dyadic kernel.
Nonzero operands split on whether the exponent gap is at most 39.
-/
theorem addFiniteWord_eq (x y : Value) :
    addFiniteWord? x y = addFinite? x y := by
  unfold addFiniteWord? addFinite?
  rw [toDyadic_eq_finiteComponents x, toDyadic_eq_finiteComponents y]
  dsimp only
  simp only [Bool.or_eq_true, beq_iff_eq]
  set xExponent := expField (toUInt32 x) with hxExponent
  set yExponent := expField (toUInt32 y) with hyExponent
  set xFraction := fracField (toUInt32 x) with hxFraction
  set yFraction := fracField (toUInt32 y) with hyFraction
  set xMantissa : UInt64 := finiteMantissa xExponent xFraction with hxMantissa
  set yMantissa : UInt64 := finiteMantissa yExponent yFraction with hyMantissa
  set xScale : UInt64 := finiteScale xExponent with hxScale
  set yScale : UInt64 := finiteScale yExponent with hyScale
  by_cases hxExceptional : xExponent = 0xff
  · simp [hxExceptional]
  by_cases hyExceptional : yExponent = 0xff
  · simp [hxExceptional, hyExceptional]
  by_cases hxZero : xMantissa = 0
  · simp [hxExceptional, hyExceptional, hxZero]
  by_cases hyZero : yMantissa = 0
  · simp [hxExceptional, hyExceptional, hxZero, hyZero]
  have hxNatNonzero : xMantissa.toNat ≠ 0 :=
    (FloatLib.Numerics.FixedWord.uint64_toNat_eq_zero xMantissa).not.mpr hxZero
  have hyNatNonzero : yMantissa.toNat ≠ 0 :=
    (FloatLib.Numerics.FixedWord.uint64_toNat_eq_zero yMantissa).not.mpr hyZero
  simp only [hxExceptional, hyExceptional, hxZero, hyZero, or_self, ite_false]
  obtain ⟨hxMantissaLt, hxScaleLe⟩ :=
    finiteComponents_bounds x hxExponent hxFraction hxMantissa hxScale hxExceptional
  obtain ⟨hyMantissaLt, hyScaleLe⟩ :=
    finiteComponents_bounds y hyExponent hyFraction hyMantissa hyScale hyExceptional
  by_cases hscale : xScale ≤ yScale
  · have hscaleNat := UInt64.le_iff_toNat_le.mp hscale
    have hshiftNat := UInt64.toNat_sub_of_le yScale xScale hscale
    rw [ite_eq_left hscale]
    by_cases hshift : yScale - xScale ≤ 39
    · obtain ⟨hshifted, hnonzero, hsum⟩ := NativeSmallWord.shiftLeft_add_fits yMantissa xMantissa
        (yScale - xScale) 24 hyMantissaLt hyNatNonzero (hxMantissaLt.trans (by norm_num))
        (by have := UInt64.le_iff_toNat_le.mp hshift; simp at this; omega)
      rw [ite_eq_left hshift, roundAddMagnitudes_eq_roundDyadic _ _ _ _ _ hxZero hnonzero
        (by omega) hxScaleLe, hshifted, hshiftNat,
        ← addDyadic_alignRight _ _ _ _ _ _ hxNatNonzero hscaleNat]
    · have hgap : xScale.toNat + 39 < yScale.toNat := by
        have h : ¬ (yScale - xScale).toNat ≤ 39 := fun hle =>
          hshift (UInt64.le_iff_toNat_le.mpr (by simpa using hle))
        omega
      rw [ite_eq_right hshift, roundDyadic_addDyadic_far y hyExponent hyFraction hyMantissa hyScale
        hyExceptional _ _ _ hxNatNonzero hxMantissaLt hgap]
      simp
  · have hscaleNat : yScale.toNat < xScale.toNat := by
      have h : ¬ xScale.toNat ≤ yScale.toNat := fun hle => hscale (UInt64.le_iff_toNat_le.mpr hle)
      omega
    have hscale' : yScale ≤ xScale := UInt64.le_iff_toNat_le.mpr hscaleNat.le
    have hshiftNat := UInt64.toNat_sub_of_le xScale yScale hscale'
    rw [ite_eq_right hscale]
    by_cases hshift : xScale - yScale ≤ 39
    · obtain ⟨hshifted, hnonzero, hsum⟩ := NativeSmallWord.shiftLeft_add_fits xMantissa yMantissa
        (xScale - yScale) 24 hxMantissaLt hxNatNonzero (hyMantissaLt.trans (by norm_num))
        (by have := UInt64.le_iff_toNat_le.mp hshift; simp at this; omega)
      rw [ite_eq_left hshift, roundAddMagnitudes_eq_roundDyadic _ _ _ _ _ hnonzero hyZero hsum
        hyScaleLe, hshifted, hshiftNat, ← addDyadic_alignLeft _ _ _ _ _ _ hyNatNonzero hscaleNat]
    · have hgap : yScale.toNat + 39 < xScale.toNat := by
        have h : ¬ (xScale - yScale).toNat ≤ 39 := fun hle =>
          hshift (UInt64.le_iff_toNat_le.mpr (by simpa using hle))
        omega
      rw [ite_eq_right hshift, Model.addDyadic_comm,
        roundDyadic_addDyadic_far x hxExponent hxFraction
        hxMantissa hxScale hxExceptional _ _ _ hyNatNonzero hyMantissaLt hgap]
      simp

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
