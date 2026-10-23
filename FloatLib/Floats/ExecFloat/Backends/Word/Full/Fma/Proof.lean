/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Core.Proof
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import FloatLib.Kernels.FixedWord.Difference.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Fma.Runtime

import FloatLib.Kernels.FixedWord.LimbRound.Proof
import FloatLib.Floats.ExecFloat.Backends.Generic.ScaleAdd.Proof
import FloatLib.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
import FloatLib.Numerics.ShiftRightJam.Proof

/-!
# Verified scale-aligned binary64 fused multiply-add

On the exact path the addend's scale is at most 62 bits above the product's, so shifting the
addend significand by that difference places it at the product's scale. Their sum or difference
needs at most 116 bits, and two native words hold it exactly before one nearest-even rounding.
An addend below the product, or more than 62 bits above it, is aligned with a sticky bit instead
(`fmaJammed?`), and the jammed magnitude rounds to the same result.

Zero and subnormal operands, exact or deep cancellation, and results outside the normal rounder's
range use the generic finite kernel. Non-finite operands are handled by the outer arithmetic
dispatcher.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord

/-! ## Two-word exact arithmetic -/

private theorem alignFmaAddend_lt (mantissa : UInt64) (shift : Nat)
    (hmantissa : mantissa.toNat < 2 ^ 53) (hshift : shift ≤ 62) :
    mantissa.toNat <<< shift < 2 ^ 115 := by
  rw [Nat.shiftLeft_eq]
  calc mantissa.toNat * 2 ^ shift < 2 ^ 53 * 2 ^ 62 :=
        Nat.mul_lt_mul_of_lt_of_le hmantissa (Nat.pow_le_pow_right (by decide) hshift)
          (Nat.two_pow_pos _)
    _ = 2 ^ 115 := by norm_num

private theorem alignFmaAddend_toNat (mantissa : UInt64) (shift : Nat)
    (hmantissa : mantissa.toNat < 2 ^ 53) (hshift : shift ≤ 62) :
    (alignFmaAddend mantissa shift).toNat = mantissa.toNat <<< shift := by
  unfold alignFmaAddend
  have hvalue : ({ hi := 0, lo := mantissa } : FloatLib.Numerics.FixedWord.UInt128).toNat =
      mantissa.toNat := by
    simp [FloatLib.Numerics.FixedWord.UInt128.toNat]
  have hfit :
      ({ hi := 0, lo := mantissa } : FloatLib.Numerics.FixedWord.UInt128).toNat <<< shift <
        2 ^ 128 := by
    rw [hvalue]
    exact lt_trans (alignFmaAddend_lt mantissa shift hmantissa hshift) (by norm_num)
  rw [FloatLib.Numerics.FixedWord.UInt128.shiftLeft_toNat _ shift (by omega) hfit, hvalue]

private theorem fmaLeading_toNat (magnitude : FloatLib.Numerics.FixedWord.UInt128)
    (hmagnitude : magnitude.toNat ≠ 0)
    (hupper : magnitude.toNat < 2 ^ 116) :
    (fmaLeading magnitude).toNat = magnitude.toNat.log2 := by
  unfold fmaLeading
  rw [UInt64.toNat_ofNat', FloatLib.Numerics.FixedWord.UInt128.log2_toNat]
  apply Nat.mod_eq_of_lt
  have hlog : magnitude.toNat.log2 < 116 := by
    rw [Nat.log2_lt hmagnitude]
    exact hupper
  omega

/-! ## Scale-aligned component semantics -/

private theorem fmaComponents_opposite_aligned_addend_larger
    (alignment : Nat) (xSign ySign zSign : Bool)
    (xExponent yExponent zExponent xMantissa yMantissa zMantissa : Nat)
    (hxExponent : xExponent ≠ 0)
    (hyExponent : yExponent ≠ 0)
    (hzExponent : zExponent ≠ 0)
    (hxMantissa : xMantissa ≠ 0)
    (hyMantissa : yMantissa ≠ 0)
    (hzMantissa : zMantissa ≠ 0)
    (hsign : Bool.xor xSign ySign ≠ zSign)
    (haligned :
      (xExponent - 1) + (yExponent - 1) + alignment =
        (zExponent - 1) + 1074)
    (hlt : xMantissa * yMantissa < zMantissa <<< alignment) :
    FiniteKernel.fmaComponents FloatFormat.binary64
        { sign := xSign
          exponent := xExponent
          mantissa := xMantissa }
        { sign := ySign
          exponent := yExponent
          mantissa := yMantissa }
        { sign := zSign
          exponent := zExponent
          mantissa := zMantissa } =
      FiniteProductRound.round FloatFormat.binary64 zSign
        ((zMantissa <<< alignment) - xMantissa * yMantissa)
        ((xExponent - 1) + (yExponent - 1)) := by
  rw [← FiniteKernel.Internal.fmaComponents_eq]
  unfold FiniteKernel.Internal.fmaComponents
  rw [ite_eq_left (by decide : FloatFormat.binary64.isIEEE = true)]
  unfold FiniteScaleAdd.roundSum
  simp only [FiniteKernel.scale, hxExponent, hyExponent, hzExponent,
    ite_false, hxMantissa, hyMantissa, hzMantissa, mul_eq_zero,
    beq_iff_eq]
  have hproduct : xMantissa * yMantissa ≠ 0 :=
    Nat.mul_ne_zero hxMantissa hyMantissa
  have hscale :
      (xExponent - 1) + (yExponent - 1) ≤
        (zExponent - 1) + FiniteKernel.finiteScaleOffset FloatFormat.binary64 := by
    change
      (xExponent - 1) + (yExponent - 1) ≤
        (zExponent - 1) + 1074
    omega
  simp only [or_self, ite_false]
  rw [ite_eq_left hscale, FiniteScaleAdd.roundAligned_eq, FiniteScaleAdd.roundMagnitudes_comm]
  unfold FiniteScaleAdd.roundMagnitudes
  rw [ite_eq_right (by simpa only [beq_iff_eq] using hsign)]
  have hne :
      xMantissa * yMantissa ≠
        zMantissa <<<
          ((zExponent - 1) +
            FiniteKernel.finiteScaleOffset FloatFormat.binary64 -
            ((xExponent - 1) + (yExponent - 1))) := by
    intro heq
    have hoffset :
        FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 := by
      decide
    rw [hoffset] at heq
    have hshift :
        (zExponent - 1) + 1074 -
            ((xExponent - 1) + (yExponent - 1)) =
          alignment := by
      omega
    rw [hshift] at heq
    omega
  rw [ite_eq_right (by simpa only [beq_iff_eq] using hne)]
  have hoffset :
      FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 := by
    decide
  rw [hoffset]
  have hshift :
      (zExponent - 1) + 1074 -
          ((xExponent - 1) + (yExponent - 1)) =
        alignment := by
    omega
  rw [hshift, ite_eq_left hlt]
  rfl

private theorem fmaComponents_opposite_aligned_product_larger
    (alignment : Nat) (xSign ySign zSign : Bool)
    (xExponent yExponent zExponent xMantissa yMantissa zMantissa : Nat)
    (hxExponent : xExponent ≠ 0)
    (hyExponent : yExponent ≠ 0)
    (hzExponent : zExponent ≠ 0)
    (hxMantissa : xMantissa ≠ 0)
    (hyMantissa : yMantissa ≠ 0)
    (hzMantissa : zMantissa ≠ 0)
    (hsign : Bool.xor xSign ySign ≠ zSign)
    (haligned :
      (xExponent - 1) + (yExponent - 1) + alignment =
        (zExponent - 1) + 1074)
    (hlt : zMantissa <<< alignment < xMantissa * yMantissa) :
    FiniteKernel.fmaComponents FloatFormat.binary64
        { sign := xSign
          exponent := xExponent
          mantissa := xMantissa }
        { sign := ySign
          exponent := yExponent
          mantissa := yMantissa }
        { sign := zSign
          exponent := zExponent
          mantissa := zMantissa } =
      FiniteProductRound.round FloatFormat.binary64
        (Bool.xor xSign ySign)
        (xMantissa * yMantissa - (zMantissa <<< alignment))
        ((xExponent - 1) + (yExponent - 1)) := by
  rw [← FiniteKernel.Internal.fmaComponents_eq]
  unfold FiniteKernel.Internal.fmaComponents
  rw [ite_eq_left (by decide : FloatFormat.binary64.isIEEE = true)]
  unfold FiniteScaleAdd.roundSum
  simp only [FiniteKernel.scale, hxExponent, hyExponent, hzExponent,
    ite_false, hxMantissa, hyMantissa, hzMantissa, mul_eq_zero,
    beq_iff_eq]
  have hproduct : xMantissa * yMantissa ≠ 0 :=
    Nat.mul_ne_zero hxMantissa hyMantissa
  have hscale :
      (xExponent - 1) + (yExponent - 1) ≤
        (zExponent - 1) + FiniteKernel.finiteScaleOffset FloatFormat.binary64 := by
    change
      (xExponent - 1) + (yExponent - 1) ≤
        (zExponent - 1) + 1074
    omega
  simp only [or_self, ite_false]
  rw [ite_eq_left hscale, FiniteScaleAdd.roundAligned_eq, FiniteScaleAdd.roundMagnitudes_comm]
  unfold FiniteScaleAdd.roundMagnitudes
  rw [ite_eq_right (by simpa only [beq_iff_eq] using hsign)]
  have hne :
      xMantissa * yMantissa ≠
        zMantissa <<<
          ((zExponent - 1) +
            FiniteKernel.finiteScaleOffset FloatFormat.binary64 -
            ((xExponent - 1) + (yExponent - 1))) := by
    intro heq
    have hoffset :
        FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 := by
      decide
    rw [hoffset] at heq
    have hshift :
        (zExponent - 1) + 1074 -
            ((xExponent - 1) + (yExponent - 1)) =
          alignment := by
      omega
    rw [hshift] at heq
    omega
  rw [ite_eq_right (by simpa only [beq_iff_eq] using hne)]
  have hoffset :
      FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 := by
    decide
  rw [hoffset]
  have hshift :
      (zExponent - 1) + 1074 -
          ((xExponent - 1) + (yExponent - 1)) =
        alignment := by
    omega
  rw [hshift, ite_eq_right (Nat.not_lt_of_ge hlt.le)]
  rfl

/-! ## Refinement of native product rounding -/

private theorem roundNormalFma_refines
    (sign : Bool) (xExponent yExponent : UInt64)
    (xMantissa yMantissa zMantissa : UInt64) (alignment : Nat) (halignment : alignment ≤ 62)
    (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < 2047)
    (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < 2047)
    (hxMantissa :
      2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53)
    (hyMantissa :
      2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53)
    (hzMantissa :
      2 ^ 52 ≤ zMantissa.toNat ∧ zMantissa.toNat < 2 ^ 53)
    (result : Value)
    (hcarry :
      (FloatLib.Numerics.FixedWord.add128
        (FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa)
        (alignFmaAddend zMantissa alignment)).carry = 0)
    (hresult :
      roundNormalProduct? sign xExponent yExponent
          (FloatLib.Numerics.FixedWord.add128
            (FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa)
            (alignFmaAddend zMantissa alignment)).value
          (fmaLeading
            (FloatLib.Numerics.FixedWord.add128
              (FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa)
              (alignFmaAddend zMantissa alignment)).value) =
        some result) :
    result =
      FiniteProductRound.round FloatFormat.binary64 sign
        (xMantissa.toNat * yMantissa.toNat + (zMantissa.toNat <<< alignment))
        ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let aligned := alignFmaAddend zMantissa alignment
  let sum := FloatLib.Numerics.FixedWord.add128 product aligned
  have hproduct :
      product.toNat = xMantissa.toNat * yMantissa.toNat := by
    simp [product]
  have haligned :
      aligned.toNat = zMantissa.toNat <<< alignment := by
    exact alignFmaAddend_toNat zMantissa alignment hzMantissa.2 halignment
  have hsum :
      sum.value.toNat =
        xMantissa.toNat * yMantissa.toNat + (zMantissa.toNat <<< alignment) := by
    rw [FloatLib.Numerics.FixedWord.add128_value_toNat_of_carry_zero product aligned]
    · rw [hproduct, haligned]
    · simpa [sum, product, aligned] using hcarry
  have hsumLower : 2 ^ 104 ≤ sum.value.toNat := by
    rw [hsum]
    nlinarith
  have hsumUpper : sum.value.toNat < 2 ^ 116 := by
    have hz := alignFmaAddend_lt zMantissa alignment hzMantissa.2 halignment
    rw [hsum]
    have hxy : xMantissa.toNat * yMantissa.toNat < 2 ^ 106 := by
      calc xMantissa.toNat * yMantissa.toNat < 2 ^ 53 * 2 ^ 53 :=
            Nat.mul_lt_mul'' hxMantissa.2 hyMantissa.2
        _ = 2 ^ 106 := by norm_num
    omega
  have hsumNe : sum.value.toNat ≠ 0 := by omega
  have hleading :
      (fmaLeading sum.value).toNat = sum.value.toNat.log2 :=
    fmaLeading_toNat sum.value hsumNe hsumUpper
  have hleadingRange :
      104 ≤ (fmaLeading sum.value).toNat ∧
        (fmaLeading sum.value).toNat ≤ 115 := by
    rw [hleading]
    constructor
    · rw [Nat.le_log2 hsumNe]
      exact hsumLower
    · have hlogLt : sum.value.toNat.log2 < 116 := by
        rw [Nat.log2_lt hsumNe]
        exact hsumUpper
      omega
  rw [← hsum]
  apply roundNormalProduct_refines sign xExponent yExponent sum.value
    (fmaLeading sum.value) hxExponent hyExponent hleading (by omega)
    (by omega) hsumUpper result
  simpa [sum, product, aligned] using hresult

private theorem roundNormalFmaDifference_refines
    (sign : Bool) (xExponent yExponent : UInt64)
    (left right : FloatLib.Numerics.FixedWord.UInt128)
    (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < 2047)
    (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < 2047)
    (hordered : right.toNat < left.toNat)
    (hleftUpper : left.toNat < 2 ^ 116)
    (hleadingMin :
      53 ≤ (fmaLeading (FloatLib.Numerics.FixedWord.UInt128.sub left right)).toNat)
    (result : Value)
    (hresult :
      roundNormalProduct? sign xExponent yExponent
          (FloatLib.Numerics.FixedWord.UInt128.sub left right)
          (fmaLeading (FloatLib.Numerics.FixedWord.UInt128.sub left right)) =
        some result) :
    result =
      FiniteProductRound.round FloatFormat.binary64 sign
        (left.toNat - right.toNat)
        ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
  let magnitude := FloatLib.Numerics.FixedWord.UInt128.sub left right
  have hmagnitude :
      magnitude.toNat = left.toNat - right.toNat := by
    exact FloatLib.Numerics.FixedWord.UInt128.sub_toNat left right hordered.le
  have hmagnitudeNe : magnitude.toNat ≠ 0 := by
    rw [hmagnitude]
    omega
  have hmagnitudeUpper : magnitude.toNat < 2 ^ 116 := by
    rw [hmagnitude]
    omega
  have hleading :
      (fmaLeading magnitude).toNat = magnitude.toNat.log2 :=
    fmaLeading_toNat magnitude hmagnitudeNe hmagnitudeUpper
  have hleadingRange :
      53 ≤ (fmaLeading magnitude).toNat ∧
        (fmaLeading magnitude).toNat ≤ 115 := by
    constructor
    · simpa [magnitude] using hleadingMin
    · rw [hleading]
      have hlogLt : magnitude.toNat.log2 < 116 := by
        rw [Nat.log2_lt hmagnitudeNe]
        exact hmagnitudeUpper
      omega
  have hmagnitudeLower : 2 ^ 52 ≤ magnitude.toNat := by
    have hpow :
        2 ^ magnitude.toNat.log2 ≤ magnitude.toNat :=
      (Nat.le_log2 hmagnitudeNe).mp (le_refl _)
    rw [← hleading] at hpow
    exact le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hpow
  rw [← hmagnitude]
  apply roundNormalProduct_refines sign xExponent yExponent magnitude
    (fmaLeading magnitude) hxExponent hyExponent hleading hleadingRange
    hmagnitudeLower hmagnitudeUpper result
  simpa [magnitude] using hresult

/-! ## Native fast-path refinements -/

private theorem fmaFiniteComponents?_eq_some_of_components (x y z result : Value)
    (hx : expField (toUInt64 x) ≠ 0x7ff)
    (hy : expField (toUInt64 y) ≠ 0x7ff)
    (hz : expField (toUInt64 z) ≠ 0x7ff)
    (hcomponents :
      FiniteKernel.fmaComponents FloatFormat.binary64
          { sign := signBit (toUInt64 x)
            exponent := (expField (toUInt64 x)).toNat
            mantissa :=
              (finiteMantissa (expField (toUInt64 x)) (fracField (toUInt64 x))).toNat }
          { sign := signBit (toUInt64 y)
            exponent := (expField (toUInt64 y)).toNat
            mantissa :=
              (finiteMantissa (expField (toUInt64 y)) (fracField (toUInt64 y))).toNat }
          { sign := signBit (toUInt64 z)
            exponent := (expField (toUInt64 z)).toNat
            mantissa :=
              (finiteMantissa (expField (toUInt64 z)) (fracField (toUInt64 z))).toNat } =
        result) :
    fmaFiniteComponents? x y z = some result := by
  unfold fmaFiniteComponents?
  rw [decode_of_finiteExponent x hx, decode_of_finiteExponent y hy,
    decode_of_finiteExponent z hz]
  simpa only [FiniteKernel.Internal.fmaComponents_eq, Option.some.injEq] using hcomponents

private theorem fmaNormalSameSign_refines
    (x y z result : Value)
    (hresult : fmaNormalSameSign? x y z = some result) :
    fmaFiniteComponents? x y z = some result := by
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let zBits := toUInt64 z
  let xExponent := expField xBits
  let yExponent := expField yBits
  let zExponent := expField zBits
  let xFraction := fracField xBits
  let yFraction := fracField yBits
  let zFraction := fracField zBits
  let xMantissa := finiteMantissa xExponent xFraction
  let yMantissa := finiteMantissa yExponent yFraction
  let zMantissa := finiteMantissa zExponent zFraction
  let productScale := finiteScale xExponent + finiteScale yExponent
  let zProductScale := finiteScale zExponent + 1074
  let productSign := Bool.xor (signBit xBits) (signBit yBits)
  let zSign := signBit zBits
  unfold fmaNormalSameSign? fmaNormalSameSignWord? at hresult
  dsimp only at hresult
  split at hresult
  · simp at hresult
  rename_i hexponents
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hexponents
  obtain ⟨⟨⟨⟨⟨hxZero, hxExceptional⟩, hyZero⟩, hyExceptional⟩, hzZero⟩, hzExceptional⟩ :=
    hexponents
  replace hxZero : xExponent ≠ 0 := hxZero
  replace hxExceptional : xExponent ≠ 0x7ff := hxExceptional
  replace hyZero : yExponent ≠ 0 := hyZero
  replace hyExceptional : yExponent ≠ 0x7ff := hyExceptional
  replace hzZero : zExponent ≠ 0 := hzZero
  replace hzExceptional : zExponent ≠ 0x7ff := hzExceptional
  split at hresult
  · simp at hresult
  rename_i hguard
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or, not_not,
    UInt64.not_lt] at hguard
  obtain ⟨⟨hsign, hlow⟩, hhigh⟩ := hguard
  replace hlow : productScale ≤ zProductScale := hlow
  replace hhigh : zProductScale ≤ productScale + 62 := hhigh
  split at hresult
  · simp at hresult
  rename_i hcarryRaw
  simp only [bne_iff_ne, ne_eq, not_not] at hcarryRaw
  have hxExponentBounds :
      0 < xExponent.toNat ∧ xExponent.toNat < 2047 := by
    simpa [xExponent, xBits] using
      normalExponent_bounds x hxZero hxExceptional
  have hyExponentBounds :
      0 < yExponent.toNat ∧ yExponent.toNat < 2047 := by
    simpa [yExponent, yBits] using
      normalExponent_bounds y hyZero hyExceptional
  have hzExponentBounds :
      0 < zExponent.toNat ∧ zExponent.toNat < 2047 := by
    simpa [zExponent, zBits] using
      normalExponent_bounds z hzZero hzExceptional
  have hxFractionBound : xFraction.toNat < 2 ^ 52 := by
    simpa [xFraction, xBits] using fracField_lt x
  have hyFractionBound : yFraction.toNat < 2 ^ 52 := by
    simpa [yFraction, yBits] using fracField_lt y
  have hzFractionBound : zFraction.toNat < 2 ^ 52 := by
    simpa [zFraction, zBits] using fracField_lt z
  have hxMantissaBounds :
      2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53 := by
    simpa [xMantissa] using
      finiteMantissa_bounds xExponent xFraction hxZero hxFractionBound
  have hyMantissaBounds :
      2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53 := by
    simpa [yMantissa] using
      finiteMantissa_bounds yExponent yFraction hyZero hyFractionBound
  have hzMantissaBounds :
      2 ^ 52 ≤ zMantissa.toNat ∧ zMantissa.toNat < 2 ^ 53 := by
    simpa [zMantissa] using
      finiteMantissa_bounds zExponent zFraction hzZero hzFractionBound
  have hxScale :
      (finiteScale xExponent).toNat = xExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hxZero]
  have hyScale :
      (finiteScale yExponent).toNat = yExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hyZero]
  have hzScale :
      (finiteScale zExponent).toNat = zExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hzZero]
  have hproductScale :
      productScale.toNat =
        (xExponent.toNat - 1) + (yExponent.toNat - 1) := by
    unfold productScale
    rw [UInt64.toNat_add, hxScale, hyScale]
    apply Nat.mod_eq_of_lt
    norm_num
    omega
  have hzProductScale :
      zProductScale.toNat = (zExponent.toNat - 1) + 1074 := by
    unfold zProductScale
    rw [UInt64.toNat_add, hzScale]
    apply Nat.mod_eq_of_lt
    change zExponent.toNat - 1 + 1074 < 18446744073709551616
    omega
  let shift := (zProductScale - productScale).toNat
  have hshiftValue : shift = zProductScale.toNat - productScale.toNat :=
    UInt64.toNat_sub_of_le _ _ hlow
  have hlowNat : productScale.toNat ≤ zProductScale.toNat := UInt64.le_iff_toNat_le.mp hlow
  have hhighNat : zProductScale.toNat ≤ productScale.toNat + 62 := by
    have h := UInt64.le_iff_toNat_le.mp hhigh
    have hadd : (productScale + 62).toNat = productScale.toNat + 62 := by
      rw [UInt64.toNat_add, hproductScale]
      simp only [UInt64.reduceToNat]
      exact Nat.mod_eq_of_lt (by change _ < 18446744073709551616; omega)
    rw [hadd] at h
    exact h
  have hshiftLe : shift ≤ 62 := by omega
  have halignedNat :
      (xExponent.toNat - 1) + (yExponent.toNat - 1) + shift =
        (zExponent.toNat - 1) + 1074 := by
    omega
  have hxMantissaNe : xMantissa.toNat ≠ 0 := by omega
  have hyMantissaNe : yMantissa.toNat ≠ 0 := by omega
  have hzMantissaNe : zMantissa.toNat ≠ 0 := by omega
  have hrefines :=
    roundNormalFma_refines productSign xExponent yExponent
      xMantissa yMantissa zMantissa shift hshiftLe hxExponentBounds hyExponentBounds
      hxMantissaBounds hyMantissaBounds hzMantissaBounds result hcarryRaw hresult
  have hcomponents :
      FiniteKernel.fmaComponents FloatFormat.binary64
          { sign := signBit xBits
            exponent := xExponent.toNat
            mantissa := xMantissa.toNat }
          { sign := signBit yBits
            exponent := yExponent.toNat
            mantissa := yMantissa.toNat }
          { sign := zSign
            exponent := zExponent.toNat
            mantissa := zMantissa.toNat } =
        result := by
    calc
      _ = FiniteProductRound.round FloatFormat.binary64 productSign
            (xMantissa.toNat * yMantissa.toNat +
              (zMantissa.toNat <<< shift))
            ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
          have hz : zSign = Bool.xor (signBit xBits) (signBit yBits) := hsign.symm
          rw [hz]
          exact FiniteKernel.fmaComponents_sameSign_aligned
              FloatFormat.binary64 (by decide) shift
              (signBit xBits) (signBit yBits)
              xExponent.toNat yExponent.toNat zExponent.toNat
              xMantissa.toNat yMantissa.toNat zMantissa.toNat
              (Nat.ne_of_gt hxExponentBounds.1)
              (Nat.ne_of_gt hyExponentBounds.1)
              (Nat.ne_of_gt hzExponentBounds.1)
              hxMantissaNe hyMantissaNe hzMantissaNe halignedNat
      _ = result := hrefines.symm
  exact fmaFiniteComponents?_eq_some_of_components x y z result
    hxExceptional hyExceptional hzExceptional hcomponents

private theorem fmaNormalOppositeSign_refines
    (x y z result : Value)
    (hresult : fmaNormalOppositeSign? x y z = some result) :
    fmaFiniteComponents? x y z = some result := by
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let zBits := toUInt64 z
  let xExponent := expField xBits
  let yExponent := expField yBits
  let zExponent := expField zBits
  let xFraction := fracField xBits
  let yFraction := fracField yBits
  let zFraction := fracField zBits
  let xMantissa := finiteMantissa xExponent xFraction
  let yMantissa := finiteMantissa yExponent yFraction
  let zMantissa := finiteMantissa zExponent zFraction
  let productScale := finiteScale xExponent + finiteScale yExponent
  let zProductScale := finiteScale zExponent + 1074
  let productSign := Bool.xor (signBit xBits) (signBit yBits)
  let zSign := signBit zBits
  unfold fmaNormalOppositeSign? fmaNormalOppositeSignWord? at hresult
  dsimp only at hresult
  split at hresult
  · simp at hresult
  rename_i hexponents
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hexponents
  obtain ⟨⟨⟨⟨⟨hxZero, hxExceptional⟩, hyZero⟩, hyExceptional⟩, hzZero⟩, hzExceptional⟩ :=
    hexponents
  replace hxZero : xExponent ≠ 0 := hxZero
  replace hxExceptional : xExponent ≠ 0x7ff := hxExceptional
  replace hyZero : yExponent ≠ 0 := hyZero
  replace hyExceptional : yExponent ≠ 0x7ff := hyExceptional
  replace hzZero : zExponent ≠ 0 := hzZero
  replace hzExceptional : zExponent ≠ 0x7ff := hzExceptional
  split at hresult
  · simp at hresult
  rename_i hguard
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or,
    UInt64.not_lt] at hguard
  obtain ⟨⟨hsign, hlow⟩, hhigh⟩ := hguard
  replace hsign : productSign ≠ zSign := hsign
  replace hlow : productScale ≤ zProductScale := hlow
  replace hhigh : zProductScale ≤ productScale + 62 := hhigh
  have hxExponentBounds :
      0 < xExponent.toNat ∧ xExponent.toNat < 2047 := by
    simpa [xExponent, xBits] using
      normalExponent_bounds x hxZero hxExceptional
  have hyExponentBounds :
      0 < yExponent.toNat ∧ yExponent.toNat < 2047 := by
    simpa [yExponent, yBits] using
      normalExponent_bounds y hyZero hyExceptional
  have hzExponentBounds :
      0 < zExponent.toNat ∧ zExponent.toNat < 2047 := by
    simpa [zExponent, zBits] using
      normalExponent_bounds z hzZero hzExceptional
  have hxFractionBound : xFraction.toNat < 2 ^ 52 := by
    simpa [xFraction, xBits] using fracField_lt x
  have hyFractionBound : yFraction.toNat < 2 ^ 52 := by
    simpa [yFraction, yBits] using fracField_lt y
  have hzFractionBound : zFraction.toNat < 2 ^ 52 := by
    simpa [zFraction, zBits] using fracField_lt z
  have hxMantissaBounds :
      2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53 := by
    simpa [xMantissa] using
      finiteMantissa_bounds xExponent xFraction hxZero hxFractionBound
  have hyMantissaBounds :
      2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53 := by
    simpa [yMantissa] using
      finiteMantissa_bounds yExponent yFraction hyZero hyFractionBound
  have hzMantissaBounds :
      2 ^ 52 ≤ zMantissa.toNat ∧ zMantissa.toNat < 2 ^ 53 := by
    simpa [zMantissa] using
      finiteMantissa_bounds zExponent zFraction hzZero hzFractionBound
  have hxScale :
      (finiteScale xExponent).toNat = xExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hxZero]
  have hyScale :
      (finiteScale yExponent).toNat = yExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hyZero]
  have hzScale :
      (finiteScale zExponent).toNat = zExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hzZero]
  have hproductScale :
      productScale.toNat =
        (xExponent.toNat - 1) + (yExponent.toNat - 1) := by
    unfold productScale
    rw [UInt64.toNat_add, hxScale, hyScale]
    apply Nat.mod_eq_of_lt
    norm_num
    omega
  have hzProductScale :
      zProductScale.toNat = (zExponent.toNat - 1) + 1074 := by
    unfold zProductScale
    rw [UInt64.toNat_add, hzScale]
    apply Nat.mod_eq_of_lt
    change zExponent.toNat - 1 + 1074 < 18446744073709551616
    omega
  let shift := (zProductScale - productScale).toNat
  have hshiftValue : shift = zProductScale.toNat - productScale.toNat :=
    UInt64.toNat_sub_of_le _ _ hlow
  have hlowNat : productScale.toNat ≤ zProductScale.toNat := UInt64.le_iff_toNat_le.mp hlow
  have hhighNat : zProductScale.toNat ≤ productScale.toNat + 62 := by
    have h := UInt64.le_iff_toNat_le.mp hhigh
    have hadd : (productScale + 62).toNat = productScale.toNat + 62 := by
      rw [UInt64.toNat_add, hproductScale]
      simp only [UInt64.reduceToNat]
      exact Nat.mod_eq_of_lt (by change _ < 18446744073709551616; omega)
    rw [hadd] at h
    exact h
  have hshiftLe : shift ≤ 62 := by omega
  have halignedNat :
      (xExponent.toNat - 1) + (yExponent.toNat - 1) + shift =
        (zExponent.toNat - 1) + 1074 := by
    omega
  have hxMantissaNe : xMantissa.toNat ≠ 0 := by omega
  have hyMantissaNe : yMantissa.toNat ≠ 0 := by omega
  have hzMantissaNe : zMantissa.toNat ≠ 0 := by omega
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let aligned := alignFmaAddend zMantissa shift
  split at hresult
  · simp at hresult
  rename_i hproductNeRaw
  have hproductNe : product ≠ aligned := by
    intro heq
    apply hproductNeRaw
    change (product == aligned) = true
    simp [heq]
  have hproduct :
      product.toNat = xMantissa.toNat * yMantissa.toNat := by
    simp [product]
  have halignedValue :
      aligned.toNat = zMantissa.toNat <<< shift := by
    exact alignFmaAddend_toNat zMantissa shift hzMantissaBounds.2 hshiftLe
  have hproductUpper : product.toNat < 2 ^ 116 := by
    rw [hproduct]
    calc xMantissa.toNat * yMantissa.toNat < 2 ^ 53 * 2 ^ 53 :=
          Nat.mul_lt_mul'' hxMantissaBounds.2 hyMantissaBounds.2
      _ ≤ 2 ^ 116 := by norm_num
  have halignedUpper : aligned.toNat < 2 ^ 116 := by
    rw [halignedValue]
    exact lt_trans (alignFmaAddend_lt zMantissa shift hzMantissaBounds.2 hshiftLe)
      (by norm_num)
  change Option.map ofUInt64 (if fmaLeading (if UInt128.less product aligned = true then
        UInt128.sub aligned product else UInt128.sub product aligned) < 53 then none
    else roundNormalProductWord? (if UInt128.less product aligned = true then zSign
        else productSign)
      xExponent yExponent
      (if UInt128.less product aligned = true then UInt128.sub aligned product
        else UInt128.sub product aligned)
      (fmaLeading (if UInt128.less product aligned = true then UInt128.sub aligned product
        else UInt128.sub product aligned))) = some result at hresult
  by_cases hless : FloatLib.Numerics.FixedWord.UInt128.less product aligned = true
  · have hordered : product.toNat < aligned.toNat :=
      (FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff product aligned).mp hless
    let magnitude := FloatLib.Numerics.FixedWord.UInt128.sub aligned product
    simp only [hless, ite_true] at hresult
    split at hresult
    · simp at hresult
    rename_i hleadingRaw
    have hleadingMin : 53 ≤ (fmaLeading magnitude).toNat := by
      have hword : (53 : UInt64) ≤ fmaLeading magnitude := UInt64.not_lt.mp hleadingRaw
      simpa using UInt64.le_iff_toNat_le.mp hword
    have hrefines :=
      roundNormalFmaDifference_refines zSign xExponent yExponent
        aligned product hxExponentBounds hyExponentBounds hordered
        halignedUpper hleadingMin result hresult
    have hcomponents :
        FiniteKernel.fmaComponents FloatFormat.binary64
            { sign := signBit xBits
              exponent := xExponent.toNat
              mantissa := xMantissa.toNat }
            { sign := signBit yBits
              exponent := yExponent.toNat
              mantissa := yMantissa.toNat }
            { sign := zSign
              exponent := zExponent.toNat
              mantissa := zMantissa.toNat } =
          result := by
      calc
        _ = FiniteProductRound.round FloatFormat.binary64 zSign
              ((zMantissa.toNat <<< shift) -
                xMantissa.toNat * yMantissa.toNat)
              ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
            exact fmaComponents_opposite_aligned_addend_larger shift
              (signBit xBits) (signBit yBits) zSign
              xExponent.toNat yExponent.toNat zExponent.toNat
              xMantissa.toNat yMantissa.toNat zMantissa.toNat
              (Nat.ne_of_gt hxExponentBounds.1)
              (Nat.ne_of_gt hyExponentBounds.1)
              (Nat.ne_of_gt hzExponentBounds.1)
              hxMantissaNe hyMantissaNe hzMantissaNe
              hsign halignedNat
              (by simpa [hproduct, halignedValue] using hordered)
        _ = result := by
          rw [← halignedValue, ← hproduct]
          exact hrefines.symm
    exact fmaFiniteComponents?_eq_some_of_components x y z result
      hxExceptional hyExceptional hzExceptional hcomponents
  · have hnotLt : ¬product.toNat < aligned.toNat := by
      intro hordered
      exact hless
        ((FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff product aligned).mpr hordered)
    have hnatNe : product.toNat ≠ aligned.toNat := by
      intro heq
      exact hproductNe (FloatLib.Numerics.FixedWord.UInt128.toNat_injective heq)
    have hordered : aligned.toNat < product.toNat := by omega
    let magnitude := FloatLib.Numerics.FixedWord.UInt128.sub product aligned
    simp only [hless, Bool.false_eq_true, ite_false] at hresult
    split at hresult
    · simp at hresult
    rename_i hleadingRaw
    have hleadingMin : 53 ≤ (fmaLeading magnitude).toNat := by
      have hword : (53 : UInt64) ≤ fmaLeading magnitude := UInt64.not_lt.mp hleadingRaw
      simpa using UInt64.le_iff_toNat_le.mp hword
    have hrefines :=
      roundNormalFmaDifference_refines productSign xExponent yExponent
        product aligned hxExponentBounds hyExponentBounds hordered
        hproductUpper hleadingMin result hresult
    have hcomponents :
        FiniteKernel.fmaComponents FloatFormat.binary64
            { sign := signBit xBits
              exponent := xExponent.toNat
              mantissa := xMantissa.toNat }
            { sign := signBit yBits
              exponent := yExponent.toNat
              mantissa := yMantissa.toNat }
            { sign := zSign
              exponent := zExponent.toNat
              mantissa := zMantissa.toNat } =
          result := by
      calc
        _ = FiniteProductRound.round FloatFormat.binary64 productSign
              (xMantissa.toNat * yMantissa.toNat -
                (zMantissa.toNat <<< shift))
              ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
            exact fmaComponents_opposite_aligned_product_larger shift
              (signBit xBits) (signBit yBits) zSign
              xExponent.toNat yExponent.toNat zExponent.toNat
              xMantissa.toNat yMantissa.toNat zMantissa.toNat
              (Nat.ne_of_gt hxExponentBounds.1)
              (Nat.ne_of_gt hyExponentBounds.1)
              (Nat.ne_of_gt hzExponentBounds.1)
              hxMantissaNe hyMantissaNe hzMantissaNe
              hsign halignedNat
              (by simpa [hproduct, halignedValue] using hordered)
        _ = result := by
          rw [← hproduct, ← halignedValue]
          exact hrefines.symm
    exact fmaFiniteComponents?_eq_some_of_components x y z result
      hxExceptional hyExceptional hzExceptional hcomponents


/-! ## Sticky alignment outside the exact window -/

/-- A jammed quotient stays below a power of two that bounds the quotient. -/
private theorem shiftRightJam_lt_two_pow (x j n : Nat) (h : x / 2 ^ j < 2 ^ n) (hn : 0 < n) :
    Numerics.shiftRightJam x j < 2 ^ n := by
  unfold Numerics.shiftRightJam
  dsimp only
  split
  · exact h
  · exact Nat.or_lt_two_pow h (Nat.one_lt_two_pow (by omega))

/-- With the addend below the product, the generic kernel rounds the exact sum at the addend's scale. -/
private theorem fmaComponents_addend_below
    (xSign ySign zSign : Bool)
    (xExponent yExponent zExponent xMantissa yMantissa zMantissa : Nat)
    (hxExponent : xExponent ≠ 0) (hyExponent : yExponent ≠ 0) (hzExponent : zExponent ≠ 0)
    (hxMantissa : xMantissa ≠ 0) (hyMantissa : yMantissa ≠ 0) (hzMantissa : zMantissa ≠ 0)
    (hbelow : (zExponent - 1) + 1074 < (xExponent - 1) + (yExponent - 1))
    (hdominant : zMantissa < xMantissa * yMantissa *
      2 ^ ((xExponent - 1) + (yExponent - 1) - ((zExponent - 1) + 1074))) :
    FiniteKernel.fmaComponents FloatFormat.binary64
        { sign := xSign, exponent := xExponent, mantissa := xMantissa }
        { sign := ySign, exponent := yExponent, mantissa := yMantissa }
        { sign := zSign, exponent := zExponent, mantissa := zMantissa } =
      FiniteProductRound.round FloatFormat.binary64 (Bool.xor xSign ySign)
        (if Bool.xor xSign ySign == zSign then
          xMantissa * yMantissa *
              2 ^ ((xExponent - 1) + (yExponent - 1) - ((zExponent - 1) + 1074)) + zMantissa
        else
          xMantissa * yMantissa *
              2 ^ ((xExponent - 1) + (yExponent - 1) - ((zExponent - 1) + 1074)) - zMantissa)
        ((zExponent - 1) + 1074) := by
  rw [← FiniteKernel.Internal.fmaComponents_eq]
  unfold FiniteKernel.Internal.fmaComponents
  rw [ite_eq_left (by decide : FloatFormat.binary64.isIEEE = true)]
  unfold FiniteScaleAdd.roundSum
  have hoffset : FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 := by decide
  simp only [FiniteKernel.scale, hxExponent, hyExponent, hzExponent, beq_iff_eq, ite_false,
    hxMantissa, hyMantissa, hzMantissa, mul_eq_zero, or_self, hoffset]
  rw [ite_eq_right (by omega), FiniteScaleAdd.roundAligned_eq]
  unfold FiniteScaleAdd.roundMagnitudes FiniteScaleAdd.roundMagnitude
  rw [Nat.shiftLeft_eq, Nat.add_zero]
  by_cases hsign : Bool.xor xSign ySign = zSign
  · simp only [hsign, beq_self_eq_true, ite_true]
  · have hsignBeq : (Bool.xor xSign ySign == zSign) = false := by simpa using hsign
    have hne : xMantissa * yMantissa *
        2 ^ ((xExponent - 1) + (yExponent - 1) - ((zExponent - 1) + 1074)) ≠ zMantissa := by
      omega
    simp only [hsignBeq, Bool.false_eq_true, ite_false, beq_iff_eq, hne, hsign,
      Nat.not_lt_of_ge hdominant.le]

/-- With the addend far above the product, the generic kernel rounds the exact sum at the product's
scale. -/
private theorem fmaComponents_addend_above
    (xSign ySign zSign : Bool)
    (xExponent yExponent zExponent xMantissa yMantissa zMantissa : Nat)
    (hxExponent : xExponent ≠ 0) (hyExponent : yExponent ≠ 0) (hzExponent : zExponent ≠ 0)
    (hxMantissa : xMantissa ≠ 0) (hyMantissa : yMantissa ≠ 0) (hzMantissa : zMantissa ≠ 0)
    (habove : (xExponent - 1) + (yExponent - 1) ≤ (zExponent - 1) + 1074)
    (hdominant : xMantissa * yMantissa < zMantissa *
      2 ^ ((zExponent - 1) + 1074 - ((xExponent - 1) + (yExponent - 1)))) :
    FiniteKernel.fmaComponents FloatFormat.binary64
        { sign := xSign, exponent := xExponent, mantissa := xMantissa }
        { sign := ySign, exponent := yExponent, mantissa := yMantissa }
        { sign := zSign, exponent := zExponent, mantissa := zMantissa } =
      FiniteProductRound.round FloatFormat.binary64 zSign
        (if zSign == Bool.xor xSign ySign then
          zMantissa * 2 ^ ((zExponent - 1) + 1074 - ((xExponent - 1) + (yExponent - 1))) +
            xMantissa * yMantissa
        else
          zMantissa * 2 ^ ((zExponent - 1) + 1074 - ((xExponent - 1) + (yExponent - 1))) -
            xMantissa * yMantissa)
        ((xExponent - 1) + (yExponent - 1)) := by
  rw [← FiniteKernel.Internal.fmaComponents_eq]
  unfold FiniteKernel.Internal.fmaComponents
  rw [ite_eq_left (by decide : FloatFormat.binary64.isIEEE = true)]
  unfold FiniteScaleAdd.roundSum
  have hoffset : FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 := by decide
  simp only [FiniteKernel.scale, hxExponent, hyExponent, hzExponent, beq_iff_eq, ite_false,
    hxMantissa, hyMantissa, hzMantissa, mul_eq_zero, or_self, hoffset]
  rw [ite_eq_left habove, FiniteScaleAdd.roundAligned_eq]
  unfold FiniteScaleAdd.roundMagnitudes FiniteScaleAdd.roundMagnitude
  rw [Nat.shiftLeft_eq, Nat.add_zero]
  by_cases hsign : zSign = Bool.xor xSign ySign
  · subst hsign
    simp only [beq_self_eq_true, ite_true, Nat.add_zero]
  · have hsignBeq : (zSign == Bool.xor xSign ySign) = false := by simpa using hsign
    have hne : zMantissa *
        2 ^ ((zExponent - 1) + 1074 - ((xExponent - 1) + (yExponent - 1))) ≠
          xMantissa * yMantissa := by
      omega
    simp only [hsignBeq, Bool.false_eq_true, ite_false, beq_iff_eq, hne, hsign, Nat.add_zero,
      Nat.not_lt_of_ge hdominant.le]

private theorem fmaJammed_refines
    (x y z result : Value)
    (hresult : fmaJammed? x y z = some result) :
    fmaFiniteComponents? x y z = some result := by
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let zBits := toUInt64 z
  let xExponent := expField xBits
  let yExponent := expField yBits
  let zExponent := expField zBits
  let xFraction := fracField xBits
  let yFraction := fracField yBits
  let zFraction := fracField zBits
  let xMantissa := finiteMantissa xExponent xFraction
  let yMantissa := finiteMantissa yExponent yFraction
  let zMantissa := finiteMantissa zExponent zFraction
  let productScale := finiteScale xExponent + finiteScale yExponent
  let zProductScale := finiteScale zExponent + 1074
  let productSign := Bool.xor (signBit xBits) (signBit yBits)
  let zSign := signBit zBits
  unfold fmaJammed? fmaJammedWord? at hresult
  dsimp only at hresult
  split at hresult
  · simp at hresult
  rename_i hexponents
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hexponents
  obtain ⟨⟨⟨⟨⟨hxZero, hxExceptional⟩, hyZero⟩, hyExceptional⟩, hzZero⟩, hzExceptional⟩ :=
    hexponents
  replace hxZero : xExponent ≠ 0 := hxZero
  replace hxExceptional : xExponent ≠ 0x7ff := hxExceptional
  replace hyZero : yExponent ≠ 0 := hyZero
  replace hyExceptional : yExponent ≠ 0x7ff := hyExceptional
  replace hzZero : zExponent ≠ 0 := hzZero
  replace hzExceptional : zExponent ≠ 0x7ff := hzExceptional
  have hxExponentBounds :
      0 < xExponent.toNat ∧ xExponent.toNat < 2047 := by
    simpa [xExponent, xBits] using
      normalExponent_bounds x hxZero hxExceptional
  have hyExponentBounds :
      0 < yExponent.toNat ∧ yExponent.toNat < 2047 := by
    simpa [yExponent, yBits] using
      normalExponent_bounds y hyZero hyExceptional
  have hzExponentBounds :
      0 < zExponent.toNat ∧ zExponent.toNat < 2047 := by
    simpa [zExponent, zBits] using
      normalExponent_bounds z hzZero hzExceptional
  have hxFractionBound : xFraction.toNat < 2 ^ 52 := by
    simpa [xFraction, xBits] using fracField_lt x
  have hyFractionBound : yFraction.toNat < 2 ^ 52 := by
    simpa [yFraction, yBits] using fracField_lt y
  have hzFractionBound : zFraction.toNat < 2 ^ 52 := by
    simpa [zFraction, zBits] using fracField_lt z
  have hxMantissaBounds :
      2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53 := by
    simpa [xMantissa] using
      finiteMantissa_bounds xExponent xFraction hxZero hxFractionBound
  have hyMantissaBounds :
      2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53 := by
    simpa [yMantissa] using
      finiteMantissa_bounds yExponent yFraction hyZero hyFractionBound
  have hzMantissaBounds :
      2 ^ 52 ≤ zMantissa.toNat ∧ zMantissa.toNat < 2 ^ 53 := by
    simpa [zMantissa] using
      finiteMantissa_bounds zExponent zFraction hzZero hzFractionBound
  have hxScale :
      (finiteScale xExponent).toNat = xExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hxZero]
  have hyScale :
      (finiteScale yExponent).toNat = yExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hyZero]
  have hzScale :
      (finiteScale zExponent).toNat = zExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hzZero]
  have hproductScale :
      productScale.toNat =
        (xExponent.toNat - 1) + (yExponent.toNat - 1) := by
    unfold productScale
    rw [UInt64.toNat_add, hxScale, hyScale]
    apply Nat.mod_eq_of_lt
    norm_num
    omega
  have hzProductScale :
      zProductScale.toNat = (zExponent.toNat - 1) + 1074 := by
    unfold zProductScale
    rw [UInt64.toNat_add, hzScale]
    apply Nat.mod_eq_of_lt
    change zExponent.toNat - 1 + 1074 < 18446744073709551616
    omega
  have hxMantissaNe : xMantissa.toNat ≠ 0 := by omega
  have hyMantissaNe : yMantissa.toNat ≠ 0 := by omega
  have hzMantissaNe : zMantissa.toNat ≠ 0 := by omega
  have hzMantissaWord : zMantissa ≠ 0 := by
    intro h
    apply hzMantissaNe
    rw [h]
    rfl
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  have hproduct : product.toNat = xMantissa.toNat * yMantissa.toNat := by simp [product]
  have hproductLower : 2 ^ 104 ≤ product.toNat := by
    rw [hproduct]
    calc 2 ^ 104 = 2 ^ 52 * 2 ^ 52 := by norm_num
      _ ≤ xMantissa.toNat * yMantissa.toNat :=
        Nat.mul_le_mul hxMantissaBounds.1 hyMantissaBounds.1
  have hproductUpper : product.toNat < 2 ^ 106 := by
    rw [hproduct]
    calc xMantissa.toNat * yMantissa.toNat < 2 ^ 53 * 2 ^ 53 :=
          Nat.mul_lt_mul'' hxMantissaBounds.2 hyMantissaBounds.2
      _ = 2 ^ 106 := by norm_num
  have hcomponentsSign :
      Bool.xor (signBit xBits) (signBit yBits) = productSign := rfl
  split at hresult
  · -- The addend lies `gap` scale positions below the product.
    rename_i hbelowWord
    have hbelow : zProductScale.toNat < productScale.toNat := UInt64.lt_iff_toNat_lt.mp hbelowWord
    set g := productScale.toNat - zProductScale.toNat with hg
    have hgap : (productScale - zProductScale).toNat = g :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hbelowWord)
    have hlowerNat :
        (if productScale - zProductScale < 64 then
            zMantissa >>> (productScale - zProductScale) else 0).toNat =
          zMantissa.toNat / 2 ^ g := by
      split
      · rename_i hsmall
        have hsmallNat : g < 64 := by
          have := UInt64.lt_iff_toNat_lt.mp hsmall
          rw [hgap] at this
          simpa using this
        rw [UInt64.toNat_shiftRight, hgap, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hsmallNat]
      · rename_i hlarge
        have hlargeNat : 64 ≤ g := by
          have h2 := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hlarge)
          rw [hgap] at h2
          simpa using h2
        rw [UInt64.toNat_zero, eq_comm, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
        exact zMantissa.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) hlargeNat)
    have hexact :
        (decide (productScale - zProductScale < 64) &&
            (if productScale - zProductScale < 64 then
                zMantissa >>> (productScale - zProductScale) else 0) <<<
              (productScale - zProductScale) == zMantissa) =
          decide (zMantissa.toNat % 2 ^ g = 0) := by
      by_cases hsmall : productScale - zProductScale < 64
      · have hsmallNat : g < 64 := by
          have := UInt64.lt_iff_toNat_lt.mp hsmall
          rw [hgap] at this
          simpa using this
        simp only [hsmall, decide_true, ite_true, Bool.true_and]
        apply Bool.eq_iff_iff.mpr
        rw [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftLeft,
          UInt64.toNat_shiftRight, hgap, Nat.mod_eq_of_lt hsmallNat,
          Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
        have hle : zMantissa.toNat / 2 ^ g * 2 ^ g ≤ zMantissa.toNat := Nat.div_mul_le_self _ _
        rw [Nat.mod_eq_of_lt (hle.trans_lt zMantissa.toNat_lt)]
        have := Nat.div_add_mod' zMantissa.toNat (2 ^ g)
        omega
      · have hlargeNat : 64 ≤ g := by
          have h2 := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hsmall)
          rw [hgap] at h2
          simpa using h2
        simp only [hsmall, decide_false, Bool.false_and]
        symm
        rw [decide_eq_false_iff_not, Nat.mod_eq_of_lt
          (zMantissa.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) hlargeNat))]
        exact hzMantissaNe
    let lower : UInt128 :=
      ⟨0, if productScale - zProductScale < 64 then
            zMantissa >>> (productScale - zProductScale) else 0⟩
    have hlowerToNat : lower.toNat = zMantissa.toNat / 2 ^ g := by
      rw [← hlowerNat]
      simp [lower, UInt128.toNat]
    have hzLt : zMantissa.toNat < 2 ^ 53 := hzMantissaBounds.2
    have hlowerSmall : lower.toNat < 2 ^ 53 := by
      rw [hlowerToNat]
      exact (Nat.div_le_self _ _).trans_lt hzLt
    let exactSum :=
      if productSign == zSign then product.toNat * 2 ^ g + zMantissa.toNat
      else product.toNat * 2 ^ g - zMantissa.toNat
    have hmagnitude := UInt128.jamCombine_toNat (productSign == zSign)
      (decide (productScale - zProductScale < 64) &&
        (if productScale - zProductScale < 64 then
            zMantissa >>> (productScale - zProductScale) else 0) <<<
          (productScale - zProductScale) == zMantissa)
      product lower zMantissa.toNat g hlowerToNat hexact (by omega) (fun _ => by
        refine ⟨by omega, ?_⟩
        calc zMantissa.toNat ≤ product.toNat := by omega
          _ ≤ product.toNat * 2 ^ g := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
    set magnitude := UInt128.jamCombine (productSign == zSign)
      (decide (productScale - zProductScale < 64) &&
        (if productScale - zProductScale < 64 then
            zMantissa >>> (productScale - zProductScale) else 0) <<<
          (productScale - zProductScale) == zMantissa)
      product lower with hmagnitudeDef
    have hpowG : 2 ^ (104 + g) = 2 ^ 104 * 2 ^ g := Nat.pow_add _ _ _
    have hexactLower : 2 ^ (103 + g) ≤ exactSum := by
      have hpg : 2 ^ (104 + g) ≤ product.toNat * 2 ^ g := by
        rw [hpowG]
        exact Nat.mul_le_mul_right _ hproductLower
      have hhalf : 2 ^ (104 + g) = 2 ^ (103 + g) * 2 := by
        rw [show 104 + g = (103 + g) + 1 by omega, Nat.pow_succ]
      have hz : zMantissa.toNat ≤ 2 ^ (103 + g) :=
        hzLt.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
      simp only [exactSum]
      split <;> omega
    have hexactUpper : exactSum / 2 ^ g < 2 ^ 107 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      have hp : product.toNat * 2 ^ g < 2 ^ 106 * 2 ^ g :=
        Nat.mul_lt_mul_of_pos_right hproductUpper (Nat.two_pow_pos _)
      have hz : zMantissa.toNat < 2 ^ 106 * 2 ^ g :=
        hzLt.trans_le ((Nat.pow_le_pow_right (by decide) (by omega)).trans
          (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))
      have h107 : 2 ^ 107 * 2 ^ g = 2 ^ 106 * 2 ^ g + 2 ^ 106 * 2 ^ g := by
        rw [Nat.pow_succ]
        ring
      simp only [exactSum]
      split <;> omega
    have hmagNat : magnitude.toNat = Numerics.shiftRightJam exactSum g := hmagnitude
    have hmagLower : 2 ^ 103 ≤ magnitude.toNat := by
      rw [hmagNat]
      refine le_trans ?_ (Numerics.div_two_pow_le_shiftRightJam exactSum g)
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
      exact hexactLower
    have hmagUpper : magnitude.toNat < 2 ^ 116 := by
      rw [hmagNat]
      exact shiftRightJam_lt_two_pow _ _ _
        (hexactUpper.trans_le (Nat.pow_le_pow_right (by decide) (by omega))) (by decide)
    have hmagNe : magnitude.toNat ≠ 0 := by omega
    have hleading :
        (fmaLeading magnitude).toNat = magnitude.toNat.log2 :=
      fmaLeading_toNat magnitude hmagNe hmagUpper
    have hleadingRange : 53 ≤ (fmaLeading magnitude).toNat ∧
        (fmaLeading magnitude).toNat ≤ 115 := by
      rw [hleading]
      constructor
      · exact le_trans (by decide) ((Nat.le_log2 hmagNe).2 hmagLower)
      · have := (Nat.log2_lt hmagNe).2 hmagUpper
        omega
    have hrefines := roundNormalProduct_refines productSign xExponent yExponent magnitude
      (fmaLeading magnitude) hxExponentBounds hyExponentBounds hleading hleadingRange
      (le_trans (by decide) hmagLower) hmagUpper result hresult
    have hscaleSplit : (xExponent.toNat - 1) + (yExponent.toNat - 1) =
        ((zExponent.toNat - 1) + 1074) + g := by
      rw [← hproductScale, ← hzProductScale]
      omega
    rw [hscaleSplit, hmagNat,
      FiniteProductRound.round_shiftRightJam FloatFormat.binary64 productSign exactSum
        ((zExponent.toNat - 1) + 1074) g (by
          have hpositive := (Nat.two_pow_pos _).trans_le hexactLower
          have := (Nat.le_log2 hpositive.ne').2 hexactLower
          change g + 52 + 2 ≤ exactSum.log2
          omega)] at hrefines
    have hgNat : g = (xExponent.toNat - 1) + (yExponent.toNat - 1) -
        ((zExponent.toNat - 1) + 1074) := by omega
    have hcomponents :
        FiniteKernel.fmaComponents FloatFormat.binary64
            { sign := signBit xBits
              exponent := xExponent.toNat
              mantissa := xMantissa.toNat }
            { sign := signBit yBits
              exponent := yExponent.toNat
              mantissa := yMantissa.toNat }
            { sign := zSign
              exponent := zExponent.toNat
              mantissa := zMantissa.toNat } =
          result := by
      rw [fmaComponents_addend_below (signBit xBits) (signBit yBits) zSign
        xExponent.toNat yExponent.toNat zExponent.toNat
        xMantissa.toNat yMantissa.toNat zMantissa.toNat
        (Nat.ne_of_gt hxExponentBounds.1) (Nat.ne_of_gt hyExponentBounds.1)
        (Nat.ne_of_gt hzExponentBounds.1) hxMantissaNe hyMantissaNe hzMantissaNe
        (by omega) (by
          rw [← hgNat, ← hproduct]
          calc zMantissa.toNat < 2 ^ 104 := hzLt.trans (by norm_num)
            _ ≤ product.toNat := hproductLower
            _ ≤ product.toNat * 2 ^ g := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)),
        hrefines, ← hgNat, ← hproduct]
    exact fmaFiniteComponents?_eq_some_of_components x y z result
      hxExceptional hyExceptional hzExceptional hcomponents
  · split at hresult
    · -- The addend lies more than 62 scale positions above the product.
      rename_i hnotBelow habove
      have hpsAdd : (productScale + 62).toNat = productScale.toNat + 62 := by
        rw [UInt64.toNat_add, hproductScale]
        simp only [UInt64.reduceToNat]
        exact Nat.mod_eq_of_lt (by change _ < 18446744073709551616; omega)
      have hfar : productScale.toNat + 62 < zProductScale.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp habove
        rwa [hpsAdd] at this
      set s := zProductScale.toNat - productScale.toNat with hs
      set d := s - 3 with hd
      have hsWord : (zProductScale - productScale).toNat = s :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
      have hdiscard : (zProductScale - productScale - 3).toNat = d := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hsWord]; simp; omega)),
          hsWord]
        rfl
      let lower := FloatLib.Numerics.FixedWord.UInt128.shiftRight product
        (zProductScale - productScale - 3).toNat
      have hlowerToNat : lower.toNat = product.toNat / 2 ^ d := by
        simp only [lower, UInt128.shiftRight_toNat, hdiscard]
      have hproductNe : product.toNat ≠ 0 := by omega
      have hexact :
          (decide (zProductScale - productScale - 3 < 128) &&
              (FloatLib.Numerics.FixedWord.UInt128.shiftLeft lower
                (zProductScale - productScale - 3).toNat).hi == product.hi &&
              (FloatLib.Numerics.FixedWord.UInt128.shiftLeft lower
                (zProductScale - productScale - 3).toNat).lo == product.lo) =
            decide (product.toNat % 2 ^ d = 0) := by
        by_cases hsmall : zProductScale - productScale - 3 < 128
        · have hsmallNat : d < 128 := by
            have := UInt64.lt_iff_toNat_lt.mp hsmall
            rw [hdiscard] at this
            simpa using this
          have hle : product.toNat / 2 ^ d * 2 ^ d ≤ product.toNat := Nat.div_mul_le_self _ _
          have hshifted :
              (FloatLib.Numerics.FixedWord.UInt128.shiftLeft lower
                (zProductScale - productScale - 3).toNat).toNat = product.toNat / 2 ^ d * 2 ^ d := by
            rw [hdiscard, UInt128.shiftLeft_toNat _ _ hsmallNat (by
              rw [hlowerToNat, Nat.shiftLeft_eq]
              exact hle.trans_lt (hproductUpper.trans (by norm_num))), hlowerToNat,
              Nat.shiftLeft_eq]
          simp only [hsmall, decide_true, Bool.true_and]
          apply Bool.eq_iff_iff.mpr
          rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, decide_eq_true_eq]
          constructor
          · rintro ⟨hhi, hlo⟩
            have this : (FloatLib.Numerics.FixedWord.UInt128.shiftLeft lower
                (zProductScale - productScale - 3).toNat).toNat = product.toNat := by
              unfold UInt128.toNat
              rw [hhi, hlo]
            rw [hshifted] at this
            have hdecomp := Nat.div_add_mod' product.toNat (2 ^ d)
            omega
          · intro hz
            have heq : FloatLib.Numerics.FixedWord.UInt128.shiftLeft lower
                (zProductScale - productScale - 3).toNat = product := by
              apply UInt128.toNat_injective
              rw [hshifted]
              have hdecomp := Nat.div_add_mod' product.toNat (2 ^ d)
              omega
            rw [heq]
            exact ⟨rfl, rfl⟩
        · have hlargeNat : 128 ≤ d := by
            have h2 := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hsmall)
            rw [hdiscard] at h2
            simpa using h2
          simp only [hsmall, decide_false, Bool.false_and]
          symm
          rw [decide_eq_false_iff_not, Nat.mod_eq_of_lt
            (hproductUpper.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
          exact hproductNe
      let upper : UInt128 := ⟨0, zMantissa <<< 3⟩
      have hzShift : (zMantissa <<< 3).toNat = zMantissa.toNat * 2 ^ 3 := by
        have hfit : zMantissa.toNat <<< 3 < 2 ^ 64 := by
          rw [Nat.shiftLeft_eq]
          calc zMantissa.toNat * 2 ^ 3 < 2 ^ 53 * 2 ^ 3 :=
                Nat.mul_lt_mul_of_pos_right hzMantissaBounds.2 (by decide)
            _ ≤ 2 ^ 64 := by norm_num
        have h := FloatLib.Numerics.FixedWord.shiftLeft_toNat zMantissa 3 (by decide) hfit
        simpa [Nat.shiftLeft_eq] using h
      have hupperToNat : upper.toNat = zMantissa.toNat * 2 ^ 3 := by
        rw [← hzShift]
        simp [upper, UInt128.toNat]
      have hlowerSmall : lower.toNat < 2 ^ 46 := by
        rw [hlowerToNat, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        calc product.toNat < 2 ^ 106 := hproductUpper
          _ ≤ 2 ^ 46 * 2 ^ d := by
            rw [← Nat.pow_add]
            exact Nat.pow_le_pow_right (by decide) (by omega)
      have hupperLower : 2 ^ 55 ≤ upper.toNat := by
        rw [hupperToNat]
        calc 2 ^ 55 = 2 ^ 52 * 2 ^ 3 := by norm_num
          _ ≤ zMantissa.toNat * 2 ^ 3 := Nat.mul_le_mul_right _ hzMantissaBounds.1
      have hupperUpper : upper.toNat < 2 ^ 56 := by
        rw [hupperToNat]
        calc zMantissa.toNat * 2 ^ 3 < 2 ^ 53 * 2 ^ 3 :=
              Nat.mul_lt_mul_of_pos_right hzMantissaBounds.2 (by decide)
          _ = 2 ^ 56 := by norm_num
      have hpowS : upper.toNat * 2 ^ d = zMantissa.toNat * 2 ^ s := by
        rw [hupperToNat, Nat.mul_assoc, ← Nat.pow_add, show 3 + d = s by omega]
      have hproductLe : product.toNat ≤ upper.toNat * 2 ^ d := by
        calc product.toNat ≤ 2 ^ 106 := hproductUpper.le
          _ ≤ 2 ^ 55 * 2 ^ d := by
            rw [← Nat.pow_add]
            exact Nat.pow_le_pow_right (by decide) (by omega)
          _ ≤ upper.toNat * 2 ^ d := Nat.mul_le_mul_right _ hupperLower
      have hmagnitude := UInt128.jamCombine_toNat (productSign == zSign)
        (decide (zProductScale - productScale - 3 < 128) &&
          (FloatLib.Numerics.FixedWord.UInt128.shiftLeft lower
            (zProductScale - productScale - 3).toNat).hi == product.hi &&
          (FloatLib.Numerics.FixedWord.UInt128.shiftLeft lower
            (zProductScale - productScale - 3).toNat).lo == product.lo)
        upper lower product.toNat d hlowerToNat hexact (by omega)
        (fun _ => ⟨by omega, hproductLe⟩)
      set magnitude := UInt128.jamCombine (productSign == zSign)
        (decide (zProductScale - productScale - 3 < 128) &&
          (FloatLib.Numerics.FixedWord.UInt128.shiftLeft lower
            (zProductScale - productScale - 3).toNat).hi == product.hi &&
          (FloatLib.Numerics.FixedWord.UInt128.shiftLeft lower
            (zProductScale - productScale - 3).toNat).lo == product.lo)
        upper lower with hmagnitudeDef
      let exactSum :=
        if productSign == zSign then upper.toNat * 2 ^ d + product.toNat
        else upper.toNat * 2 ^ d - product.toNat
      have hmagNat : magnitude.toNat = Numerics.shiftRightJam exactSum d := hmagnitude
      have hpow51 : 2 ^ (51 + s) * 2 = 2 ^ (52 + s) := by
        rw [show 52 + s = (51 + s) + 1 by omega, Nat.pow_succ]
      have hzS : 2 ^ (52 + s) ≤ zMantissa.toNat * 2 ^ s := by
        rw [Nat.pow_add]
        exact Nat.mul_le_mul_right _ hzMantissaBounds.1
      have hp51 : product.toNat ≤ 2 ^ (51 + s) :=
        hproductUpper.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
      have hexactLower : 2 ^ (51 + s) ≤ exactSum := by
        simp only [exactSum]
        split <;> omega
      have hexactUpper : exactSum / 2 ^ d < 2 ^ 58 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        have hu : upper.toNat * 2 ^ d < 2 ^ 56 * 2 ^ d :=
          Nat.mul_lt_mul_of_pos_right hupperUpper (Nat.two_pow_pos _)
        have hp : product.toNat < 2 ^ 56 * 2 ^ d :=
          hproductUpper.trans_le (by
            rw [← Nat.pow_add]
            exact Nat.pow_le_pow_right (by decide) (by omega))
        have h58 : 2 ^ 58 * 2 ^ d = 2 ^ 56 * 2 ^ d + 2 ^ 56 * 2 ^ d + 2 ^ 56 * 2 ^ d +
            2 ^ 56 * 2 ^ d := by
          rw [show (58 : Nat) = 56 + 2 by rfl, Nat.pow_add]
          ring
        simp only [exactSum]
        split <;> omega
      have hmagLower : 2 ^ 54 ≤ magnitude.toNat := by
        rw [hmagNat]
        refine le_trans ?_ (Numerics.div_two_pow_le_shiftRightJam exactSum d)
        rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
        exact (Nat.pow_le_pow_right (by decide) (by omega)).trans hexactLower
      have hmagUpper : magnitude.toNat < 2 ^ 116 := by
        rw [hmagNat]
        exact shiftRightJam_lt_two_pow _ _ _
          (hexactUpper.trans_le (Nat.pow_le_pow_right (by decide) (by omega))) (by decide)
      have hmagNe : magnitude.toNat ≠ 0 := by omega
      have hleading :
          (fmaLeading magnitude).toNat = magnitude.toNat.log2 :=
        fmaLeading_toNat magnitude hmagNe hmagUpper
      have hleadingRange : 53 ≤ (fmaLeading magnitude).toNat ∧
          (fmaLeading magnitude).toNat ≤ 115 := by
        rw [hleading]
        constructor
        · exact le_trans (by decide) ((Nat.le_log2 hmagNe).2 hmagLower)
        · have := (Nat.log2_lt hmagNe).2 hmagUpper
          omega
      have hscaleSum : (productScale + (zProductScale - productScale - 3)).toNat =
          productScale.toNat + d := by
        rw [UInt64.toNat_add, hdiscard]
        exact Nat.mod_eq_of_lt (by change _ < 18446744073709551616; omega)
      have hrefines := roundScaled_refines zSign (productScale + (zProductScale - productScale - 3))
        magnitude (fmaLeading magnitude) (by rw [hscaleSum]; omega) hleading hleadingRange
        (le_trans (by decide) hmagLower) hmagUpper result hresult
      rw [hscaleSum, hmagNat,
        FiniteProductRound.round_shiftRightJam FloatFormat.binary64 zSign exactSum
          productScale.toNat d (by
            have hpositive := (Nat.two_pow_pos _).trans_le hexactLower
            have := (Nat.le_log2 hpositive.ne').2 hexactLower
            change d + 52 + 2 ≤ exactSum.log2
            omega)] at hrefines
      have hsNat : s = (zExponent.toNat - 1) + 1074 -
          ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
        rw [hs, hproductScale, hzProductScale]
      have hcomponents :
          FiniteKernel.fmaComponents FloatFormat.binary64
              { sign := signBit xBits
                exponent := xExponent.toNat
                mantissa := xMantissa.toNat }
              { sign := signBit yBits
                exponent := yExponent.toNat
                mantissa := yMantissa.toNat }
              { sign := zSign
                exponent := zExponent.toNat
                mantissa := zMantissa.toNat } =
            result := by
        rw [fmaComponents_addend_above (signBit xBits) (signBit yBits) zSign
          xExponent.toNat yExponent.toNat zExponent.toNat
          xMantissa.toNat yMantissa.toNat zMantissa.toNat
          (Nat.ne_of_gt hxExponentBounds.1) (Nat.ne_of_gt hyExponentBounds.1)
          (Nat.ne_of_gt hzExponentBounds.1) hxMantissaNe hyMantissaNe hzMantissaNe
          (by rw [← hproductScale, ← hzProductScale]; omega) (by
            rw [← hsNat, ← hproduct]
            calc product.toNat < 2 ^ 106 := hproductUpper
              _ ≤ 2 ^ (52 + s) := Nat.pow_le_pow_right (by decide) (by omega)
              _ ≤ zMantissa.toNat * 2 ^ s := hzS),
          hrefines, ← hsNat, ← hproduct, ← hproductScale]
        have hcomm : ∀ a b : Bool, (a == b) = (b == a) := by decide
        simp only [exactSum, hpowS]
        rw [hcomm zSign]
      exact fmaFiniteComponents?_eq_some_of_components x y z result
        hxExceptional hyExceptional hzExceptional hcomponents
    · simp at hresult

/-- Native finite binary64 FMA, with its fallback, equals the generic finite kernel. -/
theorem fmaFinite_eq (x y z : Value) :
    fmaFinite? x y z = FiniteKernel.fma? x y z := by
  unfold fmaFinite? fmaNormal? fmaNormalWord?
  cases hfast : fmaNormalSameSignWord? (toUInt64 x) (toUInt64 y) (toUInt64 z) with
  | some word =>
      simp only [Option.map_some]
      rw [← fmaFiniteComponents_eq]
      exact (fmaNormalSameSign_refines x y z (ofUInt64 word)
        (by simp only [fmaNormalSameSign?, hfast, Option.map_some])).symm
  | none =>
      cases hopposite : fmaNormalOppositeSignWord? (toUInt64 x) (toUInt64 y) (toUInt64 z) with
      | some word =>
          simp only [Option.map_some]
          rw [← fmaFiniteComponents_eq]
          exact (fmaNormalOppositeSign_refines x y z (ofUInt64 word)
            (by simp only [fmaNormalOppositeSign?, hopposite, Option.map_some])).symm
      | none =>
          cases hjammed : fmaJammedWord? (toUInt64 x) (toUInt64 y) (toUInt64 z) with
          | none => exact fmaFiniteComponents_eq x y z
          | some word =>
              simp only [Option.map_some]
              rw [← fmaFiniteComponents_eq]
              exact (fmaJammed_refines x y z (ofUInt64 word)
                (by simp only [fmaJammed?, hjammed, Option.map_some])).symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
