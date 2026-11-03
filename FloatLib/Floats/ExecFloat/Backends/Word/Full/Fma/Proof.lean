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
  rw [FloatLib.Numerics.FixedWord.UInt128.shiftLeft_toNat _ shift hfit, hvalue]

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

/--
`fmaLeading` is the leading-bit position of a magnitude with 54 to 116 bits, inside the range
`53..115` that the binary64 product rounder accepts.
-/
private theorem fmaLeading_range (magnitude : FloatLib.Numerics.FixedWord.UInt128)
    (hlower : 2 ^ 53 ≤ magnitude.toNat) (hupper : magnitude.toNat < 2 ^ 116) :
    (fmaLeading magnitude).toNat = magnitude.toNat.log2 ∧
      53 ≤ (fmaLeading magnitude).toNat ∧ (fmaLeading magnitude).toNat ≤ 115 := by
  have hne : magnitude.toNat ≠ 0 := by omega
  have hleading := fmaLeading_toNat magnitude hne hupper
  have hlog := (Nat.log2_lt hne).2 hupper
  refine ⟨hleading, ?_, by omega⟩
  rw [hleading]
  exact (Nat.le_log2 hne).2 hlower

/-! ## Normal operands -/

/--
The scales that the native paths compare, for normal exponent fields: the product's scale, the
addend's scale in the product's coordinate, and the top of the exact window.
-/
private theorem fmaScales_toNat (xExponent yExponent zExponent : UInt64)
    (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < 2047)
    (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < 2047)
    (hzExponent : 0 < zExponent.toNat ∧ zExponent.toNat < 2047) :
    (finiteScale xExponent + finiteScale yExponent).toNat =
        (xExponent.toNat - 1) + (yExponent.toNat - 1) ∧
      (finiteScale zExponent + 1074).toNat = (zExponent.toNat - 1) + 1074 ∧
      (finiteScale xExponent + finiteScale yExponent + 62).toNat =
        (xExponent.toNat - 1) + (yExponent.toNat - 1) + 62 := by
  have hscale (exponent : UInt64) (hexponent : 0 < exponent.toNat) :
      (finiteScale exponent).toNat = exponent.toNat - 1 := by
    have hne : exponent ≠ 0 := by
      rintro rfl
      simp at hexponent
    rw [finiteScale_toNat, ite_eq_right hne]
  have hproduct :
      (finiteScale xExponent + finiteScale yExponent).toNat =
        (xExponent.toNat - 1) + (yExponent.toNat - 1) := by
    rw [UInt64.toNat_add, hscale xExponent hxExponent.1, hscale yExponent hyExponent.1]
    apply Nat.mod_eq_of_lt
    norm_num
    omega
  refine ⟨hproduct, ?_, ?_⟩
  · rw [UInt64.toNat_add, hscale zExponent hzExponent.1]
    apply Nat.mod_eq_of_lt
    change zExponent.toNat - 1 + 1074 < 18446744073709551616
    omega
  · rw [UInt64.toNat_add, hproduct]
    simp only [UInt64.reduceToNat]
    exact Nat.mod_eq_of_lt (by change _ < 18446744073709551616; omega)

/-- Inside the exact window the addend's scale lies `shift ≤ 62` positions above the product's. -/
private theorem exactWindow_shift (productScale addendScale : UInt64) (scale : Nat)
    (hscale : productScale.toNat = scale) (htop : (productScale + 62).toNat = scale + 62)
    (hlow : productScale ≤ addendScale) (hhigh : addendScale ≤ productScale + 62) :
    (addendScale - productScale).toNat ≤ 62 ∧
      scale + (addendScale - productScale).toNat = addendScale.toNat := by
  have hshift := UInt64.toNat_sub_of_le _ _ hlow
  have hlowNat := UInt64.le_iff_toNat_le.mp hlow
  have hhighNat := UInt64.le_iff_toNat_le.mp hhigh
  rw [htop] at hhighNat
  omega

/--
Operands that pass the exponent guard of the native paths are normal: no exponent field is all
ones, each lies in `1..2046`, and each significand has exactly 53 bits.
-/
private theorem fmaOperands_normal (x y z : Value)
    (hguard : ¬(expField (toUInt64 x) == 0 || expField (toUInt64 x) == 0x7ff ||
      expField (toUInt64 y) == 0 || expField (toUInt64 y) == 0x7ff ||
      expField (toUInt64 z) == 0 || expField (toUInt64 z) == 0x7ff) = true) :
    (expField (toUInt64 x) ≠ 0x7ff ∧ expField (toUInt64 y) ≠ 0x7ff ∧
        expField (toUInt64 z) ≠ 0x7ff) ∧
      ((0 < (expField (toUInt64 x)).toNat ∧ (expField (toUInt64 x)).toNat < 2047) ∧
        (0 < (expField (toUInt64 y)).toNat ∧ (expField (toUInt64 y)).toNat < 2047) ∧
        (0 < (expField (toUInt64 z)).toNat ∧ (expField (toUInt64 z)).toNat < 2047)) ∧
      ((2 ^ 52 ≤ (finiteMantissa (expField (toUInt64 x)) (fracField (toUInt64 x))).toNat ∧
          (finiteMantissa (expField (toUInt64 x)) (fracField (toUInt64 x))).toNat < 2 ^ 53) ∧
        (2 ^ 52 ≤ (finiteMantissa (expField (toUInt64 y)) (fracField (toUInt64 y))).toNat ∧
          (finiteMantissa (expField (toUInt64 y)) (fracField (toUInt64 y))).toNat < 2 ^ 53) ∧
        (2 ^ 52 ≤ (finiteMantissa (expField (toUInt64 z)) (fracField (toUInt64 z))).toNat ∧
          (finiteMantissa (expField (toUInt64 z)) (fracField (toUInt64 z))).toNat < 2 ^ 53)) := by
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hguard
  obtain ⟨⟨⟨⟨⟨hxZero, hxExceptional⟩, hyZero⟩, hyExceptional⟩, hzZero⟩, hzExceptional⟩ := hguard
  exact ⟨⟨hxExceptional, hyExceptional, hzExceptional⟩,
    ⟨normalExponent_bounds x hxZero hxExceptional, normalExponent_bounds y hyZero hyExceptional,
      normalExponent_bounds z hzZero hzExceptional⟩,
    ⟨finiteMantissa_bounds _ _ hxZero (fracField_lt x),
      finiteMantissa_bounds _ _ hyZero (fracField_lt y),
      finiteMantissa_bounds _ _ hzZero (fracField_lt z)⟩⟩

/--
The native paths accept only operands without an all-ones exponent, which `decode?` maps to
their fields; there `fmaFiniteComponents?` is the generic component kernel on those fields.
-/
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

/-! ## Scale-aligned component semantics -/

/-- The 128-bit product of two 53-bit significands is their exact product, of 105 or 106 bits. -/
private theorem mul64_normal_bounds (xMantissa yMantissa : UInt64)
    (hxMantissa : 2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53)
    (hyMantissa : 2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53) :
    (FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa).toNat =
        xMantissa.toNat * yMantissa.toNat ∧
      2 ^ 104 ≤ (FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa).toNat ∧
      (FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa).toNat < 2 ^ 106 := by
  rw [FloatLib.Numerics.FixedWord.mul64_toNat]
  refine ⟨rfl, ?_, ?_⟩
  · calc 2 ^ 104 = 2 ^ 52 * 2 ^ 52 := by norm_num
      _ ≤ xMantissa.toNat * yMantissa.toNat := Nat.mul_le_mul hxMantissa.1 hyMantissa.1
  · calc xMantissa.toNat * yMantissa.toNat < 2 ^ 53 * 2 ^ 53 :=
          Nat.mul_lt_mul'' hxMantissa.2 hyMantissa.2
      _ = 2 ^ 106 := by norm_num

/--
On normal components with nonzero significands, the generic FMA kernel aligns the product and the
addend at their unsigned scales.
-/
private theorem fmaComponents_normal
    (xSign ySign zSign : Bool)
    (xExponent yExponent zExponent xMantissa yMantissa zMantissa : Nat)
    (hxExponent : xExponent ≠ 0) (hyExponent : yExponent ≠ 0) (hzExponent : zExponent ≠ 0)
    (hxMantissa : xMantissa ≠ 0) (hyMantissa : yMantissa ≠ 0) (hzMantissa : zMantissa ≠ 0) :
    FiniteKernel.fmaComponents FloatFormat.binary64
        { sign := xSign, exponent := xExponent, mantissa := xMantissa }
        { sign := ySign, exponent := yExponent, mantissa := yMantissa }
        { sign := zSign, exponent := zExponent, mantissa := zMantissa } =
      if (xExponent - 1) + (yExponent - 1) ≤ (zExponent - 1) + 1074 then
        FiniteScaleAdd.roundAligned FloatFormat.binary64 0 zSign (Bool.xor xSign ySign)
          zMantissa (xMantissa * yMantissa)
          ((zExponent - 1) + 1074 - ((xExponent - 1) + (yExponent - 1)))
          ((xExponent - 1) + (yExponent - 1))
      else
        FiniteScaleAdd.roundAligned FloatFormat.binary64 0 (Bool.xor xSign ySign) zSign
          (xMantissa * yMantissa) zMantissa
          ((xExponent - 1) + (yExponent - 1) - ((zExponent - 1) + 1074))
          ((zExponent - 1) + 1074) := by
  rw [← FiniteKernel.Internal.fmaComponents_eq]
  unfold FiniteKernel.Internal.fmaComponents
  rw [ite_eq_left (by decide : FloatFormat.binary64.isIEEE = true)]
  unfold FiniteScaleAdd.roundSum
  have hoffset : FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 := by decide
  simp only [FiniteKernel.scale, hxExponent, hyExponent, hzExponent, beq_iff_eq, ite_false,
    hxMantissa, hyMantissa, hzMantissa, mul_eq_zero, or_self, hoffset]

/--
With opposite signs inside the exact window, the generic kernel rounds the difference of the
product and the aligned addend, with the sign of the larger one.
-/
private theorem fmaComponents_opposite_aligned
    (alignment : Nat) (xSign ySign zSign : Bool)
    (xExponent yExponent zExponent xMantissa yMantissa zMantissa : Nat)
    (hxExponent : xExponent ≠ 0) (hyExponent : yExponent ≠ 0) (hzExponent : zExponent ≠ 0)
    (hxMantissa : xMantissa ≠ 0) (hyMantissa : yMantissa ≠ 0) (hzMantissa : zMantissa ≠ 0)
    (hsign : Bool.xor xSign ySign ≠ zSign)
    (haligned :
      (xExponent - 1) + (yExponent - 1) + alignment =
        (zExponent - 1) + 1074)
    (hne : xMantissa * yMantissa ≠ zMantissa <<< alignment) :
    FiniteKernel.fmaComponents FloatFormat.binary64
        { sign := xSign, exponent := xExponent, mantissa := xMantissa }
        { sign := ySign, exponent := yExponent, mantissa := yMantissa }
        { sign := zSign, exponent := zExponent, mantissa := zMantissa } =
      if xMantissa * yMantissa < zMantissa <<< alignment then
        FiniteProductRound.round FloatFormat.binary64 zSign
          ((zMantissa <<< alignment) - xMantissa * yMantissa)
          ((xExponent - 1) + (yExponent - 1))
      else
        FiniteProductRound.round FloatFormat.binary64 (Bool.xor xSign ySign)
          (xMantissa * yMantissa - (zMantissa <<< alignment))
          ((xExponent - 1) + (yExponent - 1)) := by
  rw [fmaComponents_normal xSign ySign zSign _ _ _ _ _ _ hxExponent hyExponent hzExponent
    hxMantissa hyMantissa hzMantissa]
  have hshift :
      (zExponent - 1) + 1074 - ((xExponent - 1) + (yExponent - 1)) = alignment := by
    omega
  rw [ite_eq_left (by omega), FiniteScaleAdd.roundAligned_eq,
    FiniteScaleAdd.roundMagnitudes_comm]
  unfold FiniteScaleAdd.roundMagnitudes
  rw [ite_eq_right (by simpa only [beq_iff_eq] using hsign), hshift,
    ite_eq_right (by simpa only [beq_iff_eq] using hne)]
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
  let sum := FloatLib.Numerics.FixedWord.add128
    (FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa) (alignFmaAddend zMantissa alignment)
  have hsum :
      sum.value.toNat =
        xMantissa.toNat * yMantissa.toNat + (zMantissa.toNat <<< alignment) := by
    rw [FloatLib.Numerics.FixedWord.add128_value_toNat_of_carry_zero _ _ hcarry,
      FloatLib.Numerics.FixedWord.mul64_toNat,
      alignFmaAddend_toNat zMantissa alignment hzMantissa.2 halignment]
  have hlower : 2 ^ 53 ≤ sum.value.toNat := by
    rw [hsum]
    calc 2 ^ 53 ≤ 2 ^ 52 * 2 ^ 52 := by norm_num
      _ ≤ xMantissa.toNat * yMantissa.toNat := Nat.mul_le_mul hxMantissa.1 hyMantissa.1
      _ ≤ _ := Nat.le_add_right _ _
  have hupper : sum.value.toNat < 2 ^ 116 := by
    have hz := alignFmaAddend_lt zMantissa alignment hzMantissa.2 halignment
    have hxy : xMantissa.toNat * yMantissa.toNat < 2 ^ 106 := by
      obtain ⟨hproduct, -, hupper⟩ := mul64_normal_bounds xMantissa yMantissa hxMantissa hyMantissa
      rwa [hproduct] at hupper
    rw [hsum]
    omega
  obtain ⟨hleading, hleadingRange⟩ := fmaLeading_range sum.value hlower hupper
  rw [← hsum]
  exact roundNormalProduct_refines sign xExponent yExponent sum.value _ hxExponent hyExponent
    hleading hleadingRange result hresult

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
  have hmagnitude : magnitude.toNat = left.toNat - right.toNat :=
    FloatLib.Numerics.FixedWord.UInt128.sub_toNat left right hordered.le
  have hne : magnitude.toNat ≠ 0 := by omega
  have hupper : magnitude.toNat < 2 ^ 116 := by omega
  have hlower : 2 ^ 53 ≤ magnitude.toNat := by
    rw [fmaLeading_toNat magnitude hne hupper] at hleadingMin
    exact (Nat.le_log2 hne).1 hleadingMin
  obtain ⟨hleading, hleadingRange⟩ := fmaLeading_range magnitude hlower hupper
  rw [← hmagnitude]
  exact roundNormalProduct_refines sign xExponent yExponent magnitude _ hxExponent hyExponent
    hleading hleadingRange result hresult

/-! ## Native fast-path refinements -/

private theorem fmaNormalSameSign_refines
    (x y z result : Value)
    (hresult : fmaNormalSameSign? x y z = some result) :
    fmaFiniteComponents? x y z = some result := by
  unfold fmaNormalSameSign? fmaNormalSameSignWord? at hresult
  dsimp only at hresult
  split at hresult
  · simp at hresult
  rename_i hexponents
  obtain ⟨⟨hxExceptional, hyExceptional, hzExceptional⟩, ⟨hxExponent, hyExponent, hzExponent⟩,
    ⟨hxMantissa, hyMantissa, hzMantissa⟩⟩ := fmaOperands_normal x y z hexponents
  apply fmaFiniteComponents?_eq_some_of_components x y z result
    hxExceptional hyExceptional hzExceptional
  set xExponent := expField (toUInt64 x)
  set yExponent := expField (toUInt64 y)
  set zExponent := expField (toUInt64 z)
  set xMantissa := finiteMantissa xExponent (fracField (toUInt64 x))
  set yMantissa := finiteMantissa yExponent (fracField (toUInt64 y))
  set zMantissa := finiteMantissa zExponent (fracField (toUInt64 z))
  obtain ⟨hproductScale, haddendScale, htop⟩ :=
    fmaScales_toNat xExponent yExponent zExponent hxExponent hyExponent hzExponent
  split at hresult
  · simp at hresult
  rename_i hguard
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or, not_not,
    UInt64.not_lt] at hguard
  obtain ⟨⟨hsign, hlow⟩, hhigh⟩ := hguard
  obtain ⟨hshift, hwindow⟩ := exactWindow_shift _ _ _ hproductScale htop hlow hhigh
  set shift :=
    (finiteScale zExponent + 1074 - (finiteScale xExponent + finiteScale yExponent)).toNat
  split at hresult
  · simp at hresult
  rename_i hcarry
  simp only [bne_iff_ne, ne_eq, not_not] at hcarry
  have hrefines :=
    roundNormalFma_refines _ xExponent yExponent xMantissa yMantissa zMantissa shift hshift
      hxExponent hyExponent hxMantissa hyMantissa hzMantissa result hcarry hresult
  have haligned :
      (xExponent.toNat - 1) + (yExponent.toNat - 1) + shift = (zExponent.toNat - 1) + 1074 := by
    omega
  rw [← hsign]
  exact (FiniteKernel.fmaComponents_sameSign_aligned FloatFormat.binary64 (by decide) shift
    (signBit (toUInt64 x)) (signBit (toUInt64 y))
    xExponent.toNat yExponent.toNat zExponent.toNat
    xMantissa.toNat yMantissa.toNat zMantissa.toNat
    (by omega) (by omega) haligned).trans
    hrefines.symm

private theorem fmaNormalOppositeSign_refines
    (x y z result : Value)
    (hresult : fmaNormalOppositeSign? x y z = some result) :
    fmaFiniteComponents? x y z = some result := by
  unfold fmaNormalOppositeSign? fmaNormalOppositeSignWord? at hresult
  dsimp only at hresult
  split at hresult
  · simp at hresult
  rename_i hexponents
  obtain ⟨⟨hxExceptional, hyExceptional, hzExceptional⟩, ⟨hxExponent, hyExponent, hzExponent⟩,
    ⟨hxMantissa, hyMantissa, hzMantissa⟩⟩ := fmaOperands_normal x y z hexponents
  apply fmaFiniteComponents?_eq_some_of_components x y z result
    hxExceptional hyExceptional hzExceptional
  set xExponent := expField (toUInt64 x)
  set yExponent := expField (toUInt64 y)
  set zExponent := expField (toUInt64 z)
  set xMantissa := finiteMantissa xExponent (fracField (toUInt64 x))
  set yMantissa := finiteMantissa yExponent (fracField (toUInt64 y))
  set zMantissa := finiteMantissa zExponent (fracField (toUInt64 z))
  obtain ⟨hproductScale, haddendScale, htop⟩ :=
    fmaScales_toNat xExponent yExponent zExponent hxExponent hyExponent hzExponent
  set productScale := finiteScale xExponent + finiteScale yExponent
  set zProductScale := finiteScale zExponent + 1074
  set productSign := Bool.xor (signBit (toUInt64 x)) (signBit (toUInt64 y))
  set zSign := signBit (toUInt64 z)
  split at hresult
  · simp at hresult
  rename_i hguard
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or,
    UInt64.not_lt] at hguard
  obtain ⟨⟨hsign, hlow⟩, hhigh⟩ := hguard
  obtain ⟨hshift, hwindow⟩ := exactWindow_shift _ _ _ hproductScale htop hlow hhigh
  set shift := (zProductScale - productScale).toNat
  set product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  set aligned := alignFmaAddend zMantissa shift
  have haligned :
      (xExponent.toNat - 1) + (yExponent.toNat - 1) + shift = (zExponent.toNat - 1) + 1074 := by
    omega
  split at hresult
  · simp at hresult
  rename_i hproductNe
  have hproduct : product.toNat = xMantissa.toNat * yMantissa.toNat := by simp [product]
  have halignedValue : aligned.toNat = zMantissa.toNat <<< shift :=
    alignFmaAddend_toNat zMantissa shift hzMantissa.2 hshift
  have hnatNe : product.toNat ≠ aligned.toNat := by
    intro heq
    apply hproductNe
    simp [FloatLib.Numerics.FixedWord.UInt128.toNat_injective heq]
  have hproductUpper : product.toNat < 2 ^ 116 :=
    (mul64_normal_bounds xMantissa yMantissa hxMantissa hyMantissa).2.2.trans (by norm_num)
  have halignedUpper : aligned.toNat < 2 ^ 116 := by
    rw [halignedValue]
    exact lt_trans (alignFmaAddend_lt zMantissa shift hzMantissa.2 hshift) (by norm_num)
  rw [fmaComponents_opposite_aligned shift (signBit (toUInt64 x)) (signBit (toUInt64 y)) zSign
    xExponent.toNat yExponent.toNat zExponent.toNat
    xMantissa.toNat yMantissa.toNat zMantissa.toNat
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hsign haligned
    (by rwa [← hproduct, ← halignedValue])]
  by_cases hless : FloatLib.Numerics.FixedWord.UInt128.less product aligned = true
  · -- The aligned addend is larger: round `aligned - product` with the addend's sign.
    have hordered : product.toNat < aligned.toNat :=
      (FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff product aligned).mp hless
    simp only [hless, ite_true] at hresult
    split at hresult
    · simp at hresult
    rename_i hleadingRaw
    have hleadingMin := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hleadingRaw)
    have hlt : xMantissa.toNat * yMantissa.toNat < zMantissa.toNat <<< shift := by
      rwa [hproduct, halignedValue] at hordered
    rw [ite_eq_left hlt, ← halignedValue, ← hproduct]
    exact (roundNormalFmaDifference_refines zSign xExponent yExponent aligned product
      hxExponent hyExponent hordered halignedUpper (by simpa using hleadingMin) result
      hresult).symm
  · -- The product is larger: round `product - aligned` with the product's sign.
    have hordered : aligned.toNat < product.toNat := by
      have hnotLt : ¬product.toNat < aligned.toNat := fun hlt =>
        hless ((FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff product aligned).mpr hlt)
      omega
    simp only [hless, Bool.false_eq_true, ite_false] at hresult
    split at hresult
    · simp at hresult
    rename_i hleadingRaw
    have hleadingMin := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hleadingRaw)
    have hnotLt : ¬xMantissa.toNat * yMantissa.toNat < zMantissa.toNat <<< shift := by
      rw [← hproduct, ← halignedValue]
      omega
    rw [ite_eq_right hnotLt, ← hproduct, ← halignedValue]
    exact (roundNormalFmaDifference_refines productSign xExponent yExponent product aligned
      hxExponent hyExponent hordered hproductUpper (by simpa using hleadingMin) result
      hresult).symm

/-! ## Sticky alignment outside the exact window -/

/--
The addend's alignment below the product: the low word of a right shift by a machine-word gap,
zero from 64 on, is the quotient by `2 ^ gap`.
-/
private theorem shiftRightGap_toNat (value gap : UInt64) :
    ({ hi := 0, lo := if gap < 64 then value >>> gap else 0 } : UInt128).toNat =
      value.toNat / 2 ^ gap.toNat := by
  have hlow : (if gap < 64 then value >>> gap else 0).toNat = value.toNat / 2 ^ gap.toNat := by
    split
    · rename_i hsmall
      have hsmallNat : gap.toNat < 64 := by simpa using UInt64.lt_iff_toNat_lt.mp hsmall
      rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hsmallNat]
    · rename_i hlarge
      have hlargeNat : 64 ≤ gap.toNat := by
        simpa using UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hlarge)
      rw [UInt64.toNat_zero, eq_comm, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
      exact value.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) hlargeNat)
  rw [← hlow]
  simp [UInt128.toNat]

/--
The exactness test of that alignment: shifting back recovers a nonzero value exactly when the
discarded bits are zero.
-/
private theorem shiftRightGap_exact (value gap : UInt64) (hvalue : value.toNat ≠ 0) :
    (decide (gap < 64) && (if gap < 64 then value >>> gap else 0) <<< gap == value) =
      decide (value.toNat % 2 ^ gap.toNat = 0) := by
  by_cases hsmall : gap < 64
  · have hsmallNat : gap.toNat < 64 := by simpa using UInt64.lt_iff_toNat_lt.mp hsmall
    simp only [hsmall, decide_true, ite_true, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftLeft,
      UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hsmallNat,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have hle : value.toNat / 2 ^ gap.toNat * 2 ^ gap.toNat ≤ value.toNat :=
      Nat.div_mul_le_self _ _
    rw [Nat.mod_eq_of_lt (hle.trans_lt value.toNat_lt)]
    have := Nat.div_add_mod' value.toNat (2 ^ gap.toNat)
    omega
  · have hlargeNat : 64 ≤ gap.toNat := by
      simpa using UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hsmall)
    simp only [hsmall, decide_false, Bool.false_and]
    symm
    rw [decide_eq_false_iff_not, Nat.mod_eq_of_lt
      (value.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) hlargeNat))]
    exact hvalue

/--
The exactness test of the product's alignment: shifting a nonzero two-word value right by
`discard` and back recovers it exactly when the discarded bits are zero.
-/
private theorem shiftRight128_exact (value : UInt128) (discard : UInt64)
    (hvalue : value.toNat ≠ 0) :
    (decide (discard < 128) &&
        (UInt128.shiftLeft (UInt128.shiftRight value discard.toNat) discard.toNat).hi ==
          value.hi &&
        (UInt128.shiftLeft (UInt128.shiftRight value discard.toNat) discard.toNat).lo ==
          value.lo) =
      decide (value.toNat % 2 ^ discard.toNat = 0) := by
  have hdecomp := Nat.div_add_mod' value.toNat (2 ^ discard.toNat)
  by_cases hsmall : discard < 128
  · have hsmallNat : discard.toNat < 128 := by simpa using UInt64.lt_iff_toNat_lt.mp hsmall
    have hle : value.toNat / 2 ^ discard.toNat * 2 ^ discard.toNat ≤ value.toNat :=
      Nat.div_mul_le_self _ _
    have hshifted :
        (UInt128.shiftLeft (UInt128.shiftRight value discard.toNat) discard.toNat).toNat =
          value.toNat / 2 ^ discard.toNat * 2 ^ discard.toNat := by
      rw [UInt128.shiftLeft_toNat _ _ (by
        rw [UInt128.shiftRight_toNat, Nat.shiftLeft_eq]
        exact hle.trans_lt value.toNat_lt), UInt128.shiftRight_toNat, Nat.shiftLeft_eq]
    simp only [hsmall, decide_true, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨hhi, hlo⟩
      have hback :
          (UInt128.shiftLeft (UInt128.shiftRight value discard.toNat)
            discard.toNat).toNat = value.toNat := by
        unfold UInt128.toNat
        rw [hhi, hlo]
      omega
    · intro hzero
      have heq :
          UInt128.shiftLeft (UInt128.shiftRight value discard.toNat) discard.toNat = value := by
        apply UInt128.toNat_injective
        omega
      rw [heq]
      exact ⟨rfl, rfl⟩
  · have hlargeNat : 128 ≤ discard.toNat := by
      simpa using UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hsmall)
    simp only [hsmall, decide_false, Bool.false_and]
    symm
    rw [decide_eq_false_iff_not, Nat.mod_eq_of_lt
      (value.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) hlargeNat))]
    exact hvalue

/-- The addend kept with three guard positions: its significand shifted left by three. -/
private theorem guardedAddend_toNat (mantissa : UInt64) (hmantissa : mantissa.toNat < 2 ^ 53) :
    ({ hi := 0, lo := mantissa <<< 3 } : UInt128).toNat = mantissa.toNat * 2 ^ 3 := by
  have hfit : mantissa.toNat <<< 3 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    calc mantissa.toNat * 2 ^ 3 < 2 ^ 53 * 2 ^ 3 :=
          Nat.mul_lt_mul_of_pos_right hmantissa (by decide)
      _ ≤ 2 ^ 64 := by norm_num
  have hshift : (mantissa <<< 3).toNat = mantissa.toNat * 2 ^ 3 := by
    simpa [Nat.shiftLeft_eq] using
      FloatLib.Numerics.FixedWord.shiftLeft_toNat mantissa 3 hfit
  rw [← hshift]
  simp [UInt128.toNat]

/--
A term `dominant * 2 ^ k` with `2 ^ (a + 1) ≤ dominant < 2 ^ b` absorbs a second term of at most
`2 ^ (a + k)`: their sum or difference is at least `2 ^ (a + k)`, and its quotient by `2 ^ k` is
below `2 ^ (b + 1)`.
-/
private theorem dominantSum_bounds (same : Bool) (dominant other a b k : Nat)
    (hlower : 2 ^ (a + 1) ≤ dominant) (hupper : dominant < 2 ^ b)
    (hother : other ≤ 2 ^ (a + k)) :
    2 ^ (a + k) ≤ (if same then dominant * 2 ^ k + other else dominant * 2 ^ k - other) ∧
      (if same then dominant * 2 ^ k + other else dominant * 2 ^ k - other) / 2 ^ k <
        2 ^ (b + 1) := by
  have hpow : 0 < 2 ^ k := Nat.two_pow_pos k
  have hpos : 0 < 2 ^ (a + k) := Nat.two_pow_pos (a + k)
  have hdominantLower : 2 * 2 ^ (a + k) ≤ dominant * 2 ^ k := by
    calc 2 * 2 ^ (a + k) = 2 ^ (a + 1) * 2 ^ k := by
          rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
          ring
      _ ≤ dominant * 2 ^ k := Nat.mul_le_mul_right _ hlower
  have hdominantUpper : dominant * 2 ^ k < 2 ^ b * 2 ^ k :=
    Nat.mul_lt_mul_of_pos_right hupper hpow
  have hsplit : 2 ^ (b + 1) * 2 ^ k = 2 * (2 ^ b * 2 ^ k) := by
    rw [Nat.pow_succ]
    ring
  refine ⟨by split <;> omega, ?_⟩
  rw [Nat.div_lt_iff_lt_mul hpow, hsplit]
  split <;> omega

/--
A sticky right shift by `k` keeps the leading bit of a value: from `2 ^ (a + k) ≤ n` and
`n / 2 ^ k < 2 ^ b` it lies in `[2 ^ a, 2 ^ b)`.
-/
private theorem shiftRightJam_bounds (n k a b : Nat) (hlower : 2 ^ (a + k) ≤ n)
    (hupper : n / 2 ^ k < 2 ^ b) (hb : 0 < b) :
    2 ^ a ≤ Numerics.shiftRightJam n k ∧ Numerics.shiftRightJam n k < 2 ^ b := by
  constructor
  · refine le_trans ?_ (Numerics.div_two_pow_le_shiftRightJam n k)
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
    exact hlower
  · unfold Numerics.shiftRightJam
    dsimp only
    split
    · exact hupper
    · exact Nat.or_lt_two_pow hupper (Nat.one_lt_two_pow (by omega))

/--
A sticky magnitude of a dominated sum, as in `dominantSum_bounds`, has its leading bit in the
range `53..115` of the binary64 product rounder; the exact sum keeps at least `a + k + 1` bits.
-/
private theorem jammedSum_leading (same : Bool) (dominant other a b k : Nat)
    (magnitude : UInt128)
    (hlower : 2 ^ (a + 1) ≤ dominant) (hupper : dominant < 2 ^ b)
    (hother : other ≤ 2 ^ (a + k)) (ha : 53 ≤ a) (hb : b + 1 ≤ 116)
    (hmagnitude : magnitude.toNat = Numerics.shiftRightJam
      (if same then dominant * 2 ^ k + other else dominant * 2 ^ k - other) k) :
    2 ^ (a + k) ≤ (if same then dominant * 2 ^ k + other else dominant * 2 ^ k - other) ∧
      (fmaLeading magnitude).toNat = magnitude.toNat.log2 ∧
      53 ≤ (fmaLeading magnitude).toNat ∧ (fmaLeading magnitude).toNat ≤ 115 := by
  obtain ⟨hsumLower, hsumUpper⟩ := dominantSum_bounds same dominant other a b k hlower hupper hother
  obtain ⟨hmagnitudeLower, hmagnitudeUpper⟩ :=
    shiftRightJam_bounds _ k a (b + 1) hsumLower hsumUpper (by omega)
  rw [← hmagnitude] at hmagnitudeLower hmagnitudeUpper
  exact ⟨hsumLower, fmaLeading_range _
    ((Nat.pow_le_pow_right (by decide) ha).trans hmagnitudeLower)
    (hmagnitudeUpper.trans_le (Nat.pow_le_pow_right (by decide) hb))⟩

/--
Rounding the sticky right shift by `k` of a value with more than `k + 54` bits, at scale
`scale + k`, is rounding the value itself at `scale`.
-/
private theorem round_shiftRightJam_of_le (sign : Bool) (n scale k : Nat)
    (hn : 2 ^ (54 + k) ≤ n) :
    FiniteProductRound.round FloatFormat.binary64 sign (Numerics.shiftRightJam n k) (scale + k) =
      FiniteProductRound.round FloatFormat.binary64 sign n scale := by
  apply FiniteProductRound.round_shiftRightJam
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp ((Nat.two_pow_pos _).trans_le hn)
  have := (Nat.le_log2 hne).2 hn
  change k + 52 + 2 ≤ n.log2
  omega

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
  rw [fmaComponents_normal xSign ySign zSign _ _ _ _ _ _ hxExponent hyExponent hzExponent
    hxMantissa hyMantissa hzMantissa]
  rw [ite_eq_right (by omega), FiniteScaleAdd.roundAligned_eq]
  unfold FiniteScaleAdd.roundMagnitudes FiniteScaleAdd.roundMagnitude
  rw [Nat.shiftLeft_eq, Nat.add_zero]
  by_cases hsign : Bool.xor xSign ySign = zSign
  · simp only [hsign, beq_self_eq_true, ite_true]
  · have hsignBeq : (Bool.xor xSign ySign == zSign) = false := by simpa using hsign
    have hne : xMantissa * yMantissa *
        2 ^ ((xExponent - 1) + (yExponent - 1) - ((zExponent - 1) + 1074)) ≠ zMantissa := by
      omega
    simp only [hsignBeq, Bool.false_eq_true, ite_false, beq_iff_eq, hne,
      Nat.not_lt_of_ge hdominant.le]

/--
With the addend's scale at or above the product's and the shifted addend larger than the product
(`hdominant`), the generic kernel rounds the exact sum at the product's scale. The scale gap may be
zero; its one use, `fmaJammedAbove_eq`, has a gap above 62.
-/
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
  rw [fmaComponents_normal xSign ySign zSign _ _ _ _ _ _ hxExponent hyExponent hzExponent
    hxMantissa hyMantissa hzMantissa]
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
    simp only [hsignBeq, Bool.false_eq_true, ite_false, beq_iff_eq, hne, Nat.add_zero,
      Nat.not_lt_of_ge hdominant.le]


/--
The sticky path for an addend `gap` scale positions below the product. The addend's significand is
shifted right by `gap` with a sticky bit, and the product dominates the sum, so the sticky
magnitude rounds like the exact sum at the addend's scale.
-/
private theorem fmaJammedBelow_eq (xSign ySign zSign : Bool)
    (xExponent yExponent zExponent xMantissa yMantissa zMantissa : UInt64)
    (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < 2047)
    (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < 2047)
    (hzExponent : 0 < zExponent.toNat ∧ zExponent.toNat < 2047)
    (hxMantissa : 2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53)
    (hyMantissa : 2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53)
    (hzMantissa : 2 ^ 52 ≤ zMantissa.toNat ∧ zMantissa.toNat < 2 ^ 53)
    (hbelow : finiteScale zExponent + 1074 < finiteScale xExponent + finiteScale yExponent)
    (result : Value)
    (hresult :
      let gap := finiteScale xExponent + finiteScale yExponent - (finiteScale zExponent + 1074)
      let lower := if gap < 64 then zMantissa >>> gap else 0
      let magnitude := UInt128.jamCombine (Bool.xor xSign ySign == zSign)
        (gap < 64 && lower <<< gap == zMantissa)
        (FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa) ⟨0, lower⟩
      roundNormalProduct? (Bool.xor xSign ySign) xExponent yExponent magnitude
        (fmaLeading magnitude) = some result) :
    FiniteKernel.fmaComponents FloatFormat.binary64
        { sign := xSign, exponent := xExponent.toNat, mantissa := xMantissa.toNat }
        { sign := ySign, exponent := yExponent.toNat, mantissa := yMantissa.toNat }
        { sign := zSign, exponent := zExponent.toNat, mantissa := zMantissa.toNat } =
      result := by
  dsimp only at hresult
  obtain ⟨hproductScale, haddendScale, -⟩ :=
    fmaScales_toNat xExponent yExponent zExponent hxExponent hyExponent hzExponent
  set productScale := finiteScale xExponent + finiteScale yExponent
  set addendScale := finiteScale zExponent + 1074
  set product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  obtain ⟨hproduct, hproductLower, hproductUpper⟩ :
      product.toNat = xMantissa.toNat * yMantissa.toNat ∧ 2 ^ 104 ≤ product.toNat ∧
        product.toNat < 2 ^ 106 :=
    mul64_normal_bounds xMantissa yMantissa hxMantissa hyMantissa
  have hbelowNat : addendScale.toNat < productScale.toNat := UInt64.lt_iff_toNat_lt.mp hbelow
  set gap := productScale.toNat - addendScale.toNat with hgapDef
  have hgap : (productScale - addendScale).toNat = gap :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hbelow)
  -- Alignment: the addend's quotient by `2 ^ gap`, and whether that division is exact.
  have hlower := shiftRightGap_toNat zMantissa (productScale - addendScale)
  have hexact := shiftRightGap_exact zMantissa (productScale - addendScale) (by omega)
  rw [hgap] at hlower hexact
  have hlowerSmall : zMantissa.toNat / 2 ^ gap < 2 ^ 53 :=
    (Nat.div_le_self _ _).trans_lt hzMantissa.2
  have hmagnitude := UInt128.jamCombine_toNat (Bool.xor xSign ySign == zSign) _ product _
    zMantissa.toNat gap hlower hexact (fun _ => by omega) (fun _ =>
      (show zMantissa.toNat ≤ product.toNat by omega).trans
        (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))
  -- The product dominates the exact sum, so the sticky magnitude keeps its leading bit.
  obtain ⟨hsumLower, hleading, hleadingRange⟩ := jammedSum_leading
    (Bool.xor xSign ySign == zSign) product.toNat zMantissa.toNat 103 106 gap _
    hproductLower hproductUpper
    (hzMantissa.2.le.trans (Nat.pow_le_pow_right (by decide) (by omega))) (by decide)
    (by decide) hmagnitude
  -- Rounding: the native rounder rounds the sticky magnitude like the exact sum.
  have hrefines := roundNormalProduct_refines (Bool.xor xSign ySign) xExponent yExponent _ _
    hxExponent hyExponent hleading hleadingRange result hresult
  have hscale :
      (xExponent.toNat - 1) + (yExponent.toNat - 1) = ((zExponent.toNat - 1) + 1074) + gap := by
    omega
  rw [hscale, hmagnitude, round_shiftRightJam_of_le _ _ _ _
    ((Nat.pow_le_pow_right (by decide) (by omega)).trans hsumLower)] at hrefines
  have hgapNat :
      gap = (xExponent.toNat - 1) + (yExponent.toNat - 1) - ((zExponent.toNat - 1) + 1074) := by
    omega
  rw [fmaComponents_addend_below xSign ySign zSign
    xExponent.toNat yExponent.toNat zExponent.toNat
    xMantissa.toNat yMantissa.toNat zMantissa.toNat
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rw [← hgapNat, ← hproduct]
      calc zMantissa.toNat < 2 ^ 104 := hzMantissa.2.trans (by norm_num)
        _ ≤ product.toNat := hproductLower
        _ ≤ product.toNat * 2 ^ gap := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)),
    hrefines, ← hgapNat, ← hproduct]

/--
The sticky path for an addend more than 62 scale positions above the product. The addend keeps
three guard positions, the product is shifted right below them with a sticky bit, and the addend
dominates the sum, so the sticky magnitude rounds like the exact sum at the product's scale.
-/
private theorem fmaJammedAbove_eq (xSign ySign zSign : Bool)
    (xExponent yExponent zExponent xMantissa yMantissa zMantissa : UInt64)
    (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < 2047)
    (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < 2047)
    (hzExponent : 0 < zExponent.toNat ∧ zExponent.toNat < 2047)
    (hxMantissa : 2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53)
    (hyMantissa : 2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53)
    (hzMantissa : 2 ^ 52 ≤ zMantissa.toNat ∧ zMantissa.toNat < 2 ^ 53)
    (habove : finiteScale xExponent + finiteScale yExponent + 62 < finiteScale zExponent + 1074)
    (result : Value)
    (hresult :
      let productScale := finiteScale xExponent + finiteScale yExponent
      let discard := finiteScale zExponent + 1074 - productScale - 3
      let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
      let lower := FloatLib.Numerics.FixedWord.UInt128.shiftRight product discard.toNat
      let shifted := FloatLib.Numerics.FixedWord.UInt128.shiftLeft lower discard.toNat
      let magnitude := UInt128.jamCombine (Bool.xor xSign ySign == zSign)
        (discard < 128 && shifted.hi == product.hi && shifted.lo == product.lo)
        ⟨0, zMantissa <<< 3⟩ lower
      roundScaled? zSign (productScale + discard) magnitude (fmaLeading magnitude) =
        some result) :
    FiniteKernel.fmaComponents FloatFormat.binary64
        { sign := xSign, exponent := xExponent.toNat, mantissa := xMantissa.toNat }
        { sign := ySign, exponent := yExponent.toNat, mantissa := yMantissa.toNat }
        { sign := zSign, exponent := zExponent.toNat, mantissa := zMantissa.toNat } =
      result := by
  dsimp only at hresult
  obtain ⟨hproductScale, haddendScale, htop⟩ :=
    fmaScales_toNat xExponent yExponent zExponent hxExponent hyExponent hzExponent
  set productScale := finiteScale xExponent + finiteScale yExponent
  set addendScale := finiteScale zExponent + 1074
  set product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  obtain ⟨hproduct, hproductLower, hproductUpper⟩ :
      product.toNat = xMantissa.toNat * yMantissa.toNat ∧ 2 ^ 104 ≤ product.toNat ∧
        product.toNat < 2 ^ 106 :=
    mul64_normal_bounds xMantissa yMantissa hxMantissa hyMantissa
  have hfar : productScale.toNat + 62 < addendScale.toNat := by
    have := UInt64.lt_iff_toNat_lt.mp habove
    rw [htop] at this
    omega
  set s := addendScale.toNat - productScale.toNat with hs
  set d := s - 3 with hd
  have hsWord : (addendScale - productScale).toNat = s :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
  have hdiscard : (addendScale - productScale - 3).toNat = d := by
    rw [UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr (by rw [hsWord]; simp; omega)), hsWord]
    rfl
  -- Alignment: the addend with three guard positions, the product's quotient by `2 ^ d`, and
  -- whether that division is exact.
  let upper : UInt128 := ⟨0, zMantissa <<< 3⟩
  have hupper : upper.toNat = zMantissa.toNat * 2 ^ 3 :=
    guardedAddend_toNat zMantissa hzMantissa.2
  have hupperLower : 2 ^ 55 ≤ upper.toNat := by
    rw [hupper]
    calc 2 ^ 55 = 2 ^ 52 * 2 ^ 3 := by norm_num
      _ ≤ zMantissa.toNat * 2 ^ 3 := Nat.mul_le_mul_right _ hzMantissa.1
  have hupperUpper : upper.toNat < 2 ^ 56 := by
    rw [hupper]
    calc zMantissa.toNat * 2 ^ 3 < 2 ^ 53 * 2 ^ 3 :=
          Nat.mul_lt_mul_of_pos_right hzMantissa.2 (by decide)
      _ = 2 ^ 56 := by norm_num
  have hlower :
      (UInt128.shiftRight product (addendScale - productScale - 3).toNat).toNat =
        product.toNat / 2 ^ d := by
    rw [UInt128.shiftRight_toNat, hdiscard]
  have hexact := (shiftRight128_exact product (addendScale - productScale - 3)
    (by omega)).trans (by rw [hdiscard])
  have hlowerSmall : product.toNat / 2 ^ d < 2 ^ 46 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact hproductUpper.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hproductLe : product.toNat ≤ upper.toNat * 2 ^ d := by
    calc product.toNat ≤ 2 ^ 106 := hproductUpper.le
      _ ≤ 2 ^ 55 * 2 ^ d := by
        rw [← Nat.pow_add]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ upper.toNat * 2 ^ d := Nat.mul_le_mul_right _ hupperLower
  have hmagnitude := UInt128.jamCombine_toNat (Bool.xor xSign ySign == zSign) _ upper _
    product.toNat d hlower hexact (fun _ => by omega) (fun _ => hproductLe)
  -- The addend dominates the exact sum, so the sticky magnitude keeps its leading bit.
  obtain ⟨hsumLower, hleading, hleadingRange⟩ := jammedSum_leading
    (Bool.xor xSign ySign == zSign) upper.toNat product.toNat 54 56 d _ hupperLower hupperUpper
    (hproductUpper.le.trans (Nat.pow_le_pow_right (by decide) (by omega))) (by decide)
    (by decide) hmagnitude
  -- Rounding: the native rounder rounds the sticky magnitude like the exact sum.
  have hscale : (productScale + (addendScale - productScale - 3)).toNat =
      productScale.toNat + d := by
    rw [UInt64.toNat_add, hdiscard]
    exact Nat.mod_eq_of_lt (by change _ < 18446744073709551616; omega)
  have hrefines := roundScaled_refines zSign (productScale + (addendScale - productScale - 3))
    _ _ (by rw [hscale]; omega) hleading hleadingRange result hresult
  rw [hscale, hmagnitude, round_shiftRightJam_of_le _ _ _ _ hsumLower] at hrefines
  have hsNat : s = (zExponent.toNat - 1) + 1074 -
      ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
    omega
  have hshifted : upper.toNat * 2 ^ d = zMantissa.toNat * 2 ^ s := by
    rw [hupper, Nat.mul_assoc, ← Nat.pow_add, show 3 + d = s by omega]
  rw [fmaComponents_addend_above xSign ySign zSign
      xExponent.toNat yExponent.toNat zExponent.toNat
      xMantissa.toNat yMantissa.toNat zMantissa.toNat
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by
        rw [← hsNat, ← hproduct]
        calc product.toNat < 2 ^ 106 := hproductUpper
          _ ≤ 2 ^ (52 + s) := Nat.pow_le_pow_right (by decide) (by omega)
          _ ≤ zMantissa.toNat * 2 ^ s := by
            rw [Nat.pow_add]
            exact Nat.mul_le_mul_right _ hzMantissa.1),
      hrefines, ← hsNat, ← hproduct, ← hproductScale, hshifted]
  have hcomm : ∀ a b : Bool, (a == b) = (b == a) := by decide
  rw [hcomm zSign]

/-- The sticky paths: an addend below the product, or more than 62 positions above it. -/
private theorem fmaJammed_refines
    (x y z result : Value)
    (hresult : fmaJammed? x y z = some result) :
    fmaFiniteComponents? x y z = some result := by
  unfold fmaJammed? fmaJammedWord? at hresult
  dsimp only at hresult
  split at hresult
  · simp at hresult
  rename_i hexponents
  obtain ⟨⟨hxExceptional, hyExceptional, hzExceptional⟩, ⟨hxExponent, hyExponent, hzExponent⟩,
    ⟨hxMantissa, hyMantissa, hzMantissa⟩⟩ := fmaOperands_normal x y z hexponents
  apply fmaFiniteComponents?_eq_some_of_components x y z result
    hxExceptional hyExceptional hzExceptional
  split at hresult
  · rename_i hbelow
    exact fmaJammedBelow_eq _ _ _ _ _ _ _ _ _ hxExponent hyExponent hzExponent
      hxMantissa hyMantissa hzMantissa hbelow result hresult
  · split at hresult
    · rename_i habove
      exact fmaJammedAbove_eq _ _ _ _ _ _ _ _ _ hxExponent hyExponent hzExponent
        hxMantissa hyMantissa hzMantissa habove result hresult
    · simp at hresult

/--
Native finite binary64 FMA, with its fallback, equals the generic finite kernel on every input.

Both sides are `none` exactly when an operand is not finite; on finite operands they return the
same once-rounded value.
-/
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
