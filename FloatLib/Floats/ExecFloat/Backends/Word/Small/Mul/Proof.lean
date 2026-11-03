/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Mul.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
import FloatLib.Floats.ExecFloat.Backends.Word.NormalPair.Proof
import FloatLib.Floats.ExecFloat.Backends.Word.ProductRound.Proof
import Mathlib.Tactic.Positivity.Finset

/-!
# Correctness of native one-word finite multiplication

The one-word kernel declines with a high-bit sentinel outside its guarded normal-result region.
The sentinel never collides with a valid packed result, and the main refinement identifies every
accepted result with the format-generic finite multiplication kernel.

`Mul.Runtime` has a word-valued and an optional entry point. Because they agree, the dispatcher
can use the sentinel form and fall back to the generic implementation on a decline.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordMul

open NativeSmallWord

/-- Natural-number value of the one-word decline sentinel. -/
@[simp] theorem declineWord_toNat :
    declineWord.toNat = 2 ^ 63 := by
  decide

/--
The word-valued normal-product result decodes to the optional result.

Since the high decline bit is outside every eligible storage word, successful packed results
cannot collide with the sentinel.
-/
theorem roundNormalProductWord_decode
    (fmt : FloatFormat)
    (hstorage : fmt.bitWidth ≤ 63)
    (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : UInt64) :
    (if roundNormalProductWord fmt sign
          xExponent yExponent xMantissa yMantissa == declineWord then
        none
      else
        some <| NativeSmallWord.ofWord <|
          roundNormalProductWord fmt sign
            xExponent yExponent xMantissa yMantissa) =
      roundNormalProduct? fmt sign
        xExponent yExponent xMantissa yMantissa := by
  unfold roundNormalProductWord roundNormalProduct?
  simp only [FloatLib.Numerics.FixedWord.log2Word_eq_log2]
  let product := xMantissa * yMantissa
  let leading := product.log2
  let scale := (xExponent - 1) + (yExponent - 1)
  let position := leading + scale
  let normalThreshold :=
    (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1)
  by_cases hsubnormal : position < normalThreshold
  · simp [product, leading, scale, position, normalThreshold, hsubnormal]
  let rounded :=
    FloatLib.Numerics.FixedWord.roundShiftRightEven product
      (leading - UInt64.ofNat fmt.fracWidth).toNat
  have hdecline :
      2 ^ fmt.bitWidth ≤ declineWord.toNat := by
    rw [declineWord_toNat]
    exact Nat.pow_le_pow_right (by decide) hstorage
  simpa [roundNormalProductWord, roundNormalProduct?, product, leading,
    scale, position, normalThreshold, rounded, hsubnormal] using
    NativeWordProduct.finishWord_decode
      fmt declineWord hdecline sign position rounded

private theorem roundNormalProduct_eq_spec
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 31)
    (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : UInt64)
    (hxExponent :
      0 < xExponent.toNat ∧ xExponent.toNat < 2 ^ fmt.expWidth)
    (hyExponent :
      0 < yExponent.toNat ∧ yExponent.toNat < 2 ^ fmt.expWidth)
    (hxMantissa :
      2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧
        xMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hyMantissa :
      2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧
        yMantissa.toNat < 2 ^ (fmt.fracWidth + 1)) :
    roundNormalProduct? fmt sign xExponent yExponent xMantissa yMantissa =
      FiniteProductRound.normalSpec? fmt sign xExponent.toNat yExponent.toNat
        xMantissa.toNat yMantissa.toNat := by
  have hpowFrac : 2 ^ (fmt.fracWidth + 1) ≤ 2 ^ 32 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hxMantissa32 : xMantissa.toNat < 2 ^ 32 := hxMantissa.2.trans_le hpowFrac
  have hyMantissa32 : yMantissa.toNat < 2 ^ 32 := hyMantissa.2.trans_le hpowFrac
  have hproductFit : xMantissa.toNat * yMantissa.toNat < 2 ^ 64 := by
    nlinarith [hxMantissa32, hyMantissa32]
  have hproduct : (xMantissa * yMantissa).toNat = xMantissa.toNat * yMantissa.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hproductFit]
  have hproductLower := (FiniteProductRound.normalizedProduct_bounds fmt hxMantissa hyMantissa).1
  have hproductNe : xMantissa.toNat * yMantissa.toNat ≠ 0 :=
    Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hproductLower)
  have hleading :
      (xMantissa * yMantissa).log2.toNat = (xMantissa.toNat * yMantissa.toNat).log2 := by
    rw [FloatLib.Numerics.FixedWord.log2_toNat, hproduct]
  have hfracLeading : fmt.fracWidth ≤ (xMantissa.toNat * yMantissa.toNat).log2 := by
    have hlower := (Nat.le_log2 hproductNe).2 hproductLower
    omega
  have hfracWord : (UInt64.ofNat fmt.fracWidth).toNat = fmt.fracWidth := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    omega
  have hshift :
      ((xMantissa * yMantissa).log2 - UInt64.ofNat fmt.fracWidth).toNat =
        (xMantissa.toNat * yMantissa.toNat).log2 - fmt.fracWidth := by
    rw [UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr (by rw [hfracWord, hleading]; omega)), hleading, hfracWord]
  unfold roundNormalProduct?
  simp only [FloatLib.Numerics.FixedWord.log2Word_eq_log2]
  exact NativeWordProduct.normal_eq_normalSpec fmt hwidth (by omega) (by omega) sign
    xExponent yExponent xMantissa yMantissa hxExponent hyExponent hxMantissa hyMantissa _ _ _
    hleading (normalThreshold_toNat hwidth)
    (by rw [FloatLib.Numerics.FixedWord.roundShiftRightEven_toNat, hproduct, hshift])

/--
A successful native normal-product round agrees with the exact finite-product rounder.

Its hypotheses are the machine-capacity and normalized-input bounds that the `UInt64`
implementation needs, and nothing more.
-/
theorem roundNormalProduct_refines
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 31)
    (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : UInt64)
    (hxExponent :
      0 < xExponent.toNat ∧ xExponent.toNat < 2 ^ fmt.expWidth)
    (hyExponent :
      0 < yExponent.toNat ∧ yExponent.toNat < 2 ^ fmt.expWidth)
    (hxMantissa :
      2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧
        xMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hyMantissa :
      2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧
        yMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (result : Model fmt)
    (hresult :
      roundNormalProduct? fmt sign
          xExponent yExponent xMantissa yMantissa =
        some result) :
    result =
      FiniteProductRound.round fmt sign
        (xMantissa.toNat * yMantissa.toNat)
        ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
  rw [roundNormalProduct_eq_spec fmt hwidth hexpWidth hfracWidth
    sign xExponent yExponent xMantissa yMantissa
    hxExponent hyExponent hxMantissa hyMantissa] at hresult
  exact FiniteProductRound.normalSpec_refines_of_normalized
    fmt sign xExponent.toNat yExponent.toNat
      xMantissa.toNat yMantissa.toNat
      hxMantissa.1 hyMantissa.1 result hresult

/-- The flat sentinel-tagged word result decodes to the optional result `mulNormal?`. -/
theorem mulNormalWord_decode {fmt : FloatFormat}
    (heligible : Eligible fmt) (x y : Model fmt) :
    (if mulNormalWord x y == declineWord then
        none
      else
        some (NativeSmallWord.ofWord (mulNormalWord x y))) =
      mulNormal? x y := by
  rcases heligible with ⟨hieee, hwidth, hexpWidth, hfracWidth⟩
  have hstorage : fmt.bitWidth ≤ 63 := by
    unfold FloatFormat.bitWidth
    omega
  let xBits := NativeSmallWord.toWord x
  let yBits := NativeSmallWord.toWord y
  let xExponent := NativeSmallWord.exponentField fmt xBits
  let yExponent := NativeSmallWord.exponentField fmt yBits
  let allOnes := NativeSmallWord.exponentMask fmt
  let xMantissa :=
    NativeSmallWord.fractionField fmt xBits ||| hiddenBit fmt
  let yMantissa :=
    NativeSmallWord.fractionField fmt yBits ||| hiddenBit fmt
  let sign :=
    Bool.xor
      (NativeSmallWord.signField fmt xBits)
      (NativeSmallWord.signField fmt yBits)
  by_cases hinvalid :
      (xExponent == 0 || xExponent == allOnes ||
        yExponent == 0 || yExponent == allOnes) = true
  · simp [mulNormalWord, mulNormal?, NativeSmallWord.withNormalPair?,
      NativeSmallWord.withNormalPairWord?,
      xBits, yBits, xExponent,
      yExponent, allOnes, hinvalid]
  · simpa [mulNormalWord, mulNormal?, NativeSmallWord.withNormalPair?,
      NativeSmallWord.withNormalPairWord?,
      xBits, yBits, xExponent,
      yExponent, allOnes, xMantissa, yMantissa, sign, hinvalid] using
      roundNormalProductWord_decode fmt hstorage sign
        xExponent yExponent xMantissa yMantissa

/--
A successful one-word normal multiplication agrees with the compact finite kernel.

The native path handles only normal IEEE operands whose intermediate fields fit in one word.
Every other input returns `none`, and callers fall back to the exact kernel.
-/
theorem mulNormal_refines {fmt : FloatFormat}
    (heligible : Eligible fmt) (x y result : Model fmt)
    (hresult : mulNormal? x y = some result) :
    FiniteKernel.mul? x y = some result := by
  rcases heligible with ⟨hieee, hwidth, hexpWidth, hfracWidth⟩
  refine NativeNormalPair.mul_refines
    hieee hwidth (roundNormalProduct? fmt) ?_ x y result ?_
  · intro sign xExponent yExponent xMantissa yMantissa candidate
      hxExponent hyExponent hxMantissa hyMantissa hround
    exact roundNormalProduct_refines fmt hwidth hexpWidth hfracWidth
      sign xExponent yExponent xMantissa yMantissa
      hxExponent hyExponent hxMantissa hyMantissa candidate hround
  · simpa [mulNormal?] using hresult

end Model.NativeSmallWordMul
end FloatLib.Floats.Formats.BinaryInterchange
