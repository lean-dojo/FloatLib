/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.TwoWordMul.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
public import FloatLib.Kernels.FixedWord.LimbRound.Proof
public import FloatLib.Kernels.FixedWord.Core.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.ExecFloat.Backends.Word.NormalPair.Proof
import FloatLib.Floats.ExecFloat.Backends.Word.ProductRound.Proof
import Mathlib.Tactic.Positivity.Finset

/-!
# Correctness of native two-word finite multiplication

Every accepted result of the `64 x 64 -> 128` normal-product tier in `TwoWordMul.Runtime` is the
exact format-generic product rounding. The proof separates the two-word product and its leading-bit
bounds from the shared one-word carry and packing stage. The dispatcher handles declined inputs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeTwoWordMul

open NativeSmallWord

/-- Binary64 satisfies the two-word capacity contract. -/
theorem binary64_eligible : Eligible FloatFormat.binary64 := by
  decide

private theorem productLeading_toNat
    (fmt : FloatFormat)
    (hfracLower : 32 ≤ fmt.fracWidth)
    (hfracUpper : fmt.fracWidth ≤ 62)
    (xMantissa yMantissa : UInt64)
    (hxMantissa :
      2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧
        xMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hyMantissa :
      2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧
        yMantissa.toNat < 2 ^ (fmt.fracWidth + 1)) :
    (productLeading fmt (FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa)).toNat =
      (xMantissa.toNat * yMantissa.toNat).log2 := by
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let productNat := xMantissa.toNat * yMantissa.toNat
  let lower := 2 * fmt.fracWidth
  let thresholdShift := 2 * fmt.fracWidth + 1 - 64
  let threshold := (1 : UInt64) <<< UInt64.ofNat thresholdShift
  have hproduct :
      product.toNat = productNat := by
    simp [product, productNat]
  obtain ⟨hproductLower, hproductUpper⟩ :
      2 ^ lower ≤ productNat ∧ productNat < 2 ^ (lower + 2) :=
    FiniteProductRound.normalizedProduct_bounds fmt hxMantissa hyMantissa
  have hproductNe : productNat ≠ 0 := Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hproductLower)
  have hlowerRange : 64 ≤ lower ∧ lower + 1 < 128 := by
    unfold lower
    omega
  have hshiftRange : 0 < thresholdShift ∧ thresholdShift < 64 := by
    unfold thresholdShift
    omega
  have hthreshold :
      threshold.toNat = 2 ^ thresholdShift := by
    unfold threshold
    rw [FloatLib.Numerics.FixedWord.shiftLeft_toNat]
    · simp [Nat.shiftLeft_eq]
    · simp [Nat.shiftLeft_eq]
      exact Nat.pow_lt_pow_right (by decide) hshiftRange.2
  have hbelow :
      product.hi < threshold ↔ productNat < 2 ^ (lower + 1) := by
    rw [UInt64.lt_iff_toNat_lt, hthreshold]
    rw [← hproduct]
    unfold FloatLib.Numerics.FixedWord.UInt128.toNat
    have hlo := product.lo.toNat_lt
    have hpow :
        2 ^ (lower + 1) = 2 ^ thresholdShift * 2 ^ 64 := by
      rw [← pow_add]
      apply congrArg (fun exponent : Nat => 2 ^ exponent)
      have hle : 64 ≤ 2 * fmt.fracWidth + 1 := by omega
      unfold thresholdShift lower
      omega
    rw [hpow]
    constructor
    · intro hhi
      calc
        product.lo.toNat + product.hi.toNat * 2 ^ 64 <
            2 ^ 64 + product.hi.toNat * 2 ^ 64 :=
          Nat.add_lt_add_right product.lo.toNat_lt _
        _ = (product.hi.toNat + 1) * 2 ^ 64 := by ring
        _ ≤ 2 ^ thresholdShift * 2 ^ 64 :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hhi)
    · intro htotal
      by_contra hhi
      have hhi' : 2 ^ thresholdShift ≤ product.hi.toNat :=
        Nat.le_of_not_gt hhi
      have hmul :
          2 ^ thresholdShift * 2 ^ 64 ≤
            product.hi.toNat * 2 ^ 64 :=
        Nat.mul_le_mul_right _ hhi'
      have htail :
          product.hi.toNat * 2 ^ 64 ≤
            product.lo.toNat + product.hi.toNat * 2 ^ 64 :=
        Nat.le_add_left _ _
      exact (Nat.not_lt_of_ge (hmul.trans htail)) htotal
  have hlowerWord :
      (UInt64.ofNat lower).toNat = lower := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    omega
  have hlowerSucc :
      (UInt64.ofNat lower + 1).toNat = lower + 1 := by
    rw [UInt64.toNat_add, hlowerWord]
    apply Nat.mod_eq_of_lt
    have hsmall : lower + 1 ≤ 125 := by
      unfold lower
      omega
    exact hsmall.trans_lt (by norm_num)
  by_cases hhigh : productNat < 2 ^ (lower + 1)
  · have hlog :
        productNat.log2 = lower :=
      (Nat.log2_eq_iff hproductNe).2 ⟨hproductLower, hhigh⟩
    have hnative : product.hi < threshold := hbelow.mpr hhigh
    unfold productLeading
    change
      (if product.hi < threshold then UInt64.ofNat lower
        else UInt64.ofNat lower + 1).toNat =
        productNat.log2
    rw [ite_eq_left hnative, hlowerWord, hlog]
  · have hge : 2 ^ (lower + 1) ≤ productNat :=
      Nat.le_of_not_gt hhigh
    have hlog :
        productNat.log2 = lower + 1 :=
      (Nat.log2_eq_iff hproductNe).2 ⟨hge, hproductUpper⟩
    have hnative : ¬product.hi < threshold := by
      intro h
      exact hhigh (hbelow.mp h)
    unfold productLeading
    change
      (if product.hi < threshold then UInt64.ofNat lower
        else UInt64.ofNat lower + 1).toNat =
        productNat.log2
    rw [ite_eq_right hnative, hlowerSucc, hlog]

private theorem roundNormalProduct_eq_spec
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 31)
    (hfracLower : 32 ≤ fmt.fracWidth)
    (hfracUpper : fmt.fracWidth ≤ 62)
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
      FiniteProductRound.normalSpec? fmt sign
        xExponent.toNat yExponent.toNat xMantissa.toNat yMantissa.toNat := by
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let productNat := xMantissa.toNat * yMantissa.toNat
  let leading := productLeading fmt product
  have hproduct : product.toNat = productNat := by
    simp [product, productNat]
  obtain ⟨hproductLower, hproductUpper⟩ :
      2 ^ (2 * fmt.fracWidth) ≤ productNat ∧ productNat < 2 ^ (2 * fmt.fracWidth + 2) :=
    FiniteProductRound.normalizedProduct_bounds fmt hxMantissa hyMantissa
  have hproductNe : productNat ≠ 0 := Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hproductLower)
  have hleading :
      leading.toNat = productNat.log2 := by
    unfold leading product
    exact productLeading_toNat fmt hfracLower hfracUpper
      xMantissa yMantissa hxMantissa hyMantissa
  have hleadingLower :
      2 * fmt.fracWidth ≤ leading.toNat := by
    rw [hleading]
    exact (Nat.le_log2 hproductNe).2 hproductLower
  have hleadingUpper :
      leading.toNat < 2 * fmt.fracWidth + 2 := by
    rw [hleading]
    exact (Nat.log2_lt hproductNe).2 hproductUpper
  have hbias :
      fmt.bias < 2 ^ 31 :=
    (FloatFormat.bias_lt_pow_expWidth fmt).trans_le (Nat.pow_le_pow_right (by decide) hexpWidth)
  have hnormalThreshold :
      (UInt64.ofNat
          (fmt.bias + 2 * fmt.fracWidth - 1)).toNat =
        fmt.bias + 2 * fmt.fracWidth - 1 := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    norm_num at hbias ⊢
    omega
  -- The two-word product is rounded to a one-word significand.
  have hfracWord :
      (UInt64.ofNat fmt.fracWidth).toNat = fmt.fracWidth := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    omega
  have hleadingWord :
      UInt64.ofNat fmt.fracWidth ≤ leading := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hfracWord]
    omega
  have hshift :
      (leading - UInt64.ofNat fmt.fracWidth).toNat =
        productNat.log2 - fmt.fracWidth := by
    rw [UInt64.toNat_sub_of_le _ _ hleadingWord, hleading, hfracWord]
  have hshiftLower :
      fmt.fracWidth ≤
        (leading - UInt64.ofNat fmt.fracWidth).toNat := by
    rw [hshift, ← hleading]
    omega
  have hshiftUpper :
      (leading - UInt64.ofNat fmt.fracWidth).toNat ≤
        fmt.fracWidth + 1 := by
    rw [hshift, ← hleading]
    omega
  have hshiftLt :
      (leading - UInt64.ofNat fmt.fracWidth).toNat < 64 := by
    omega
  have hlogUpper :
      productNat < 2 ^ (productNat.log2 + 1) :=
    ((Nat.log2_eq_iff hproductNe).mp rfl).2
  have hquotientBase :
      productNat /
          2 ^ (leading - UInt64.ofNat fmt.fracWidth).toNat <
        2 ^ (fmt.fracWidth + 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [← pow_add]
    have hexponent :
        fmt.fracWidth + 1 +
            (leading - UInt64.ofNat fmt.fracWidth).toNat =
          productNat.log2 + 1 := by
      rw [hshift]
      omega
    rwa [hexponent]
  have hquotient :
      (product.toNat >>>
          (leading - UInt64.ofNat fmt.fracWidth).toNat) + 1 <
        2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow, hproduct]
    have hpow :
        2 ^ (fmt.fracWidth + 1) < 2 ^ 64 :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have hrounded :
      (product.roundShiftRightEven (leading - UInt64.ofNat fmt.fracWidth).toNat).toNat =
        Numerics.roundShiftRightEven productNat (productNat.log2 - fmt.fracWidth) := by
    rw [FloatLib.Numerics.FixedWord.UInt128.roundShiftRightEven_toNat product
      (leading - UInt64.ofNat fmt.fracWidth).toNat
      hshiftLt hquotient]
    rw [hproduct, hshift]
  unfold roundNormalProduct? roundNormalProductWord?
  dsimp only
  rw [apply_ite (Option.map ofWord), Option.map_none]
  exact NativeWordProduct.normal_eq_normalSpec fmt hwidth hexpWidth hfracUpper sign
    xExponent yExponent xMantissa yMantissa hxExponent hyExponent hxMantissa hyMantissa
    leading _ _ hleading hnormalThreshold hrounded

/--
A successful two-word normal-product round agrees with the exact finite-product rounder.
-/
theorem roundNormalProduct_refines
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hfracLower : 32 ≤ fmt.fracWidth)
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
  have hexp := fmt.expWidth_ge_two
  have hexpWidth : fmt.expWidth ≤ 31 := by
    unfold FloatFormat.bitWidth at hwidth
    omega
  have hfracUpper : fmt.fracWidth ≤ 62 := by
    unfold FloatFormat.bitWidth at hwidth
    omega
  rw [roundNormalProduct_eq_spec fmt hwidth hexpWidth
    hfracLower hfracUpper sign xExponent yExponent xMantissa yMantissa
    hxExponent hyExponent hxMantissa hyMantissa] at hresult
  exact FiniteProductRound.normalSpec_refines_of_normalized
    fmt sign xExponent.toNat yExponent.toNat
      xMantissa.toNat yMantissa.toNat
      hxMantissa.1 hyMantissa.1 result hresult

/--
A successful two-word normal multiplication agrees with the compact finite kernel.

The native tier handles normal operands of one-storage-word IEEE formats with fraction widths 32
through 62. Zero, subnormal and exceptional operands and boundary results return `none` and take
the generic path.
-/
theorem mulNormal_refines {fmt : FloatFormat}
    (heligible : Eligible fmt) (x y result : Model fmt)
    (hresult : mulNormal? x y = some result) :
    FiniteKernel.mul? x y = some result := by
  rcases heligible with ⟨hieee, hwidth, hfracLower, -⟩
  refine NativeNormalPair.mul_refines
    hieee hwidth (roundNormalProduct? fmt) ?_ x y result ?_
  · intro sign xExponent yExponent xMantissa yMantissa candidate
      hxExponent hyExponent hxMantissa hyMantissa hround
    exact roundNormalProduct_refines fmt hwidth hfracLower sign
      xExponent yExponent xMantissa yMantissa
      hxExponent hyExponent hxMantissa hyMantissa candidate hround
  · have hpair :
        mulNormal? x y = NativeSmallWord.withNormalPair? x y (roundNormalProduct? fmt) := by
      simp only [mulNormal?, mulNormalWord?, NativeSmallWord.withNormalPair?,
        NativeSmallWord.withNormalPairWord?]
      split_ifs <;> rfl
    rwa [hpair] at hresult

/-! ## Storage-word entry points -/

/-- On storage words below the radix, `mulNormal?` is the `ofWord` image of `mulNormalWord?`. -/
theorem mulNormal?_ofWord {fmt : FloatFormat} {xBits yBits : UInt64}
    (hx : xBits.toNat < 2 ^ fmt.bitWidth) (hy : yBits.toNat < 2 ^ fmt.bitWidth) :
    mulNormal? (ofWord (fmt := fmt) xBits) (ofWord yBits) =
      (mulNormalWord? fmt xBits yBits).map ofWord := by
  rw [mulNormal?, toWord_ofWord_of_lt hx, toWord_ofWord_of_lt hy]

end Model.NativeTwoWordMul
end FloatLib.Floats.Formats.BinaryInterchange
