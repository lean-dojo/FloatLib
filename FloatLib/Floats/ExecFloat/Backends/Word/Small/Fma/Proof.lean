/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Fma.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
import FloatLib.Floats.ExecFloat.Backends.Word.Small.Add.Proof
import FloatLib.Floats.ExecFloat.Backends.Word.Small.Core.Proof
import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
import FloatLib.Floats.ExecFloat.Backends.Generic.ScaleAdd.Proof
import Mathlib.Tactic.NormNum

/-!
# Correctness of native one-word finite fused multiply-add

Under `Eligible`, every accepted result of `Fma.Runtime` agrees with the exact finite kernel.
`fmaFields_refines` matches the four alignment branches of `fmaFields?` with
`FiniteScaleAdd.roundSum` at round offset `0`, reusing the one-word addition lemmas for the rounder,
the aligned combination, and the sticky alignment. `fmaFinite_refines` then identifies the decoded
fields with the IEEE branch of `FiniteKernel.Internal.fmaComponents`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordFma

open NativeSmallWord NativeSmallWordAdd

/-- The product shift limit is exact when `fracWidth ≤ 29`. -/
theorem productShiftLimit_toNat (fmt : FloatFormat) (hfracWidth : fmt.fracWidth ≤ 29) :
    (productShiftLimit fmt).toNat = 61 - 2 * fmt.fracWidth := by
  have hfrac : (UInt64.ofNat fmt.fracWidth).toNat = fmt.fracWidth := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    omega
  have htwice : (2 * UInt64.ofNat fmt.fracWidth).toNat = 2 * fmt.fracWidth := by
    rw [UInt64.toNat_mul, hfrac, Nat.mod_eq_of_lt] <;> simp only [UInt64.reduceToNat]
    omega
  unfold productShiftLimit
  rw [UInt64.toNat_sub_of_le, htwice]
  · rfl
  · apply UInt64.le_iff_toNat_le.mpr
    rw [htwice]
    change 2 * fmt.fracWidth ≤ 61
    omega

private theorem toNat_ne_zero_of_ne_zero {value : UInt64} (h : value ≠ 0) :
    value.toNat ≠ 0 := by
  simpa [← UInt64.toNat_inj] using h

/-- A left shift that keeps a `width`-bit word below `2 ^ 63` is exact. -/
private theorem shifted_toNat (value shift : UInt64) (width : Nat)
    (hvalue : value.toNat < 2 ^ width) (hshift : shift.toNat + width ≤ 63) :
    (value <<< shift).toNat = value.toNat <<< shift.toNat ∧
      value.toNat <<< shift.toNat < 2 ^ 63 := by
  have hfit : value.toNat <<< shift.toNat < 2 ^ 63 := by
    have hshifted := Nat.shiftLeft_lt (m := shift.toNat) hvalue
    exact hshifted.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨?_, hfit⟩
  have hshiftNat :=
    FloatLib.Numerics.FixedWord.shiftLeft_toNat value shift.toNat (by omega)
      (hfit.trans (by norm_num))
  rwa [UInt64.ofNat_toNat] at hshiftNat

private theorem shifted_ne_zero (value shift : UInt64) (hvalue : value.toNat ≠ 0)
    (hshifted : (value <<< shift).toNat = value.toNat <<< shift.toNat) :
    value <<< shift ≠ 0 := by
  intro h
  have hnat := congrArg UInt64.toNat h
  rw [hshifted, UInt64.toNat_zero, Nat.shiftLeft_eq] at hnat
  exact absurd hnat (Nat.mul_ne_zero hvalue (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)))

/--
An accepted field FMA is the exact kernel's rounded sum of the product and the addend.

The product has at most `2 * fracWidth + 2` bits, the addend at most `fracWidth + 1`, and both
scales are below `2 ^ 33`. The machine-word transfer needs nothing else.
-/
theorem fmaFields_refines
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 29)
    (productSign : Bool) (product productScale : UInt64)
    (addendSign : Bool) (addend addendScale : UInt64)
    (hproduct : product.toNat < 2 ^ (2 * fmt.fracWidth + 2))
    (haddend : addend.toNat < 2 ^ (fmt.fracWidth + 1))
    (hproductScale : productScale.toNat < 2 ^ 33)
    (haddendScale : addendScale.toNat < 2 ^ 33)
    (result : Model fmt)
    (hresult :
      fmaFields? fmt productSign product productScale addendSign addend addendScale =
        some result) :
    result =
      FiniteScaleAdd.roundSum fmt 0 productSign addendSign
        product.toNat productScale.toNat addend.toNat addendScale.toNat := by
  have hfrac61 : fmt.fracWidth ≤ 61 := by omega
  have hproduct60 : product.toNat < 2 ^ 60 :=
    hproduct.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hlimit := shiftLimit_toNat fmt hfrac61
  have hproductLimit := productShiftLimit_toNat fmt hfracWidth
  unfold fmaFields? at hresult
  unfold FiniteScaleAdd.roundSum
  by_cases hp : product = 0
  · simp [hp] at hresult
  have hpNat := toNat_ne_zero_of_ne_zero hp
  rw [ite_eq_right (by simpa using hp)] at hresult
  rw [ite_eq_right (by simpa using hpNat)]
  by_cases ha : addend = 0
  · subst ha
    simp only [beq_self_eq_true, ite_true] at hresult
    simp only [UInt64.toNat_zero, beq_self_eq_true, ite_true]
    have h := roundMagnitude_refines fmt hwidth hexpWidth hfrac61 0 productSign product
      productScale hp (by simp only [UInt64.toNat_zero]; omega) result hresult
    rwa [UInt64.toNat_zero] at h
  have haNat := toNat_ne_zero_of_ne_zero ha
  rw [ite_eq_right (by simpa using ha)] at hresult
  rw [ite_eq_right (by simpa using haNat)]
  by_cases hle : productScale ≤ addendScale
  · have hleNat : productScale.toNat ≤ addendScale.toNat := UInt64.le_iff_toNat_le.mp hle
    have hshiftNat : (addendScale - productScale).toNat =
        addendScale.toNat - productScale.toNat :=
      UInt64.toNat_sub_of_le _ _ hle
    rw [ite_eq_left hle] at hresult
    rw [ite_eq_left hleNat, FiniteScaleAdd.roundAligned_eq]
    by_cases hshift : addendScale - productScale ≤ shiftLimit fmt
    · rw [ite_eq_left hshift] at hresult
      have hshiftBound : (addendScale - productScale).toNat + (fmt.fracWidth + 1) ≤ 63 := by
        have hnat := UInt64.le_iff_toNat_le.mp hshift
        rw [hlimit] at hnat
        omega
      obtain ⟨hshifted, hshiftedLt⟩ :=
        shifted_toNat addend (addendScale - productScale) _ haddend hshiftBound
      have hsum : product.toNat + (addend <<< (addendScale - productScale)).toNat < 2 ^ 64 := by
        rw [hshifted]
        norm_num at hproduct60 hshiftedLt ⊢
        omega
      have h := roundAligned_refines fmt hwidth hexpWidth hfrac61 0 productSign addendSign
        product (addend <<< (addendScale - productScale)) productScale hp
        (shifted_ne_zero _ _ haNat hshifted) hsum
        (by simp only [UInt64.toNat_zero]; omega) result hresult
      rw [UInt64.toNat_zero, hshifted, hshiftNat] at h
      rw [FiniteScaleAdd.roundMagnitudes_comm]
      exact h
    · rw [ite_eq_right hshift] at hresult
      have hgt := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hshift)
      rw [hlimit] at hgt
      have hlow : product.toNat ≤ 2 ^ (fmt.fracWidth + (addendScale - productScale).toNat - 1) :=
        hproduct.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
      have h := roundJammed_refines fmt hwidth hexpWidth hfrac61 0 addendSign productSign
        addend product (addendScale - productScale) productScale hlow hp
        (by rw [hshiftNat, UInt64.toNat_zero]; omega) result hresult
      rwa [UInt64.toNat_zero, hshiftNat] at h
  · have hleNat : ¬productScale.toNat ≤ addendScale.toNat :=
      fun h => hle (UInt64.le_iff_toNat_le.mpr h)
    have hge : addendScale ≤ productScale := by
      apply UInt64.le_iff_toNat_le.mpr
      omega
    have hshiftNat : (productScale - addendScale).toNat =
        productScale.toNat - addendScale.toNat :=
      UInt64.toNat_sub_of_le _ _ hge
    rw [ite_eq_right hle] at hresult
    rw [ite_eq_right hleNat, FiniteScaleAdd.roundAligned_eq]
    by_cases hshift : productScale - addendScale ≤ productShiftLimit fmt
    · rw [ite_eq_left hshift] at hresult
      have hshiftBound :
          (productScale - addendScale).toNat + (2 * fmt.fracWidth + 2) ≤ 63 := by
        have hnat := UInt64.le_iff_toNat_le.mp hshift
        rw [hproductLimit] at hnat
        omega
      obtain ⟨hshifted, hshiftedLt⟩ :=
        shifted_toNat product (productScale - addendScale) _ hproduct hshiftBound
      have haddend63 : addend.toNat < 2 ^ 63 :=
        haddend.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      have hsum : (product <<< (productScale - addendScale)).toNat + addend.toNat < 2 ^ 64 := by
        rw [hshifted]
        norm_num at haddend63 hshiftedLt ⊢
        omega
      have h := roundAligned_refines fmt hwidth hexpWidth hfrac61 0 productSign addendSign
        (product <<< (productScale - addendScale)) addend addendScale
        (shifted_ne_zero _ _ hpNat hshifted) ha hsum
        (by simp only [UInt64.toNat_zero]; omega) result hresult
      rwa [UInt64.toNat_zero, hshifted, hshiftNat] at h
    · rw [ite_eq_right hshift] at hresult
      have hgt := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hshift)
      rw [hproductLimit] at hgt
      have hlow : addend.toNat ≤ 2 ^ (fmt.fracWidth + (productScale - addendScale).toNat - 1) :=
        haddend.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
      have h := roundJammed_refines fmt hwidth hexpWidth hfrac61 0 productSign addendSign
        product addend (productScale - addendScale) addendScale hlow ha
        (by rw [hshiftNat, UInt64.toNat_zero]; omega) result hresult
      rwa [UInt64.toNat_zero, hshiftNat] at h

private theorem finiteScale_toNat_lt (fmt : FloatFormat) (hexpWidth : fmt.expWidth ≤ 30)
    (exponent : UInt64) (hexponent : exponent.toNat < 2 ^ fmt.expWidth) :
    FiniteKernel.scale exponent.toNat < 2 ^ 30 := by
  have hpow : 2 ^ fmt.expWidth ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hexpWidth
  unfold FiniteKernel.scale
  split <;> omega

/--
An accepted one-word FMA is the exact compact finite kernel's answer.

Declines fall outside the statement, and the dispatcher handles them with the native-storage
component kernel or the exact implementation. Only the capacity contract `Eligible` is assumed of
the format.
-/
theorem fmaFinite_refines {fmt : FloatFormat}
    (heligible : Eligible fmt)
    (x y z result : Model fmt)
    (hresult : fmaFinite? x y z = some result) :
    FiniteKernel.fma? x y z = some result := by
  rcases heligible with ⟨hieee, hwidth, hexpWidth, hfracWidth⟩
  unfold fmaFinite? at hresult
  by_cases hexceptional :
      (exponentField fmt (toWord x) == exponentMask fmt ||
        exponentField fmt (toWord y) == exponentMask fmt ||
        exponentField fmt (toWord z) == exponentMask fmt) = true
  · simp [hexceptional] at hresult
  rw [ite_eq_right hexceptional] at hresult
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hexceptional
  obtain ⟨⟨hxFinite, hyFinite⟩, hzFinite⟩ := hexceptional
  have hxMantissa := finiteMantissa_toNat_lt hwidth x
  have hyMantissa := finiteMantissa_toNat_lt hwidth y
  have hzMantissa := finiteMantissa_toNat_lt hwidth z
  have hxScale := finiteScale_toNat_lt fmt hexpWidth _ (exponentField_toNat_lt hwidth x)
  have hyScale := finiteScale_toNat_lt fmt hexpWidth _ (exponentField_toNat_lt hwidth y)
  have hzScale := finiteScale_toNat_lt fmt hexpWidth _ (exponentField_toNat_lt hwidth z)
  have hbias : fmt.exponentBias < 2 ^ 30 :=
    (FloatFormat.exponentBias_lt_two_pow fmt).trans_le
      (Nat.pow_le_pow_right (by decide) hexpWidth)
  have hoffset := alignOffset_toNat fmt hexpWidth (by omega)
  set xMantissa := NativeSmallWordFinite.finiteMantissa fmt (exponentField fmt (toWord x))
    (fractionField fmt (toWord x))
  set yMantissa := NativeSmallWordFinite.finiteMantissa fmt (exponentField fmt (toWord y))
    (fractionField fmt (toWord y))
  have hproductLt : xMantissa.toNat * yMantissa.toNat < 2 ^ (2 * fmt.fracWidth + 2) := by
    rw [show 2 * fmt.fracWidth + 2 = (fmt.fracWidth + 1) + (fmt.fracWidth + 1) by omega,
      Nat.pow_add]
    exact Nat.mul_lt_mul'' hxMantissa hyMantissa
  have hproduct : (xMantissa * yMantissa).toNat = xMantissa.toNat * yMantissa.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt]
    exact hproductLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hproductScale :
      (FloatLib.Numerics.FixedWord.finiteScale (exponentField fmt (toWord x)) +
          FloatLib.Numerics.FixedWord.finiteScale (exponentField fmt (toWord y))).toNat =
        FiniteKernel.scale (exponentField fmt (toWord x)).toNat +
          FiniteKernel.scale (exponentField fmt (toWord y)).toNat := by
    rw [UInt64.toNat_add, finiteScale_toNat_eq_scale, finiteScale_toNat_eq_scale,
      Nat.mod_eq_of_lt (by norm_num at hxScale hyScale ⊢; omega)]
  have haddendScale :
      (FloatLib.Numerics.FixedWord.finiteScale (exponentField fmt (toWord z)) +
          alignOffset fmt).toNat =
        FiniteKernel.scale (exponentField fmt (toWord z)).toNat +
          FiniteKernel.finiteScaleOffset fmt := by
    rw [UInt64.toNat_add, finiteScale_toNat_eq_scale, hoffset, Nat.mod_eq_of_lt]
    · rfl
    · norm_num at hzScale hbias ⊢
      omega
  have h := fmaFields_refines fmt hwidth hexpWidth hfracWidth _ _ _ _ _ _
    (by rw [hproduct]; exact hproductLt) hzMantissa
    (by rw [hproductScale]; norm_num at hxScale hyScale ⊢; omega)
    (by rw [haddendScale]; unfold FiniteKernel.finiteScaleOffset
        norm_num at hzScale hbias ⊢; omega)
    result hresult
  rw [hproduct, hproductScale, haddendScale] at h
  unfold FiniteKernel.fma?
  rw [decode_of_finite hieee hwidth x hxFinite, decode_of_finite hieee hwidth y hyFinite,
    decode_of_finite hieee hwidth z hzFinite]
  simp only
  rw [← FiniteKernel.Internal.fmaComponents_eq]
  unfold FiniteKernel.Internal.fmaComponents
  rw [ite_eq_left hieee, h]

end Model.NativeSmallWordFma
end FloatLib.Floats.Formats.BinaryInterchange
