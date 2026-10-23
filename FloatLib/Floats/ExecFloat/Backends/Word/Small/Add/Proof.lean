/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Add.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.ScaleAdd.Runtime
public import FloatLib.Numerics.ShiftRightJam
import FloatLib.Floats.ExecFloat.Backends.Word.Small.Core.Proof
import FloatLib.Floats.ExecFloat.Backends.Word.Small.Finite.Proof
import FloatLib.Floats.ExecFloat.Backends.Word.ProductRound.Proof
import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
import FloatLib.Floats.ExecFloat.Backends.Generic.ScaleAdd.Proof
import FloatLib.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
import FloatLib.Numerics.ShiftRightJam.Proof
import FloatLib.Floats.Formats.BinaryInterchange.ModelRounding.Proof
import Mathlib.Tactic.NormNum

/-!
# Correctness of native one-word finite addition

Under `Eligible`, every accepted result of `Add.Runtime` agrees with the exact finite kernel.
`addFinite_refines` also covers subtraction by identifying the toggled right sign with `neg y`.
A declined input is handled by the dispatcher's generic fallback.

`normalSpec?` describes the normal branch of `FiniteProductRound.round`. The proof transfers
native rounding to this specification using the shared carry and packing theorem
`NativeWordProduct.finish_eq`, then treats signed magnitudes, exponent alignment, and decoding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordAdd

open NativeSmallWord

/-! ## Natural-number specification of the normal rounding path -/

/--
The normal branch of `FiniteProductRound.round`, declining instead of producing a subnormal or an
infinite result.

For a nonzero magnitude, this rounds the value with sign `sign` and magnitude
`magnitude * 2 ^ (scale - 2 * ieeeSubnormalAlignExp fmt)`, interpreting subtraction in `Int`.
`normalSpec_refines` identifies each accepted answer with the total product rounder.
-/
def normalSpec? (fmt : FloatFormat) (sign : Bool) (magnitude scale : Nat) :
    Option (Model fmt) :=
  let leading := magnitude.log2
  let position := leading + scale
  let normalThreshold := fmt.bias + 2 * fmt.fracWidth - 1
  if position < normalThreshold then
    none
  else
    let rounded :=
      if fmt.fracWidth ≤ leading then
        Numerics.roundShiftRightEven magnitude (leading - fmt.fracWidth)
      else
        magnitude <<< (fmt.fracWidth - leading)
    let carry := rounded = pow2 (fmt.fracWidth + 1)
    let normalizedPosition := if carry then position + 1 else position
    let overflowThreshold := 3 * fmt.bias + 2 * fmt.fracWidth - 2
    if overflowThreshold < normalizedPosition then
      none
    else
      let normalizedMantissa := if carry then pow2 fmt.fracWidth else rounded
      let exponentOffset := fmt.bias + 2 * fmt.fracWidth - 2
      some <| ofFields fmt sign
        (normalizedPosition - exponentOffset)
        (normalizedMantissa - pow2 fmt.fracWidth)

/-- A `some` answer of the normal specification is the arbitrary-precision rounder's result. -/
theorem normalSpec_refines
    (fmt : FloatFormat) (sign : Bool) (magnitude scale : Nat)
    (hmagnitude : magnitude ≠ 0)
    (result : Model fmt)
    (hresult : normalSpec? fmt sign magnitude scale = some result) :
    result = FiniteProductRound.round fmt sign magnitude scale := by
  unfold normalSpec? at hresult
  let leading := magnitude.log2
  let position := leading + scale
  let normalThreshold := fmt.bias + 2 * fmt.fracWidth - 1
  by_cases hsubnormal : position < normalThreshold
  · simp [leading, position, normalThreshold, hsubnormal] at hresult
  let rounded :=
    if fmt.fracWidth ≤ leading then
      Numerics.roundShiftRightEven magnitude (leading - fmt.fracWidth)
    else
      magnitude <<< (fmt.fracWidth - leading)
  let carry := rounded = pow2 (fmt.fracWidth + 1)
  let normalizedPosition := if carry then position + 1 else position
  let overflowThreshold := 3 * fmt.bias + 2 * fmt.fracWidth - 2
  by_cases hoverflow : overflowThreshold < normalizedPosition
  · simp [leading, position, normalThreshold, hsubnormal, rounded, carry,
      normalizedPosition, overflowThreshold, hoverflow] at hresult
  have hresultEq :
      ofFields fmt sign
          (normalizedPosition - (fmt.bias + 2 * fmt.fracWidth - 2))
          ((if carry then pow2 fmt.fracWidth else rounded) - pow2 fmt.fracWidth) =
        result := by
    simpa [leading, position, normalThreshold, hsubnormal, rounded, carry,
      normalizedPosition, overflowThreshold, hoverflow] using hresult
  rw [← hresultEq]
  unfold FiniteProductRound.round
  simp only [beq_iff_eq, hmagnitude, ite_false]
  rw [ite_eq_right hsubnormal, ite_eq_right hoverflow]

/-! ## Machine-word rounding -/

private theorem bias_lt (fmt : FloatFormat) (hexpWidth : fmt.expWidth ≤ 30) :
    fmt.bias < 2 ^ 30 :=
  (FloatFormat.bias_lt_pow_expWidth fmt).trans_le
    (Nat.pow_le_pow_right (by decide) hexpWidth)

private theorem exponentBias_lt (fmt : FloatFormat) (hexpWidth : fmt.expWidth ≤ 30) :
    fmt.exponentBias < 2 ^ 30 :=
  (FloatFormat.exponentBias_lt_two_pow fmt).trans_le
    (Nat.pow_le_pow_right (by decide) hexpWidth)

/-- The alignment offset is exact when `expWidth ≤ 30` and `fracWidth ≤ 61`. -/
theorem alignOffset_toNat (fmt : FloatFormat)
    (hexpWidth : fmt.expWidth ≤ 30) (hfracWidth : fmt.fracWidth ≤ 61) :
    (alignOffset fmt).toNat = fmt.exponentBias + fmt.fracWidth - 1 := by
  have hbias := exponentBias_lt fmt hexpWidth
  unfold alignOffset
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
  norm_num at hbias ⊢
  omega

/-- The alignment shift limit is exact when `fracWidth ≤ 61`. -/
theorem shiftLimit_toNat (fmt : FloatFormat) (hfracWidth : fmt.fracWidth ≤ 61) :
    (shiftLimit fmt).toNat = 62 - fmt.fracWidth := by
  have hfrac : (UInt64.ofNat fmt.fracWidth).toNat = fmt.fracWidth := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    omega
  unfold shiftLimit
  rw [UInt64.toNat_sub_of_le]
  · rw [hfrac]
    rfl
  · apply UInt64.le_iff_toNat_le.mpr
    rw [hfrac]
    change fmt.fracWidth ≤ 62
    omega

private theorem roundMantissa_lt_eq_le (magnitude width leading : UInt64) :
    (if width < leading then
        Numerics.FixedWord.roundShiftRightEven magnitude (leading - width).toNat
      else magnitude <<< (width - leading)) =
    (if width ≤ leading then
        Numerics.FixedWord.roundShiftRightEven magnitude (leading - width).toNat
      else magnitude <<< (width - leading)) := by
  by_cases hlt : width < leading
  · simp only [hlt, UInt64.le_of_lt hlt, ite_true]
  · by_cases heq : width = leading
    · subst leading
      simp [Numerics.FixedWord.roundShiftRightEven]
    · have hnotle : ¬width ≤ leading := by
        rw [UInt64.lt_iff_toNat_lt] at hlt
        rw [← UInt64.toNat_inj] at heq
        rw [UInt64.le_iff_toNat_le]
        omega
      simp only [hlt, hnotle, ite_false]

/--
The machine-word rounder computes the natural-number normal specification.

With a nonzero magnitude and a scale bounded by the exponent range, no intermediate position,
shift or increment wraps around the word.
-/
theorem roundMagnitude_eq_normalSpec
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 61)
    (offset : UInt64) (sign : Bool) (magnitude scale : UInt64)
    (hmagnitude : magnitude ≠ 0)
    (hscale : scale.toNat + offset.toNat < 2 ^ 62) :
    roundMagnitude? fmt offset sign magnitude scale =
      normalSpec? fmt sign magnitude.toNat (scale.toNat + offset.toNat) := by
  let magnitudeNat := magnitude.toNat
  have hmagnitudeNe : magnitudeNat ≠ 0 := by
    simpa [magnitudeNat, ← UInt64.toNat_inj] using hmagnitude
  have hmagnitudeFit : magnitudeNat < 2 ^ 64 := UInt64.toNat_lt_size magnitude
  have hbias := bias_lt fmt hexpWidth
  have hexponentBias := exponentBias_lt fmt hexpWidth
  let leading := magnitude.log2
  have hleading : leading.toNat = magnitudeNat.log2 :=
    FloatLib.Numerics.FixedWord.log2_toNat magnitude
  have hleadingUpper : leading.toNat < 64 := by
    rw [hleading]
    exact (Nat.log2_lt hmagnitudeNe).2 hmagnitudeFit
  let positionNat := magnitudeNat.log2 + (scale.toNat + offset.toNat)
  let position := leading + scale + offset
  have hposition : position.toNat = positionNat := by
    unfold position positionNat
    rw [UInt64.toNat_add, UInt64.toNat_add, hleading]
    have hinner : magnitudeNat.log2 + scale.toNat < 2 ^ 64 := by
      norm_num at hscale ⊢
      omega
    rw [Nat.mod_eq_of_lt hinner, Nat.mod_eq_of_lt]
    · omega
    · norm_num at hscale hexponentBias ⊢
      omega
  have hpositionAdd : (position + 1).toNat = positionNat + 1 := by
    rw [UInt64.toNat_add, hposition, UInt64.toNat_one]
    apply Nat.mod_eq_of_lt
    unfold positionNat
    have hlog : magnitudeNat.log2 < 64 := by
      rwa [← hleading]
    norm_num at hscale hexponentBias ⊢
    omega
  have hnormalThreshold :
      (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1).toNat =
        fmt.bias + 2 * fmt.fracWidth - 1 :=
    normalThreshold_toNat hwidth
  unfold roundMagnitude? normalSpec?
  simp only [FloatLib.Numerics.FixedWord.log2Word_eq_log2]
  rw [roundMantissa_lt_eq_le]
  rw [show magnitude.log2 = leading by rfl,
    show leading + scale + offset = position by rfl,
    show magnitude.toNat = magnitudeNat by rfl,
    show magnitudeNat.log2 + (scale.toNat + offset.toNat) = positionNat by rfl]
  by_cases hsubnormal : positionNat < fmt.bias + 2 * fmt.fracWidth - 1
  · have hsubnormalWord :
        position < (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1) := by
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [hposition, hnormalThreshold]
      exact hsubnormal
    rw [ite_eq_left hsubnormalWord, ite_eq_left hsubnormal]
  have hsubnormalWord :
      ¬position < (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1) := by
    intro h
    apply hsubnormal
    have hnat := UInt64.lt_iff_toNat_lt.mp h
    rwa [hposition, hnormalThreshold] at hnat
  rw [ite_eq_right hsubnormalWord, ite_eq_right hsubnormal]
  let fracWidthWord := UInt64.ofNat fmt.fracWidth
  have hfracWord : fracWidthWord.toNat = fmt.fracWidth := by
    unfold fracWidthWord
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    omega
  let rounded :=
    if fracWidthWord ≤ leading then
      FloatLib.Numerics.FixedWord.roundShiftRightEven magnitude
        (leading - fracWidthWord).toNat
    else
      magnitude <<< (fracWidthWord - leading)
  let roundedNat :=
    if fmt.fracWidth ≤ magnitudeNat.log2 then
      Numerics.roundShiftRightEven magnitudeNat (magnitudeNat.log2 - fmt.fracWidth)
    else
      magnitudeNat <<< (fmt.fracWidth - magnitudeNat.log2)
  have hrounded : rounded.toNat = roundedNat := by
    unfold rounded roundedNat
    by_cases hle : fmt.fracWidth ≤ magnitudeNat.log2
    · have hleWord : fracWidthWord ≤ leading := by
        apply UInt64.le_iff_toNat_le.mpr
        rw [hfracWord, hleading]
        exact hle
      rw [ite_eq_left hleWord, ite_eq_left hle,
        FloatLib.Numerics.FixedWord.roundShiftRightEven_toNat,
        UInt64.toNat_sub_of_le _ _ hleWord, hleading, hfracWord]
    · have hleWord : ¬fracWidthWord ≤ leading := by
        intro h
        apply hle
        have hnat := UInt64.le_iff_toNat_le.mp h
        rwa [hfracWord, hleading] at hnat
      rw [ite_eq_right hleWord, ite_eq_right hle]
      have hshiftLe : leading ≤ fracWidthWord := by
        apply UInt64.le_iff_toNat_le.mpr
        rw [hfracWord, hleading]
        omega
      have hshiftNat :
          (fracWidthWord - leading).toNat = fmt.fracWidth - magnitudeNat.log2 := by
        rw [UInt64.toNat_sub_of_le _ _ hshiftLe, hfracWord, hleading]
      have hshiftLt : fmt.fracWidth - magnitudeNat.log2 < 64 := by
        omega
      have hfit :
          magnitudeNat <<< (fmt.fracWidth - magnitudeNat.log2) < 2 ^ 64 := by
        have hshifted :=
          Nat.shiftLeft_lt (m := fmt.fracWidth - magnitudeNat.log2)
            (Nat.lt_log2_self (n := magnitudeNat))
        have hexponent :
            magnitudeNat.log2 + 1 + (fmt.fracWidth - magnitudeNat.log2) =
              fmt.fracWidth + 1 := by
          omega
        rw [hexponent] at hshifted
        exact hshifted.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      rw [← UInt64.ofNat_toNat (x := fracWidthWord - leading), hshiftNat,
        FloatLib.Numerics.FixedWord.shiftLeft_toNat magnitude _ hshiftLt hfit]
  have hroundedDef :
      (if fracWidthWord ≤ leading then
          FloatLib.Numerics.FixedWord.roundShiftRightEven magnitude
            (leading - fracWidthWord).toNat
        else
          magnitude <<< (fracWidthWord - leading)) = rounded := rfl
  have hroundedNatDef :
      (if fmt.fracWidth ≤ magnitudeNat.log2 then
          Numerics.roundShiftRightEven magnitudeNat (magnitudeNat.log2 - fmt.fracWidth)
        else
          magnitudeNat <<< (fmt.fracWidth - magnitudeNat.log2)) = roundedNat := rfl
  rw [hroundedDef, hroundedNatDef]
  have hroundedLower : 2 ^ fmt.fracWidth ≤ roundedNat := by
    have hbound :=
      pow2_le_roundMantissaToLeadingBitEven magnitudeNat fmt.fracWidth hmagnitudeNe
    simpa [roundMantissaToLeadingBitEven, roundedNat, pow2_eq_two_pow] using hbound
  have hnormal : fmt.bias + 2 * fmt.fracWidth - 1 ≤ positionNat := by
    omega
  exact NativeWordProduct.finish_eq fmt hwidth sign position rounded
    positionNat roundedNat hposition hpositionAdd hrounded hnormal
    (hiddenBit_toNat_of_width fmt hwidth) (carryBit_toNat_of_width fmt hwidth (by omega))
    hroundedLower

/-- An accepted machine-word rounding is the unsigned-scale rounding of the exact kernel. -/
theorem roundMagnitude_refines
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 61)
    (offset : UInt64) (sign : Bool) (magnitude scale : UInt64)
    (hmagnitude : magnitude ≠ 0)
    (hscale : scale.toNat + offset.toNat < 2 ^ 62)
    (result : Model fmt)
    (hresult : roundMagnitude? fmt offset sign magnitude scale = some result) :
    result =
      FiniteScaleAdd.roundMagnitude fmt offset.toNat sign magnitude.toNat scale.toNat := by
  rw [roundMagnitude_eq_normalSpec fmt hwidth hexpWidth hfracWidth
    offset sign magnitude scale hmagnitude hscale] at hresult
  have hmagnitudeNe : magnitude.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hmagnitude
  unfold FiniteScaleAdd.roundMagnitude
  exact normalSpec_refines fmt sign magnitude.toNat _ hmagnitudeNe result hresult

/-! ## Signed magnitudes and alignment -/

private theorem toNat_ne_zero_of_ne_zero {value : UInt64} (h : value ≠ 0) :
    value.toNat ≠ 0 := by
  simpa [← UInt64.toNat_inj] using h

/-- An accepted aligned combination is the exact kernel's signed-magnitude combination. -/
theorem roundAligned_refines
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 61)
    (offset : UInt64) (leftSign rightSign : Bool) (left right scale : UInt64)
    (hleft : left ≠ 0) (hright : right ≠ 0)
    (hsum : left.toNat + right.toNat < 2 ^ 64)
    (hscale : scale.toNat + offset.toNat < 2 ^ 62)
    (result : Model fmt)
    (hresult : roundAligned? fmt offset leftSign rightSign left right scale = some result) :
    result =
      FiniteScaleAdd.roundMagnitudes fmt offset.toNat
        leftSign rightSign left.toNat right.toNat scale.toNat := by
  have hleftNat := toNat_ne_zero_of_ne_zero hleft
  have hrightNat := toNat_ne_zero_of_ne_zero hright
  unfold roundAligned? at hresult
  unfold FiniteScaleAdd.roundMagnitudes
  by_cases hsign : leftSign = rightSign
  · rw [ite_eq_left (by simp [hsign])] at hresult
    rw [ite_eq_left (by simp [hsign])]
    have hadd : (left + right).toNat = left.toNat + right.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum]
    have haddNe : left + right ≠ 0 := by
      intro h
      have hnat := congrArg UInt64.toNat h
      rw [hadd, UInt64.toNat_zero] at hnat
      omega
    rw [roundMagnitude_refines fmt hwidth hexpWidth hfracWidth offset leftSign (left + right)
      scale haddNe hscale result hresult, hadd]
  · rw [ite_eq_right (by simpa using hsign)] at hresult
    rw [ite_eq_right (by simpa using hsign)]
    by_cases heq : left = right
    · subst heq
      simp only [beq_self_eq_true, ite_true, Option.some.injEq] at hresult
      simp only [beq_self_eq_true, ite_true]
      exact hresult.symm
    · have heqNat : left.toNat ≠ right.toNat := by
        intro h
        exact heq (UInt64.toNat_inj.mp h)
      rw [ite_eq_right (by simpa using heq)] at hresult
      rw [ite_eq_right (by simpa using heqNat)]
      by_cases hlt : left < right
      · have hltNat : left.toNat < right.toNat := UInt64.lt_iff_toNat_lt.mp hlt
        rw [ite_eq_left hlt] at hresult
        rw [ite_eq_left hltNat]
        have hsub : (right - left).toNat = right.toNat - left.toNat :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hlt)
        have hsubNe : right - left ≠ 0 := by
          intro h
          have hnat := congrArg UInt64.toNat h
          rw [hsub, UInt64.toNat_zero] at hnat
          omega
        rw [roundMagnitude_refines fmt hwidth hexpWidth hfracWidth offset rightSign
          (right - left) scale hsubNe hscale result hresult, hsub]
      · have hltNat : ¬left.toNat < right.toNat := by
          intro h
          exact hlt (UInt64.lt_iff_toNat_lt.mpr h)
        have hgt : right < left := by
          apply UInt64.lt_iff_toNat_lt.mpr
          omega
        rw [ite_eq_right hlt] at hresult
        rw [ite_eq_right hltNat]
        have hsub : (left - right).toNat = left.toNat - right.toNat :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hgt)
        have hsubNe : left - right ≠ 0 := by
          intro h
          have hnat := congrArg UInt64.toNat h
          rw [hsub, UInt64.toNat_zero] at hnat
          omega
        rw [roundMagnitude_refines fmt hwidth hexpWidth hfracWidth offset leftSign
          (left - right) scale hsubNe hscale result hresult, hsub]

/-- The machine-word finite scale is the compact finite scale of the exact kernel. -/
theorem finiteScale_toNat_eq_scale (exponent : UInt64) :
    (FloatLib.Numerics.FixedWord.finiteScale exponent).toNat =
      FiniteKernel.scale exponent.toNat := by
  rw [FloatLib.Numerics.FixedWord.finiteScale_toNat]
  unfold FiniteKernel.scale
  by_cases hzero : exponent = 0
  · subst hzero
    simp
  · have hzeroNat : exponent.toNat ≠ 0 := toNat_ne_zero_of_ne_zero hzero
    simp [hzero, hzeroNat]

private theorem finiteScale_toNat_lt (fmt : FloatFormat)
    (hexpWidth : fmt.expWidth ≤ 30) (exponent : UInt64)
    (hexponent : exponent.toNat < 2 ^ fmt.expWidth) :
    (FloatLib.Numerics.FixedWord.finiteScale exponent).toNat < 2 ^ 31 := by
  have hpow : 2 ^ fmt.expWidth ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hexpWidth
  rw [FloatLib.Numerics.FixedWord.finiteScale_toNat]
  split
  · exact Nat.two_pow_pos _
  · norm_num at hpow ⊢
    omega

private theorem shifted_toNat (fmt : FloatFormat) (hfracWidth : fmt.fracWidth ≤ 61)
    (mantissa shift : UInt64)
    (hmantissa : mantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hshift : shift.toNat + fmt.fracWidth ≤ 62) :
    (mantissa <<< shift).toNat = mantissa.toNat <<< shift.toNat ∧
      mantissa.toNat <<< shift.toNat < 2 ^ 63 := by
  have hfit : mantissa.toNat <<< shift.toNat < 2 ^ 63 := by
    have hshifted := Nat.shiftLeft_lt (m := shift.toNat) hmantissa
    exact hshifted.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨?_, hfit⟩
  have hshiftNat :=
    FloatLib.Numerics.FixedWord.shiftLeft_toNat mantissa shift.toNat (by omega)
      (hfit.trans (by norm_num))
  rwa [UInt64.ofNat_toNat] at hshiftNat


/-! ## Sticky alignment for large scale gaps -/

/-- With a normal larger significand and a small enough lower operand, the exact aligned magnitude
has its leading bit at least at `width + gap - 1`. -/
theorem alignedMagnitude_lower (width high low gap : Nat) (sameSign : Bool)
    (hhighLower : 2 ^ width ≤ high) (hlow : low ≤ 2 ^ (width + gap - 1)) (hgap : 3 ≤ gap) :
    2 ^ (width + gap - 1) ≤
      (if sameSign then high * 2 ^ gap + low else high * 2 ^ gap - low) := by
  have hpowGap : 2 ^ (width + gap) = 2 ^ width * 2 ^ gap := Nat.pow_add _ _ _
  have hhighGap : 2 ^ (width + gap) ≤ high * 2 ^ gap := by
    rw [hpowGap]
    exact Nat.mul_le_mul_right _ hhighLower
  have hhalf : 2 ^ (width + gap) = 2 ^ (width + gap - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  split <;> omega

end Model.NativeSmallWordAdd

/--
With a normal larger significand, three guard positions and a sticky bit round like the exact sum:
the exact magnitude keeps at least `fracWidth + 2` bits above the jammed positions.
-/
theorem Model.FiniteScaleAdd.roundMagnitude_shiftRightJam (fmt : FloatFormat) (roundOffset : Nat)
    (highSign lowSign : Bool) (high low gap scale : Nat)
    (hhighLower : 2 ^ fmt.fracWidth ≤ high) (hlow : low ≤ 2 ^ (fmt.fracWidth + gap - 1))
    (hgap : 3 ≤ gap) :
    FiniteScaleAdd.roundMagnitude fmt roundOffset highSign
        (Numerics.shiftRightJam
          (if highSign == lowSign then high * 2 ^ gap + low else high * 2 ^ gap - low) (gap - 3))
        (scale + (gap - 3)) =
      FiniteScaleAdd.roundMagnitudes fmt roundOffset highSign lowSign (high <<< gap) low scale := by
  have hbound := NativeSmallWordAdd.alignedMagnitude_lower fmt.fracWidth high low gap
    (highSign == lowSign) hhighLower hlow hgap
  have hround (magnitude : Nat) (hbound : 2 ^ (fmt.fracWidth + gap - 1) ≤ magnitude) :
      FiniteScaleAdd.roundMagnitude fmt roundOffset highSign
          (Numerics.shiftRightJam magnitude (gap - 3)) (scale + (gap - 3)) =
        FiniteScaleAdd.roundMagnitude fmt roundOffset highSign magnitude scale := by
    have hpositive := (Nat.two_pow_pos _).trans_le hbound
    have hleading : gap - 3 + fmt.fracWidth + 2 ≤ magnitude.log2 := by
      have := (Nat.le_log2 hpositive.ne').2 hbound
      omega
    unfold FiniteScaleAdd.roundMagnitude
    rw [show scale + (gap - 3) + roundOffset = (scale + roundOffset) + (gap - 3) by omega]
    exact FiniteProductRound.round_shiftRightJam fmt highSign magnitude
      (scale + roundOffset) (gap - 3) hleading
  rw [hround _ hbound, Nat.shiftLeft_eq]
  have hlowLt : low < high * 2 ^ gap := by
    have := NativeSmallWordAdd.alignedMagnitude_lower fmt.fracWidth high low gap false
      hhighLower hlow hgap
    simp only [Bool.false_eq_true, ite_false] at this
    have hpos : 0 < 2 ^ (fmt.fracWidth + gap - 1) := Nat.two_pow_pos _
    omega
  by_cases hsign : highSign = lowSign
  · subst hsign
    simp only [FiniteScaleAdd.roundMagnitudes, beq_self_eq_true, ite_true]
  · have hsignBeq : (highSign == lowSign) = false := by simpa using hsign
    simp only [hsignBeq, Bool.false_eq_true, ite_false, FiniteScaleAdd.roundMagnitudes,
      beq_iff_eq, Nat.ne_of_gt hlowLt, Nat.not_lt_of_ge hlowLt.le]

namespace Model.NativeSmallWordAdd

open NativeSmallWord

/-- The machine-word sticky magnitude is the natural-number jam of the exact aligned sum. -/
private theorem jammedMagnitude_toNat (sameSign : Bool) (high low gap : UInt64)
    (hhigh : high.toNat < 2 ^ 60) (hlowLt : low.toNat < high.toNat * 2 ^ gap.toNat)
    (hlowNe : low.toNat ≠ 0) (hgap : 3 ≤ gap.toNat) :
    (jammedMagnitude sameSign high low gap).toNat =
      Numerics.shiftRightJam
        (if sameSign then high.toNat * 2 ^ gap.toNat + low.toNat
          else high.toNat * 2 ^ gap.toNat - low.toNat)
        (gap.toNat - 3) := by
  have hdiscard : (gap - 3).toNat = gap.toNat - 3 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hgap))
  set d := gap.toNat - 3 with hd
  have hlowerNat : (if gap - 3 < 64 then low >>> (gap - 3) else 0).toNat = low.toNat / 2 ^ d := by
    split
    · rename_i hsmall
      have hsmallNat : d < 64 := by
        have := UInt64.lt_iff_toNat_lt.mp hsmall
        rw [hdiscard] at this
        simpa using this
      rw [UInt64.toNat_shiftRight, hdiscard, Nat.shiftRight_eq_div_pow]
      congr 2
      exact Nat.mod_eq_of_lt hsmallNat
    · rename_i hlarge
      have hlargeNat : 64 ≤ d := by
        have := UInt64.not_lt.mp hlarge
        have h2 := UInt64.le_iff_toNat_le.mp this
        rw [hdiscard] at h2
        simpa using h2
      rw [UInt64.toNat_zero, eq_comm, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
      exact low.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) hlargeNat)
  have hexact :
      (decide (gap - 3 < 64) &&
          (if gap - 3 < 64 then low >>> (gap - 3) else 0) <<< (gap - 3) == low) =
        decide (low.toNat % 2 ^ d = 0) := by
    by_cases hsmall : gap - 3 < 64
    · have hsmallNat : d < 64 := by
        have := UInt64.lt_iff_toNat_lt.mp hsmall
        rw [hdiscard] at this
        simpa using this
      simp only [hsmall, decide_true, ite_true, Bool.true_and]
      apply Bool.eq_iff_iff.mpr
      rw [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftLeft,
        UInt64.toNat_shiftRight, hdiscard, Nat.mod_eq_of_lt (show d < 64 from hsmallNat),
        Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
      have hle : low.toNat / 2 ^ d * 2 ^ d ≤ low.toNat := Nat.div_mul_le_self _ _
      rw [Nat.mod_eq_of_lt (hle.trans_lt low.toNat_lt)]
      have := Nat.div_add_mod' low.toNat (2 ^ d)
      omega
    · have hlargeNat : 64 ≤ d := by
        have := UInt64.not_lt.mp hsmall
        have h2 := UInt64.le_iff_toNat_le.mp this
        rw [hdiscard] at h2
        simpa using h2
      simp only [hsmall, decide_false, Bool.false_and]
      symm
      rw [decide_eq_false_iff_not, Nat.mod_eq_of_lt
        (low.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) hlargeNat))]
      exact hlowNe
  have hupper : (high <<< 3).toNat = high.toNat * 2 ^ 3 := by
    have hfit : high.toNat <<< 3 < 2 ^ 64 := by
      rw [Nat.shiftLeft_eq]
      calc high.toNat * 2 ^ 3 < 2 ^ 60 * 2 ^ 3 :=
            Nat.mul_lt_mul_of_pos_right hhigh (by decide)
        _ ≤ 2 ^ 64 := by norm_num
    have h := FloatLib.Numerics.FixedWord.shiftLeft_toNat high 3 (by decide) hfit
    simpa [Nat.shiftLeft_eq] using h
  have hgapSplit : high.toNat * 2 ^ gap.toNat = high.toNat * 2 ^ 3 * 2 ^ d := by
    rw [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  have hlowSplit : low.toNat < high.toNat * 2 ^ 3 * 2 ^ d := by
    rw [← hgapSplit]
    exact hlowLt
  have hquot : low.toNat / 2 ^ d < high.toNat * 2 ^ 3 :=
    Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hlowSplit)
  unfold jammedMagnitude FloatLib.Numerics.FixedWord.jamCombine
  simp only [hexact]
  rw [hgapSplit]
  have hupperFit : high.toNat * 2 ^ 3 < 2 ^ 63 := by
    calc high.toNat * 2 ^ 3 < 2 ^ 60 * 2 ^ 3 :=
          Nat.mul_lt_mul_of_pos_right hhigh (by decide)
      _ = 2 ^ 63 := by norm_num
  cases sameSign
  · simp only [Bool.false_eq_true, ite_false]
    rw [Numerics.shiftRightJam_mul_two_pow_sub _ _ _ hlowSplit.le]
    have hsubLe : (if gap - 3 < 64 then low >>> (gap - 3) else 0) ≤ high <<< 3 := by
      apply UInt64.le_iff_toNat_le.mpr
      rw [hlowerNat, hupper]
      omega
    by_cases hz : low.toNat % 2 ^ d = 0
    · simp only [hz, decide_true, ite_true]
      rw [UInt64.toNat_sub_of_le _ _ hsubLe, hupper, hlowerNat]
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      have hone : (1 : UInt64) ≤ high <<< 3 - (if gap - 3 < 64 then low >>> (gap - 3) else 0) := by
        apply UInt64.le_iff_toNat_le.mpr
        rw [UInt64.toNat_sub_of_le _ _ hsubLe, hupper, hlowerNat]
        simp only [UInt64.reduceToNat]
        omega
      rw [UInt64.toNat_or, UInt64.toNat_sub_of_le _ _ hone, UInt64.toNat_sub_of_le _ _ hsubLe,
        hupper, hlowerNat]
      rfl
  · simp only [ite_true]
    rw [Numerics.shiftRightJam_add_mul_two_pow]
    have hsumFit : high.toNat * 2 ^ 3 + low.toNat / 2 ^ d < 2 ^ 64 := by omega
    have hsum : (high <<< 3 + (if gap - 3 < 64 then low >>> (gap - 3) else 0)).toNat =
        high.toNat * 2 ^ 3 + low.toNat / 2 ^ d := by
      rw [UInt64.toNat_add, hupper, hlowerNat]
      exact Nat.mod_eq_of_lt hsumFit
    by_cases hz : low.toNat % 2 ^ d = 0
    · simp only [hz, decide_true, ite_true]
      exact hsum
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      rw [UInt64.toNat_or, hsum]
      rfl

/-- An accepted sticky alignment is the exact signed-magnitude combination of the same fields. -/
theorem roundJammed_refines
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 61)
    (offset : UInt64) (highSign lowSign : Bool) (high low gap scale : UInt64)
    (hlow : low.toNat ≤ 2 ^ (fmt.fracWidth + gap.toNat - 1))
    (hlowNe : low ≠ 0)
    (hscale : scale.toNat + gap.toNat + offset.toNat < 2 ^ 62)
    (result : Model fmt)
    (hresult : roundJammed? fmt offset highSign lowSign high low gap scale = some result) :
    result =
      FiniteScaleAdd.roundMagnitudes fmt offset.toNat
        highSign lowSign (high.toNat <<< gap.toNat) low.toNat scale.toNat := by
  unfold roundJammed? at hresult
  split at hresult
  · rename_i hguard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hguard
    obtain ⟨⟨hhidden, hhighLt⟩, hgap⟩ := hguard
    have hhighLower : 2 ^ fmt.fracWidth ≤ high.toNat := by
      have := UInt64.le_iff_toNat_le.mp hhidden
      rwa [NativeSmallWord.hiddenBit_toNat_of_width fmt hwidth] at this
    have hhigh : high.toNat < 2 ^ 60 := by simpa using UInt64.lt_iff_toNat_lt.mp hhighLt
    have hgapNat : 3 ≤ gap.toNat := by simpa using UInt64.le_iff_toNat_le.mp hgap
    have hlowNeNat := toNat_ne_zero_of_ne_zero hlowNe
    have hbelow := alignedMagnitude_lower fmt.fracWidth high.toNat low.toNat gap.toNat false
      hhighLower hlow hgapNat
    have hlowLt : low.toNat < high.toNat * 2 ^ gap.toNat := by
      simp only [Bool.false_eq_true, ite_false] at hbelow
      have hpos : 0 < 2 ^ (fmt.fracWidth + gap.toNat - 1) := Nat.two_pow_pos _
      omega
    have hmag := jammedMagnitude_toNat (highSign == lowSign) high low gap hhigh hlowLt
      hlowNeNat hgapNat
    have hdiscard : (gap - 3).toNat = gap.toNat - 3 :=
      UInt64.toNat_sub_of_le _ _ hgap
    have hscaleSum : (scale + (gap - 3)).toNat = scale.toNat + (gap.toNat - 3) := by
      rw [UInt64.toNat_add, hdiscard]
      exact Nat.mod_eq_of_lt (by omega)
    have hmagNe : jammedMagnitude (highSign == lowSign) high low gap ≠ 0 := by
      intro h
      have hzero := congrArg UInt64.toNat h
      rw [hmag, UInt64.toNat_zero] at hzero
      refine Numerics.shiftRightJam_ne_zero _ _ ?_ hzero
      exact (Nat.pow_le_pow_right (by decide) (by omega)).trans
        (alignedMagnitude_lower fmt.fracWidth high.toNat low.toNat gap.toNat _ hhighLower hlow
          hgapNat)
    have hscaleBound : (scale + (gap - 3)).toNat + offset.toNat < 2 ^ 62 := by
      rw [hscaleSum]
      omega
    rw [roundMagnitude_refines fmt hwidth hexpWidth hfracWidth offset highSign _ _ hmagNe
      hscaleBound result hresult, hmag, hscaleSum]
    exact FiniteScaleAdd.roundMagnitude_shiftRightJam fmt _ highSign lowSign high.toNat low.toNat
      gap.toNat scale.toNat hhighLower hlow hgapNat
  · simp at hresult

private theorem addFields_eq_shift_alignment (fmt : FloatFormat)
    (xSign : Bool) (xExponent xMantissa : UInt64)
    (ySign : Bool) (yExponent yMantissa : UInt64) :
    addFields? fmt xSign xExponent xMantissa ySign yExponent yMantissa =
      (if xMantissa == 0 || yMantissa == 0 then
        none
      else
        let xScale := FloatLib.Numerics.FixedWord.finiteScale xExponent
        let yScale := FloatLib.Numerics.FixedWord.finiteScale yExponent
        if xScale ≤ yScale then
          let shift := yScale - xScale
          if shift ≤ shiftLimit fmt then
            roundAligned? fmt (alignOffset fmt) xSign ySign xMantissa (yMantissa <<< shift) xScale
          else
            roundJammed? fmt (alignOffset fmt) ySign xSign yMantissa xMantissa shift xScale
        else
          let shift := xScale - yScale
          if shift ≤ shiftLimit fmt then
            roundAligned? fmt (alignOffset fmt) xSign ySign (xMantissa <<< shift) yMantissa yScale
          else
            roundJammed? fmt (alignOffset fmt) xSign ySign xMantissa yMantissa shift yScale) := by
  unfold addFields?
  split
  · rfl
  · by_cases hscale :
        FloatLib.Numerics.FixedWord.finiteScale xExponent =
          FloatLib.Numerics.FixedWord.finiteScale yExponent <;>
      simp [hscale]

/--
An accepted field addition is the exact unsigned-scale sum of the same fields.

The exponent bounds keep every scale below `2 ^ 31` and the significand bounds keep the aligned
same-sign sum below `2 ^ 64`, which is all the machine-word transfer needs.
-/
theorem addFields_refines
    (fmt : FloatFormat)
    (hieee : fmt.isIEEE = true)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 61)
    (xSign : Bool) (xExponent xMantissa : UInt64)
    (ySign : Bool) (yExponent yMantissa : UInt64)
    (hxExponent : xExponent.toNat < 2 ^ fmt.expWidth)
    (hyExponent : yExponent.toNat < 2 ^ fmt.expWidth)
    (hxMantissa : xMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hyMantissa : yMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (result : Model fmt)
    (hresult :
      addFields? fmt xSign xExponent xMantissa ySign yExponent yMantissa = some result) :
    result =
      FiniteKernel.addFields fmt
        xSign xExponent.toNat xMantissa.toNat ySign yExponent.toNat yMantissa.toNat := by
  have hpowFrac : 2 ^ (fmt.fracWidth + 1) ≤ 2 ^ 62 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hxMantissa62 : xMantissa.toNat < 2 ^ 62 := hxMantissa.trans_le hpowFrac
  have hyMantissa62 : yMantissa.toNat < 2 ^ 62 := hyMantissa.trans_le hpowFrac
  rw [addFields_eq_shift_alignment] at hresult
  by_cases hzero : (xMantissa == 0 || yMantissa == 0) = true
  · simp [hzero] at hresult
  rw [ite_eq_right hzero] at hresult
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hzero
  obtain ⟨hxNe, hyNe⟩ := hzero
  have hxNeNat := toNat_ne_zero_of_ne_zero hxNe
  have hyNeNat := toNat_ne_zero_of_ne_zero hyNe
  have hxScale := finiteScale_toNat_eq_scale xExponent
  have hyScale := finiteScale_toNat_eq_scale yExponent
  have hxScaleLt := finiteScale_toNat_lt fmt hexpWidth xExponent hxExponent
  have hyScaleLt := finiteScale_toNat_lt fmt hexpWidth yExponent hyExponent
  have hlimit := shiftLimit_toNat fmt hfracWidth
  have hoffset : (alignOffset fmt).toNat = FiniteKernel.finiteScaleOffset fmt :=
    alignOffset_toNat fmt hexpWidth hfracWidth
  have hoffsetLt : (alignOffset fmt).toNat < 2 ^ 31 := by
    have := exponentBias_lt fmt hexpWidth
    rw [alignOffset_toNat fmt hexpWidth hfracWidth]
    norm_num at this ⊢
    omega
  unfold FiniteKernel.addFields
  rw [ite_eq_left hieee]
  unfold FiniteScaleAdd.roundSum
  rw [ite_eq_right (by simpa using hxNeNat), ite_eq_right (by simpa using hyNeNat)]
  set xScale := FloatLib.Numerics.FixedWord.finiteScale xExponent with hxScaleDef
  set yScale := FloatLib.Numerics.FixedWord.finiteScale yExponent with hyScaleDef
  by_cases hle : xScale ≤ yScale
  · have hleNat : FiniteKernel.scale xExponent.toNat ≤ FiniteKernel.scale yExponent.toNat := by
      rw [← hxScale, ← hyScale]
      exact UInt64.le_iff_toNat_le.mp hle
    rw [ite_eq_left hle] at hresult
    rw [ite_eq_left hleNat, FiniteScaleAdd.roundAligned_eq,
      FiniteScaleAdd.roundMagnitudes_comm]
    by_cases hshift : yScale - xScale ≤ shiftLimit fmt
    · rw [ite_eq_left hshift] at hresult
      have hshiftNat :
          (yScale - xScale).toNat =
            FiniteKernel.scale yExponent.toNat - FiniteKernel.scale xExponent.toNat := by
        rw [UInt64.toNat_sub_of_le _ _ hle, hxScale, hyScale]
      have hshiftBound : (yScale - xScale).toNat + fmt.fracWidth ≤ 62 := by
        have hnat := UInt64.le_iff_toNat_le.mp hshift
        rw [hlimit] at hnat
        omega
      obtain ⟨hshifted, hshiftedLt⟩ :=
        shifted_toNat fmt hfracWidth yMantissa (yScale - xScale) hyMantissa hshiftBound
      have hshiftedNe : yMantissa <<< (yScale - xScale) ≠ 0 := by
        intro h
        have hnat := congrArg UInt64.toNat h
        rw [hshifted, UInt64.toNat_zero, Nat.shiftLeft_eq] at hnat
        exact absurd hnat (Nat.mul_ne_zero hyNeNat (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)))
      have hsum : xMantissa.toNat + (yMantissa <<< (yScale - xScale)).toNat < 2 ^ 64 := by
        rw [hshifted]
        norm_num at hxMantissa62 hshiftedLt ⊢
        omega
      have hscaleBound : xScale.toNat + (alignOffset fmt).toNat < 2 ^ 62 := by
        norm_num at hxScaleLt hoffsetLt ⊢
        omega
      rw [roundAligned_refines fmt hwidth hexpWidth hfracWidth (alignOffset fmt) xSign ySign
        xMantissa (yMantissa <<< (yScale - xScale)) xScale hxNe hshiftedNe hsum hscaleBound
        result hresult, hshifted, hshiftNat, hxScale, hoffset]
    · rw [ite_eq_right hshift] at hresult
      have hshiftNat :
          (yScale - xScale).toNat =
            FiniteKernel.scale yExponent.toNat - FiniteKernel.scale xExponent.toNat := by
        rw [UInt64.toNat_sub_of_le _ _ hle, hxScale, hyScale]
      have hscaleBound :
          xScale.toNat + (yScale - xScale).toNat + (alignOffset fmt).toNat < 2 ^ 62 := by
        rw [UInt64.toNat_sub_of_le _ _ hle]
        have := UInt64.le_iff_toNat_le.mp hle
        norm_num at hyScaleLt hoffsetLt ⊢
        omega
      have hlowBound :
          xMantissa.toNat ≤ 2 ^ (fmt.fracWidth + (yScale - xScale).toNat - 1) := by
        have hgt := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hshift)
        rw [hlimit] at hgt
        exact hxMantissa.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
      rw [FiniteScaleAdd.roundMagnitudes_comm, roundJammed_refines fmt hwidth hexpWidth hfracWidth
        (alignOffset fmt) ySign xSign yMantissa xMantissa (yScale - xScale) xScale hlowBound hxNe
        hscaleBound result hresult, hshiftNat, hxScale, hoffset]
  · have hleNat :
        ¬FiniteKernel.scale xExponent.toNat ≤ FiniteKernel.scale yExponent.toNat := by
      intro h
      apply hle
      apply UInt64.le_iff_toNat_le.mpr
      rwa [hxScale, hyScale]
    have hlt : yScale ≤ xScale := by
      apply UInt64.le_iff_toNat_le.mpr
      have hnat : ¬xScale.toNat ≤ yScale.toNat := fun h => hle (UInt64.le_iff_toNat_le.mpr h)
      omega
    rw [ite_eq_right hle] at hresult
    rw [ite_eq_right hleNat, FiniteScaleAdd.roundAligned_eq]
    by_cases hshift : xScale - yScale ≤ shiftLimit fmt
    · rw [ite_eq_left hshift] at hresult
      have hshiftNat :
          (xScale - yScale).toNat =
            FiniteKernel.scale xExponent.toNat - FiniteKernel.scale yExponent.toNat := by
        rw [UInt64.toNat_sub_of_le _ _ hlt, hxScale, hyScale]
      have hshiftBound : (xScale - yScale).toNat + fmt.fracWidth ≤ 62 := by
        have hnat := UInt64.le_iff_toNat_le.mp hshift
        rw [hlimit] at hnat
        omega
      obtain ⟨hshifted, hshiftedLt⟩ :=
        shifted_toNat fmt hfracWidth xMantissa (xScale - yScale) hxMantissa hshiftBound
      have hshiftedNe : xMantissa <<< (xScale - yScale) ≠ 0 := by
        intro h
        have hnat := congrArg UInt64.toNat h
        rw [hshifted, UInt64.toNat_zero, Nat.shiftLeft_eq] at hnat
        exact absurd hnat (Nat.mul_ne_zero hxNeNat (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)))
      have hsum : (xMantissa <<< (xScale - yScale)).toNat + yMantissa.toNat < 2 ^ 64 := by
        rw [hshifted]
        norm_num at hyMantissa62 hshiftedLt ⊢
        omega
      have hscaleBound : yScale.toNat + (alignOffset fmt).toNat < 2 ^ 62 := by
        norm_num at hyScaleLt hoffsetLt ⊢
        omega
      rw [roundAligned_refines fmt hwidth hexpWidth hfracWidth (alignOffset fmt) xSign ySign
        (xMantissa <<< (xScale - yScale)) yMantissa yScale hshiftedNe hyNe hsum hscaleBound
        result hresult, hshifted, hshiftNat, hyScale, hoffset]
    · rw [ite_eq_right hshift] at hresult
      have hshiftNat :
          (xScale - yScale).toNat =
            FiniteKernel.scale xExponent.toNat - FiniteKernel.scale yExponent.toNat := by
        rw [UInt64.toNat_sub_of_le _ _ hlt, hxScale, hyScale]
      have hscaleBound :
          yScale.toNat + (xScale - yScale).toNat + (alignOffset fmt).toNat < 2 ^ 62 := by
        rw [UInt64.toNat_sub_of_le _ _ hlt]
        have := UInt64.le_iff_toNat_le.mp hlt
        norm_num at hxScaleLt hoffsetLt ⊢
        omega
      have hlowBound :
          yMantissa.toNat ≤ 2 ^ (fmt.fracWidth + (xScale - yScale).toNat - 1) := by
        have hgt := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hshift)
        rw [hlimit] at hgt
        exact hyMantissa.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
      rw [roundJammed_refines fmt hwidth hexpWidth hfracWidth (alignOffset fmt) xSign ySign
        xMantissa yMantissa (xScale - yScale) yScale hlowBound hyNe hscaleBound result hresult,
        hshiftNat, hyScale, hoffset]

/-! ## Storage-word decoding -/

/-- The generic finite decoder sees the fields the one-word kernel extracts from a finite word. -/
theorem decode_of_finite {fmt : FloatFormat}
    (hieee : fmt.isIEEE = true) (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt)
    (hfinite : exponentField fmt (toWord x) ≠ exponentMask fmt) :
    FiniteKernel.decode? x =
      some {
        sign := signField fmt (toWord x)
        exponent := (exponentField fmt (toWord x)).toNat
        mantissa :=
          (NativeSmallWordFinite.finiteMantissa fmt (exponentField fmt (toWord x))
            (fractionField fmt (toWord x))).toNat } := by
  rw [← NativeSmallWordFinite.decode_eq ⟨hieee, hwidth⟩ x]
  unfold NativeSmallWordFinite.decode?
  simp only [beq_iff_eq, hfinite, ite_false]

/-- Negating a finite word keeps its exponent and fraction fields and toggles its sign. -/
theorem decode_neg_of_finite {fmt : FloatFormat}
    (hieee : fmt.isIEEE = true) (hwidth : fmt.bitWidth ≤ 64)
    (y : Model fmt)
    (hfinite : exponentField fmt (toWord y) ≠ exponentMask fmt) :
    FiniteKernel.decode? (neg y) =
      some {
        sign := !signField fmt (toWord y)
        exponent := (exponentField fmt (toWord y)).toNat
        mantissa :=
          (NativeSmallWordFinite.finiteMantissa fmt (exponentField fmt (toWord y))
            (fractionField fmt (toWord y))).toNat } := by
  have hexponent : exponentField fmt (toWord (neg y)) = exponentField fmt (toWord y) := by
    apply UInt64.toNat_inj.mp
    rw [exponentField_toNat hwidth, exponentField_toNat hwidth, expField_neg]
  have hfraction : fractionField fmt (toWord (neg y)) = fractionField fmt (toWord y) := by
    apply UInt64.toNat_inj.mp
    rw [fractionField_toNat hwidth, fractionField_toNat hwidth, fracField_neg]
  have hsign : signField fmt (toWord (neg y)) = !signField fmt (toWord y) := by
    rw [signField_eq hwidth, signField_eq hwidth, signBit_neg,
      ite_eq_left (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hieee)]
  rw [decode_of_finite hieee hwidth (neg y) (by rwa [hexponent]), hexponent, hfraction, hsign]

/-- The exponent field of a one-word value is a stored exponent. -/
theorem exponentField_toNat_lt {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt) :
    (exponentField fmt (toWord x)).toNat < 2 ^ fmt.expWidth := by
  rw [exponentField_toNat hwidth]
  exact Model.expField_lt_pow2 x

/-- The finite significand of a one-word value has at most `fracWidth + 1` bits. -/
theorem finiteMantissa_toNat_lt {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt) :
    (NativeSmallWordFinite.finiteMantissa fmt (exponentField fmt (toWord x))
      (fractionField fmt (toWord x))).toNat < 2 ^ (fmt.fracWidth + 1) := by
  unfold NativeSmallWordFinite.finiteMantissa
  split
  · rw [fractionField_toNat hwidth]
    exact (Model.fracField_lt_pow2 x).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  · exact (normalMantissa_bounds_of_width hwidth x).2

/--
An accepted one-word addition, or subtraction, is the exact compact finite kernel's answer.

With `negateRight` set the kernel toggles the right sign in machine words, and the theorem states
the claim for `neg y`. Declines fall outside the statement, and the dispatcher handles them with
the exact implementation. Only the capacity contract `Eligible` is assumed of the format.
-/
theorem addFinite_refines {fmt : FloatFormat}
    (heligible : Eligible fmt)
    (x y result : Model fmt) (negateRight : Bool)
    (hresult : addFinite? x y negateRight = some result) :
    FiniteKernel.add? x (if negateRight then neg y else y) = some result := by
  rcases heligible with ⟨hieee, hwidth, hexpWidth, hfracWidth⟩
  unfold addFinite? at hresult
  by_cases hexceptional :
      (exponentField fmt (toWord x) == exponentMask fmt ||
        exponentField fmt (toWord y) == exponentMask fmt) = true
  · simp [hexceptional] at hresult
  rw [ite_eq_right hexceptional] at hresult
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hexceptional
  obtain ⟨hxFinite, hyFinite⟩ := hexceptional
  have hxExponent := exponentField_toNat_lt hwidth x
  have hyExponent := exponentField_toNat_lt hwidth y
  have hxMantissa := finiteMantissa_toNat_lt hwidth x
  have hyMantissa := finiteMantissa_toNat_lt hwidth y
  unfold FiniteKernel.add?
  rw [decode_of_finite hieee hwidth x hxFinite]
  cases negateRight
  · simp only [Bool.false_eq_true, ite_false, Bool.xor_false] at hresult ⊢
    rw [decode_of_finite hieee hwidth y hyFinite]
    simp only
    rw [← FiniteKernel.addFields_eq]
    exact congrArg some
      (addFields_refines fmt hieee hwidth hexpWidth hfracWidth _ _ _ _ _ _
        hxExponent hyExponent hxMantissa hyMantissa result hresult).symm
  · simp only [ite_true, Bool.xor_true] at hresult ⊢
    rw [decode_neg_of_finite hieee hwidth y hyFinite]
    simp only
    rw [← FiniteKernel.addFields_eq]
    exact congrArg some
      (addFields_refines fmt hieee hwidth hexpWidth hfracWidth _ _ _ _ _ _
        hxExponent hyExponent hxMantissa hyMantissa result hresult).symm

/-! ## Storage-word entry points -/

private theorem model_eq_of_toNatBits {fmt : FloatFormat} {x y : Model fmt}
    (h : x.toNatBits = y.toNatBits) : x = y := by
  rw [← ofNatBits_toNatBits x, ← ofNatBits_toNatBits y, h]

theorem ofWord_zeroWord {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) (sign : Bool) :
    ofWord (fmt := fmt) (zeroWord fmt sign) = zero fmt sign := by
  unfold zeroWord zero
  by_cases h : (sign && fmt.supportsSignedZero) = true
  · simp only [h, ite_true]
    apply model_eq_of_toNatBits
    have hfield : fmt.expWidth + fmt.fracWidth < 64 := by
      unfold FloatFormat.bitWidth at hwidth; omega
    have hshift : ((1 : UInt64) <<< UInt64.ofNat (fmt.expWidth + fmt.fracWidth)).toNat =
        2 ^ (fmt.expWidth + fmt.fracWidth) :=
      FloatLib.Numerics.FixedWord.uint64_powTwo_toNat _ hfield
    rw [toNatBits_ofWord]
    simp only [packFields, ite_true, UInt64.zero_and, UInt64.zero_shiftLeft, UInt64.or_zero]
    rw [hshift]
    simp only [negZero, Model.toNatBits, FloatFormat.signMask, FloatFormat.ofWordNat,
      FloatFormat.signMaskNat, FloatFormat.signBitIndex, FloatFormat.bitWidth,
      Model.ofBits, BitVec.toNat_ofNat]
    have hlt : 2 ^ (fmt.expWidth + fmt.fracWidth) < 2 ^ (1 + fmt.expWidth + fmt.fracWidth) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    rw [Nat.mod_eq_of_lt hlt, show 1 + fmt.expWidth + fmt.fracWidth - 1 =
      fmt.expWidth + fmt.fracWidth by omega, Nat.mod_eq_of_lt hlt]
  · simp only [h]
    apply model_eq_of_toNatBits
    rw [toNatBits_ofWord]
    simp [posZero]

theorem roundMagnitude?_eq_map (fmt : FloatFormat) (offset : UInt64) (sign : Bool)
    (magnitude scale : UInt64) :
    roundMagnitude? fmt offset sign magnitude scale =
      (roundMagnitudeWord? fmt offset sign magnitude scale).map ofWord := by
  simp only [roundMagnitude?, roundMagnitudeWord?]
  split
  · rfl
  · rfl

theorem roundAligned?_eq_map {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64)
    (offset : UInt64) (leftSign rightSign : Bool) (left right scale : UInt64) :
    roundAligned? fmt offset leftSign rightSign left right scale =
      (roundAlignedWord? fmt offset leftSign rightSign left right scale).map ofWord := by
  simp only [roundAligned?, roundAlignedWord?]
  split_ifs <;> simp [roundMagnitude?_eq_map, ofWord_zeroWord hwidth]

theorem roundJammed?_eq_map (fmt : FloatFormat) (offset : UInt64) (highSign lowSign : Bool)
    (high low gap scale : UInt64) :
    roundJammed? fmt offset highSign lowSign high low gap scale =
      (roundJammedWord? fmt offset highSign lowSign high low gap scale).map ofWord := by
  simp only [roundJammed?, roundJammedWord?]
  split
  · exact roundMagnitude?_eq_map _ _ _ _ _
  · rfl

theorem addFields?_eq_map {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64)
    (xSign : Bool) (xExponent xMantissa : UInt64)
    (ySign : Bool) (yExponent yMantissa : UInt64) :
    addFields? fmt xSign xExponent xMantissa ySign yExponent yMantissa =
      (addFieldsWord? fmt xSign xExponent xMantissa ySign yExponent yMantissa).map ofWord := by
  simp only [addFields?, addFieldsWord?]
  split_ifs <;> simp [roundAligned?_eq_map hwidth, roundJammed?_eq_map]

/--
On storage words below the radix, `addFinite?` is the `ofWord` image of `addFiniteWord?`.
-/
theorem addFinite?_ofWord {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64)
    {xBits yBits : UInt64}
    (hx : xBits.toNat < 2 ^ fmt.bitWidth) (hy : yBits.toNat < 2 ^ fmt.bitWidth)
    (negateRight : Bool) :
    addFinite? (ofWord (fmt := fmt) xBits) (ofWord yBits) negateRight =
      (addFiniteWord? fmt xBits yBits negateRight).map ofWord := by
  simp only [addFinite?, addFiniteWord?, toWord_ofWord_of_lt hx, toWord_ofWord_of_lt hy]
  split_ifs <;> simp [addFields?_eq_map hwidth]

end Model.NativeSmallWordAdd
end FloatLib.Floats.Formats.BinaryInterchange
