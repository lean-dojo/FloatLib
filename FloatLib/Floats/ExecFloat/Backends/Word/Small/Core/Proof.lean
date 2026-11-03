/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Core.Runtime
public import FloatLib.Kernels.FixedWord.Core.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Optimized
import FloatLib.Floats.Formats.BinaryInterchange.Model.Lean
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Data.Rat.Cast.Order

/-!
# Correctness of native storage for one-word floating-point formats

The word conversions, field operations and packing of `Core.Runtime` are proved against the
exact-width carrier under the real capacity requirement, so the results hold for every configured
binary format that fits one machine word.

Arithmetic proofs reuse these facts and don't repeat masking and truncation arguments for each
operation. The descriptor constants of `Core.Runtime` are machine words computed by shifts.
`exponentMask_toNat`, `fractionMask_toNat`, `biasWord_toNat` and the threshold lemmas at the end
of this module give their natural-number values under the one-word capacity bound.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWord

/-- The native word has the same natural-number value as a carrier that fits in one word. -/
@[simp, grind =] theorem toWord_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt) :
    (toWord x).toNat = x.toNatBits := by
  unfold toWord
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
  exact x.bits.toFin.isLt.trans_le <|
    Nat.pow_le_pow_right (by decide) hwidth

/-- Masking with the storage mask reduces a native word modulo the format's radix. -/
theorem and_storageMask_toNat {fmt : FloatFormat} (bits : UInt64) :
    (bits &&& storageMask fmt).toNat = bits.toNat % 2 ^ fmt.bitWidth := by
  rw [UInt64.toNat_and]
  unfold storageMask
  split
  · rename_i hlt
    rw [powTwo_sub_one_toNat fmt.bitWidth hlt, Nat.and_two_pow_sub_one_eq_mod]
  · rename_i hge
    have hmask : (0xffffffffffffffff : UInt64).toNat = 2 ^ 64 - 1 := by decide
    have hbits : bits.toNat < 2 ^ 64 := UInt64.toNat_lt_size bits
    rw [hmask, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hbits, Nat.mod_eq_of_lt]
    exact hbits.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hge))

/-- Truncating a native word has the expected exact-width natural-number value. -/
@[simp, grind =] theorem toNatBits_ofWord {fmt : FloatFormat} (bits : UInt64) :
    (ofWord (fmt := fmt) bits).toNatBits =
      bits.toNat % 2 ^ fmt.bitWidth := by
  change (BitVec.ofNatLT (bits &&& storageMask fmt).toNat _).toNat =
    bits.toNat % 2 ^ fmt.bitWidth
  rw [BitVec.toNat_ofNatLT, and_storageMask_toNat]

/-- Zero-extension followed by exact-width truncation is identity for a one-word format. -/
@[simp] theorem ofWord_toWord {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt) :
    ofWord (toWord x) = x := by
  cases x with
  | mk bits =>
      apply congrArg Model.ofBits
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNatLT, and_storageMask_toNat, toWord_toNat hwidth]
      exact Nat.mod_eq_of_lt bits.toFin.isLt

private theorem fracWidth_lt_64 (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64) :
    fmt.fracWidth < 64 := by
  unfold FloatFormat.bitWidth at hwidth
  omega

private theorem fieldWidth_lt_64 (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64) :
    fmt.expWidth + fmt.fracWidth < 64 := by
  unfold FloatFormat.bitWidth at hwidth
  omega

private theorem expMask_lt_field (fmt : FloatFormat) :
    fmt.expAllOnesNat < 2 ^ fmt.expWidth := by
  unfold FloatFormat.expAllOnesNat
  have hpositive : 0 < 2 ^ fmt.expWidth := Nat.two_pow_pos _
  omega

private theorem fracMask_lt_field (fmt : FloatFormat) :
    fmt.fracMaskNat < 2 ^ fmt.fracWidth := by
  unfold FloatFormat.fracMaskNat
  have hpositive : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  omega

/-- Natural-number value of the native exponent mask for a one-word format. -/
theorem exponentMask_toNat {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) :
    (exponentMask fmt).toNat = fmt.expAllOnesNat := by
  have hexp : fmt.expWidth < 64 := by
    unfold FloatFormat.bitWidth at hwidth
    omega
  unfold exponentMask FloatFormat.expAllOnesNat
  exact powTwo_sub_one_toNat fmt.expWidth hexp

/-- Natural-number value of the native fraction mask for a one-word format. -/
theorem fractionMask_toNat {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) :
    (fractionMask fmt).toNat = fmt.fracMaskNat := by
  unfold fractionMask FloatFormat.fracMaskNat
  exact powTwo_sub_one_toNat fmt.fracWidth (fracWidth_lt_64 fmt hwidth)

/-- The machine-word bias is the conventional bias for every format that fits one word. -/
theorem biasWord_toNat {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) :
    (biasWord fmt).toNat = fmt.bias := by
  have hexp : fmt.expWidth < 64 := by
    unfold FloatFormat.bitWidth at hwidth
    omega
  have hexpTwo : 2 ≤ fmt.expWidth := fmt.expWidth_ge_two
  have hexpWord : (UInt64.ofNat fmt.expWidth).toNat = fmt.expWidth := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (lt_trans hexp (by norm_num))]
  have hone : (1 : UInt64) ≤ UInt64.ofNat fmt.expWidth := by
    rw [UInt64.le_iff_toNat_le, hexpWord, UInt64.toNat_one]
    omega
  have hsub : UInt64.ofNat fmt.expWidth - 1 = UInt64.ofNat (fmt.expWidth - 1) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ hone, hexpWord, UInt64.toNat_one, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (lt_trans (by omega : fmt.expWidth - 1 < 64) (by norm_num))]
  unfold biasWord FloatFormat.bias
  rw [hsub]
  exact powTwo_sub_one_toNat (fmt.expWidth - 1) (by omega)

/-- The integer bias is the conventional bias for every format that fits one word. -/
theorem biasInt_eq {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    biasInt fmt = Int.ofNat fmt.bias := by
  unfold biasInt
  rw [biasWord_toNat hwidth]

/-- Native exponent extraction has the same value as the canonical field decoder. -/
theorem exponentField_toNat {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt) :
    (exponentField fmt (toWord x)).toNat = Model.expField x := by
  rw [Model.expField_eq_internal_apply]
  unfold exponentField Model.Internal.expField
  rw [UInt64.toNat_and,
    FloatLib.Numerics.FixedWord.shiftRight_toNat _ _ (fracWidth_lt_64 fmt hwidth),
    toWord_toNat hwidth, exponentMask_toNat hwidth]

/-- The native test for the all-ones exponent field is the test on the generic exponent field. -/
theorem exponentField_eq_exponentMask_iff {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt) :
    exponentField fmt (toWord x) = exponentMask fmt ↔ Model.expField x = fmt.expAllOnesNat := by
  rw [← UInt64.toNat_inj, exponentField_toNat hwidth x, exponentMask_toNat hwidth]

/--
Bounds for a nonzero exponent extracted through the one-word representation.

Arithmetic kernels know the exponent is nonzero once they reject zero and subnormal operands.
This lemma adds the format-width bound, so no kernel repeats the bridge from `UInt64` fields to
`Model.expField`.
-/
theorem exponentField_bounds_of_ne_zero {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt)
    (hnonzero : exponentField fmt (toWord x) ≠ 0) :
    0 < (exponentField fmt (toWord x)).toNat ∧
      (exponentField fmt (toWord x)).toNat < 2 ^ fmt.expWidth := by
  constructor
  · apply Nat.pos_of_ne_zero
    intro h
    apply hnonzero
    apply UInt64.toNat_inj.mp
    simpa using h
  · rw [exponentField_toNat hwidth x]
    exact Model.expField_lt_pow2 x

/-- Native fraction extraction has the same value as the canonical field decoder. -/
theorem fractionField_toNat {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt) :
    (fractionField fmt (toWord x)).toNat = Model.fracField x := by
  rw [Model.fracField_eq_internal_apply]
  unfold fractionField Model.Internal.fracField
  rw [UInt64.toNat_and, fractionMask_toNat hwidth, toWord_toNat hwidth]

/-- Natural-number value of the implicit leading bit for a small one-word format. -/
theorem hiddenBit_toNat (fmt : FloatFormat) (hfracWidth : fmt.fracWidth ≤ 30) :
    (hiddenBit fmt).toNat = 2 ^ fmt.fracWidth := by
  unfold hiddenBit
  exact FloatLib.Numerics.FixedWord.uint64_powTwo_toNat _ (by omega)

/-- Natural-number value of the implicit bit for any format that fits in one storage word. -/
theorem hiddenBit_toNat_of_width (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64) :
    (hiddenBit fmt).toNat = 2 ^ fmt.fracWidth := by
  unfold hiddenBit
  exact FloatLib.Numerics.FixedWord.uint64_powTwo_toNat _ (fracWidth_lt_64 fmt hwidth)

/-- Natural-number value of the rounding carry bit for a small one-word format. -/
theorem carryBit_toNat (fmt : FloatFormat) (hfracWidth : fmt.fracWidth ≤ 30) :
    (carryBit fmt).toNat = 2 ^ (fmt.fracWidth + 1) := by
  unfold carryBit
  exact FloatLib.Numerics.FixedWord.uint64_powTwo_toNat _ (by omega)

/-- Natural-number value of the rounding carry bit for any format that fits in one storage word. -/
theorem carryBit_toNat_of_width (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64) :
    (carryBit fmt).toNat = 2 ^ (fmt.fracWidth + 1) := by
  have hexp := fmt.expWidth_ge_two
  unfold FloatFormat.bitWidth at hwidth
  unfold carryBit
  exact FloatLib.Numerics.FixedWord.uint64_powTwo_toNat _ (by omega)

/-- Decoded normal significand value for any format that fits in one storage word. -/
theorem normalMantissa_toNat {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt) :
    (fractionField fmt (toWord x) ||| hiddenBit fmt).toNat =
      2 ^ fmt.fracWidth + Model.fracField x := by
  rw [UInt64.toNat_or, fractionField_toNat hwidth,
    hiddenBit_toNat_of_width fmt hwidth]
  rw [Nat.or_two_pow_eq_add_of_lt (Model.fracField_lt_pow2 x)]
  rw [Nat.add_comm]

/--
The implicit-bit significand extracted from a one-word value is normalized.

Only the stored fraction-width bound is needed. The calling kernel classifies the source value
before it treats this word as a normal significand.
-/
theorem normalMantissa_bounds_of_width {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt) :
    2 ^ fmt.fracWidth ≤
        (fractionField fmt (toWord x) ||| hiddenBit fmt).toNat ∧
      (fractionField fmt (toWord x) ||| hiddenBit fmt).toNat <
        2 ^ (fmt.fracWidth + 1) := by
  rw [normalMantissa_toNat hwidth x, pow_succ]
  have hfrac := Model.fracField_lt_pow2 x
  omega

/-- Native sign extraction agrees with the canonical storage decoder. -/
theorem signField_eq {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt) :
    signField fmt (toWord x) = Model.signBit x := by
  have hindex : fmt.expWidth + fmt.fracWidth < 64 := fieldWidth_lt_64 fmt hwidth
  have hindexWord :
      (UInt64.ofNat (fmt.expWidth + fmt.fracWidth)).toNat = fmt.expWidth + fmt.fracWidth := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (lt_trans hindex (by norm_num))]
  have hlast : fmt.bitWidth - 1 = fmt.expWidth + fmt.fracWidth := by
    unfold FloatFormat.bitWidth
    omega
  rw [Model.signBit_eq_msb, BitVec.msb_eq_getLsbD_last, hlast]
  unfold signField
  rw [FloatLib.Numerics.FixedWord.bitAtWord_eq_testBit, toWord_toNat hwidth, hindexWord]
  rfl

/-- A left shift that keeps a `width`-bit word below `2 ^ 63` is exact. -/
theorem shiftLeft_toNat_of_width (value shift : UInt64) (width : Nat)
    (hvalue : value.toNat < 2 ^ width) (hshift : shift.toNat + width ≤ 63) :
    (value <<< shift).toNat = value.toNat <<< shift.toNat ∧
      value.toNat <<< shift.toNat < 2 ^ 63 := by
  have hfit : value.toNat <<< shift.toNat < 2 ^ 63 := by
    have hshifted := Nat.shiftLeft_lt (m := shift.toNat) hvalue
    exact hshifted.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨?_, hfit⟩
  have hshiftNat :=
    FloatLib.Numerics.FixedWord.shiftLeft_toNat value shift.toNat
      (hfit.trans (by norm_num))
  rwa [UInt64.ofNat_toNat] at hshiftNat

/-- An exact left shift of a nonzero word is nonzero. -/
theorem shiftLeft_ne_zero_of_toNat (value shift : UInt64) (hvalue : value.toNat ≠ 0)
    (hshifted : (value <<< shift).toNat = value.toNat <<< shift.toNat) :
    value <<< shift ≠ 0 := by
  intro h
  have hnat := congrArg UInt64.toNat h
  rw [hshifted, UInt64.toNat_zero, Nat.shiftLeft_eq] at hnat
  exact absurd hnat (Nat.mul_ne_zero hvalue (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)))

/--
An alignment shift that keeps a nonzero `width`-bit word below `2 ^ 63` is exact and nonzero, and
adding a second word below `2 ^ 63` to the shifted word does not wrap.
-/
theorem shiftLeft_add_fits (value other shift : UInt64) (width : Nat)
    (hvalue : value.toNat < 2 ^ width) (hne : value.toNat ≠ 0) (hother : other.toNat < 2 ^ 63)
    (hshift : shift.toNat + width ≤ 63) :
    (value <<< shift).toNat = value.toNat <<< shift.toNat ∧ value <<< shift ≠ 0 ∧
      (value <<< shift).toNat + other.toNat < 2 ^ 64 := by
  obtain ⟨hshifted, hshiftedLt⟩ := shiftLeft_toNat_of_width value shift width hvalue hshift
  refine ⟨hshifted, shiftLeft_ne_zero_of_toNat _ _ hne hshifted, ?_⟩
  rw [hshifted]
  norm_num at hother hshiftedLt ⊢
  omega

/--
The product scale `(x - 1) + (y - 1)` of two nonzero exponent fields `x` and `y` is computed
without wrapping when its value is below `2 ^ 64`.
-/
theorem productScale_toNat (x y : UInt64) (hx : 0 < x.toNat) (hy : 0 < y.toNat)
    (hfit : (x.toNat - 1) + (y.toNat - 1) < 2 ^ 64) :
    ((x - 1) + (y - 1)).toNat = (x.toNat - 1) + (y.toNat - 1) := by
  rw [UInt64.toNat_add, UInt64.toNat_sub_of_le x 1 (UInt64.le_iff_toNat_le.mpr hx),
    UInt64.toNat_sub_of_le y 1 (UInt64.le_iff_toNat_le.mpr hy), UInt64.toNat_one]
  exact Nat.mod_eq_of_lt hfit

/-- The masked exponent shifted into place stays below the format's radix. -/
private theorem exponentShift_lt_bitWidth (fmt : FloatFormat) (exponent : Nat) :
    (exponent &&& fmt.expAllOnesNat) <<< fmt.fracWidth < 2 ^ fmt.bitWidth := by
  have hshift := Nat.shiftLeft_lt (m := fmt.fracWidth)
    (Nat.and_lt_two_pow exponent (expMask_lt_field fmt))
  exact hshift.trans_le <|
    Nat.pow_le_pow_right (by decide) (by
      unfold FloatFormat.bitWidth
      omega)

/-- The natural-number value of a packed native word, field by field. -/
private theorem packFields_toNat {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (sign : Bool) (exponent fraction : UInt64) :
    (packFields fmt sign exponent fraction).toNat =
      (if sign then 1 <<< (fmt.expWidth + fmt.fracWidth) else 0) |||
        (exponent.toNat &&& fmt.expAllOnesNat) <<< fmt.fracWidth |||
        (fraction.toNat &&& fmt.fracMaskNat) := by
  unfold packFields
  rw [UInt64.toNat_or, UInt64.toNat_or]
  have hfrac : fmt.fracWidth < 64 := fracWidth_lt_64 fmt hwidth
  have hfield : fmt.expWidth + fmt.fracWidth < 64 := fieldWidth_lt_64 fmt hwidth
  have hexponentShift :
      (exponent.toNat &&& fmt.expAllOnesNat) <<< fmt.fracWidth < 2 ^ 64 :=
    (exponentShift_lt_bitWidth fmt exponent.toNat).trans_le <|
      Nat.pow_le_pow_right (by decide) hwidth
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_and, exponentMask_toNat hwidth, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (lt_trans hfrac (by norm_num)), Nat.mod_eq_of_lt hfrac,
    Nat.mod_eq_of_lt hexponentShift, UInt64.toNat_and, fractionMask_toNat hwidth]
  cases sign
  · simp
  · simp only [ite_true]
    rw [FloatLib.Numerics.FixedWord.uint64_powTwo_toNat _ hfield, Nat.one_shiftLeft]

/-- Native field packing agrees with the canonical exact-width constructor. -/
theorem ofWord_packFields {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (sign : Bool)
    (exponent fraction : UInt64) :
    ofWord (fmt := fmt) (packFields fmt sign exponent fraction) =
      Model.ofFields fmt sign exponent.toNat fraction.toNat := by
  rw [Model.ofFields_eq_internal]
  unfold Model.Internal.ofFields
  apply congrArg Model.ofBits
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNatLT, and_storageMask_toNat, packFields_toNat hwidth]
  unfold Model.Internal.mkBits
  simp only [BitVec.ofNatLT_eq_ofNat, BitVec.toNat_ofNat]
  rfl

/-- A native packed word uses no bits above the format's exact storage width. -/
theorem packFields_toNat_lt {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (sign : Bool)
    (exponent fraction : UInt64) :
    (packFields fmt sign exponent fraction).toNat <
      2 ^ fmt.bitWidth := by
  rw [packFields_toNat hwidth]
  have hexponentShift := exponentShift_lt_bitWidth fmt exponent.toNat
  have hfractionTarget :
      fraction.toNat &&& fmt.fracMaskNat < 2 ^ fmt.bitWidth :=
    (Nat.and_lt_two_pow fraction.toNat (fracMask_lt_field fmt)).trans_le <|
      Nat.pow_le_pow_right (by decide) (by
        unfold FloatFormat.bitWidth
        omega)
  have hsignTarget :
      (1 : Nat) <<< (fmt.expWidth + fmt.fracWidth) <
        2 ^ fmt.bitWidth := by
    simp only [Nat.shiftLeft_eq, one_mul]
    unfold FloatFormat.bitWidth
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  cases sign
  · simp only [Bool.false_eq_true, ite_false, Nat.zero_or]
    exact Nat.or_lt_two_pow hexponentShift hfractionTarget
  · simp only [ite_true]
    exact Nat.or_lt_two_pow
      (Nat.or_lt_two_pow hsignTarget hexponentShift)
      hfractionTarget

/-! ## Rounding thresholds in machine words -/

private theorem fracWidthWord_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    (UInt64.ofNat fmt.fracWidth).toNat = fmt.fracWidth := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (lt_trans (fracWidth_lt_64 fmt hwidth) (by norm_num))]

private theorem bias_lt_two_pow_62 {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    fmt.bias < 2 ^ 62 := by
  have hfracPos := fmt.fracWidth_pos
  have hexp : fmt.expWidth ≤ 62 := by
    unfold FloatFormat.bitWidth at hwidth
    omega
  exact (FloatFormat.bias_lt_pow_expWidth fmt).trans_le (Nat.pow_le_pow_right (by decide) hexp)

private theorem biasSum_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth).toNat = fmt.bias + 2 * fmt.fracWidth := by
  have hbias := bias_lt_two_pow_62 hwidth
  have hfrac := fracWidth_lt_64 fmt hwidth
  have htwo : (2 : UInt64).toNat = 2 := by decide
  have hdouble : 2 * fmt.fracWidth < 2 ^ 64 := by
    norm_num
    omega
  have hsum : fmt.bias + 2 * fmt.fracWidth < 2 ^ 64 := by
    norm_num at hbias ⊢
    omega
  rw [UInt64.toNat_add, UInt64.toNat_mul, biasWord_toNat hwidth, fracWidthWord_toNat hwidth, htwo,
    Nat.mod_eq_of_lt hdouble, Nat.mod_eq_of_lt hsum]

private theorem tripleBiasSum_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    (3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth).toNat =
      3 * fmt.bias + 2 * fmt.fracWidth := by
  have hbias := bias_lt_two_pow_62 hwidth
  have hfrac := fracWidth_lt_64 fmt hwidth
  have htwo : (2 : UInt64).toNat = 2 := by decide
  have hthree : (3 : UInt64).toNat = 3 := by decide
  have hproduct : 3 * fmt.bias < 2 ^ 64 := by
    norm_num at hbias ⊢
    omega
  have hdouble : 2 * fmt.fracWidth < 2 ^ 64 := by
    norm_num
    omega
  have hsum : 3 * fmt.bias + 2 * fmt.fracWidth < 2 ^ 64 := by
    norm_num at hbias ⊢
    omega
  rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mul, biasWord_toNat hwidth,
    fracWidthWord_toNat hwidth, htwo, hthree, Nat.mod_eq_of_lt hproduct, Nat.mod_eq_of_lt hdouble,
    Nat.mod_eq_of_lt hsum]

/-- Value of the machine-word first normal leading-bit position `bias + 2 * fracWidth - 1`. -/
theorem normalThreshold_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1).toNat =
      fmt.bias + 2 * fmt.fracWidth - 1 := by
  have hsum := biasSum_toNat hwidth
  have hfracPos := fmt.fracWidth_pos
  rw [UInt64.toNat_sub_of_le, hsum, UInt64.toNat_one]
  rw [UInt64.le_iff_toNat_le, hsum, UInt64.toNat_one]
  omega

/-- Value of the machine-word overflow threshold `3 * bias + 2 * fracWidth - 2`. -/
theorem overflowThreshold_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    (3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2).toNat =
      3 * fmt.bias + 2 * fmt.fracWidth - 2 := by
  have hsum := tripleBiasSum_toNat hwidth
  have hfracPos := fmt.fracWidth_pos
  rw [UInt64.toNat_sub_of_le, hsum, show (2 : UInt64).toNat = 2 by decide]
  rw [UInt64.le_iff_toNat_le, hsum, show (2 : UInt64).toNat = 2 by decide]
  omega

/-- Value of the machine-word exponent offset `bias + 2 * fracWidth - 2`. -/
theorem exponentOffset_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2).toNat =
      fmt.bias + 2 * fmt.fracWidth - 2 := by
  have hsum := biasSum_toNat hwidth
  have hfracPos := fmt.fracWidth_pos
  rw [UInt64.toNat_sub_of_le, hsum, show (2 : UInt64).toNat = 2 by decide]
  rw [UInt64.le_iff_toNat_le, hsum, show (2 : UInt64).toNat = 2 by decide]
  omega

/-- A storage word below the radix survives the round trip through the model. -/
theorem toWord_ofWord_of_lt {fmt : FloatFormat} {bits : UInt64}
    (hbits : bits.toNat < 2 ^ fmt.bitWidth) :
    toWord (ofWord (fmt := fmt) bits) = bits := by
  unfold toWord
  rw [toNatBits_ofWord, Nat.mod_eq_of_lt hbits, UInt64.ofNat_toNat]

end Model.NativeSmallWord
end FloatLib.Floats.Formats.BinaryInterchange
