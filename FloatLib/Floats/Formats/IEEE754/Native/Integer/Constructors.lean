/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.IEEE754.Native.Integer.FromInt
public import FloatLib.Numerics.ShiftRightJam.Proof
import all Init.Data.OfScientific
import all Init.Data.Float.Float
import all Init.Data.Float.Float32

/-!
# Arbitrary integer constructors

Lean 4.33 introduced the logical floating-point models. Lean 4.34 exposes the definitions of
`Float.ofNat`, `Float.ofInt`, and their binary32 counterparts.
The arbitrary-integer casts use these constructors, whose scientific-literal path includes a
small-input optimization. These proofs account for both branches before applying the shared
integer conversion specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics
open Float.Model
open Float.Model.UnpackedFloat

private theorem roundMantissaAtExponentEven_shift (n k : Nat) (e t : Int) :
    roundMantissaAtExponentEven (n <<< k) (e - k) t =
      roundMantissaAtExponentEven n e t := by
  by_cases h : e ≤ t
  · have h' : e - k ≤ t := by omega
    have hs : (t - (e - k)).toNat = (t - e).toNat + k := by omega
    simp [roundMantissaAtExponentEven, h, h', hs, Nat.shiftLeft_eq,
      roundShiftRightEven_mul_two_pow]
  · by_cases h' : e - k ≤ t
    · have hs : (t - (e - k)).toNat ≤ k := by omega
      have hd : k - (t - (e - k)).toNat = (e - t).toNat := by omega
      simp [roundMantissaAtExponentEven, h, h', Nat.shiftLeft_eq,
        roundShiftRightEven_mul_two_pow_of_le _ _ _ hs, hd]
    · have hs : k + (e - k - t).toNat = (e - t).toNat := by omega
      simp only [roundMantissaAtExponentEven, h, h', ite_false, Nat.shiftLeft_eq]
      rw [mul_assoc, ← pow_add, hs]

/-- Moving exact trailing binary zeros into the exponent does not change model rounding. -/
theorem round_shiftLeft (spec : Format) (sign : Sign) (n k : Nat) (e : Int) (hn : n ≠ 0) :
    Float.Model.UnpackedFloat.round spec sign (n <<< k) (e - k) =
      Float.Model.UnpackedFloat.round spec sign n e := by
  have hshift : n <<< k ≠ 0 := by simp [Nat.shiftLeft_eq, hn]
  have htotal : totalExponent (n <<< k) (e - k) = totalExponent n e := by
    simp only [totalExponent, Nat.log2_shiftLeft_of_ne_zero _ _ hn, Nat.cast_add]
    omega
  rw [round_exact_eq_finishRoundedMantissa _ _ _ _ hshift,
    round_exact_eq_finishRoundedMantissa _ _ _ _ hn, htotal,
    roundMantissaAtExponentEven_shift]

private theorem ofNat_eq_round (spec : Format) (n : Nat) (hn : n ≠ 0) :
    Float.Model.UnpackedFloat.ofNat spec n =
      Float.Model.UnpackedFloat.round spec .positive n 0 := by
  have hp : (0 : Int) < (n : Int) := by omega
  simp [Float.Model.UnpackedFloat.ofNat, Float.Model.UnpackedFloat.ofInt,
    Float.Model.UnpackedFloat.normalize,
    Int.compare_eq_gt.mpr hp]

/-- A scientific literal with decimal exponent zero is the shared natural-number constructor. -/
theorem ofScientific_zero_eq_ofNat (spec : Format) (n : Nat) :
    Float.Model.UnpackedFloat.ofScientific spec n 0 =
      Float.Model.UnpackedFloat.ofNat spec n := by
  by_cases hn : n = 0
  · subst n
    simp [Float.Model.UnpackedFloat.ofScientific, Float.Model.UnpackedFloat.ofNat,
      Float.Model.UnpackedFloat.ofInt, Float.Model.UnpackedFloat.normalize]
  have hp : (0 : Int) < 2 ^ spec.exponentBits := Int.pow_pos (by decide)
  have htarget :
      -(spec.mantissaBits : Int) ≤
        spec.targetExponent (totalExponent (n <<< spec.mantissaBits) (-spec.mantissaBits)) := by
    unfold Format.targetExponent totalExponent
    rw [Nat.log2_shiftLeft_of_ne_zero _ _ hn]
    have := le_max_left
      (((n.log2 + spec.mantissaBits : Nat) : Int) + 1 - spec.mantissaBits -
        spec.mantissaBits) spec.minExponent
    push_cast at this ⊢
    omega
  simp only [Float.Model.UnpackedFloat.ofScientific, hn, ↓reduceDIte,
    show ¬(0 : Int) > 2 ^ spec.exponentBits by omega,
    show ¬(0 : Int) < -(2 ^ spec.exponentBits + n.log2) by omega,
    le_refl, ite_true, ite_false, Int.toNat_zero, pow_zero, Float.Model.UnpackedFloat.mul,
    Nat.mul_one, Int.add_zero]
  change roundWithAccuracy spec .positive (n <<< spec.mantissaBits)
    (-spec.mantissaBits) .exact = _
  rw [roundWithAccuracy_exact_eq_round_of_le_targetExponent _ _ _ _ htarget]
  simpa only [zero_sub] using
    (round_shiftLeft spec .positive n spec.mantissaBits 0 hn).trans
      (ofNat_eq_round spec n hn).symm

private theorem round_eq_finite_of_targetExponent
    (spec : Format) (sign : Sign) (n : Nat) (e : Int) (hn : n ≠ 0)
    (he : spec.targetExponent (totalExponent n e) = e) :
    Float.Model.UnpackedFloat.round spec sign n e =
      .finite sign n e (Nat.pos_of_ne_zero hn) := by
  have hshift (em : ExtendedMantissa) : em >>> 0 = em := rfl
  simp [Float.Model.UnpackedFloat.round, decreaseExponent, he, roundWithAccuracy,
    shiftToTargetExponent, shiftToExponent, ExtendedMantissa.ofMantissaAndAccuracy,
    ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
    Accuracy.roundToNearestEven, hshift, hn]

-- The literal fast path multiplies by the normalized representation of one. The hypotheses
-- below give enough exponent range for every integer that fits in the significand.
private theorem mul_one_ofNat_small (spec : Format) (n : Nat)
    (hsmall : n < 2 ^ spec.mantissaBits)
    (hmin : spec.minExponent ≤ -(spec.mantissaBits : Int))
    (hbias : spec.mantissaBits ≤ spec.exponentBias)
    (hmax : spec.exponentBias + spec.mantissaBits < 2 ^ spec.exponentBits) :
    Float.Model.UnpackedFloat.mul spec
        (unpack spec (pack spec (Float.Model.UnpackedFloat.ofNat spec n)))
        (.finite .positive (2 ^ spec.mantissaBitsWithoutImplicit)
          (-(spec.mantissaBitsWithoutImplicit : Int)) (by positivity)) =
      Float.Model.UnpackedFloat.ofNat spec n := by
  by_cases hn : n = 0
  · subst n
    simp [Float.Model.UnpackedFloat.ofNat, Float.Model.UnpackedFloat.ofInt,
      Float.Model.UnpackedFloat.normalize, unpack_pack_zero, Float.Model.UnpackedFloat.mul]
    rfl
  let k := spec.mantissaBits - (n.log2 + 1)
  have hlog : n.log2 < spec.mantissaBits := (Nat.log2_lt hn).2 hsmall
  have hk : k + n.log2 + 1 = spec.mantissaBits := by dsimp [k]; omega
  have hm : n <<< k ≠ 0 := by simp [Nat.shiftLeft_eq, hn]
  have hbits : (n <<< k).log2 + 1 = spec.mantissaBits := by
    rw [Nat.log2_shiftLeft_of_ne_zero _ _ hn]
    omega
  have htarget : spec.targetExponent (totalExponent (n <<< k) (-(k : Int))) = -k := by
    simp only [Format.targetExponent, totalExponent, Nat.log2_shiftLeft_of_ne_zero _ _ hn,
      Nat.cast_add]
    rw [max_eq_left] <;> omega
  have hnat :
      Float.Model.UnpackedFloat.ofNat spec n =
        .finite .positive (n <<< k) (-(k : Int)) (Nat.pos_of_ne_zero hm) := by
    rw [ofNat_eq_round spec n hn, ← round_shiftLeft spec .positive n k 0 hn]
    simpa only [zero_sub] using
      round_eq_finite_of_targetExponent spec .positive (n <<< k) (-k) hm htarget
  have hbiasedPos : 0 < -(k : Int) + spec.exponentBias +
      spec.mantissaBitsWithoutImplicit := by
    have := spec.hm
    simp only [Format.mantissaBits] at hk hbias
    omega
  have hnoOverflow :
      (-(k : Int) + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat + 1 <
        2 ^ spec.exponentBits := by
    have : spec.mantissaBitsWithoutImplicit + 1 = spec.mantissaBits := by
      simp [Format.mantissaBits, Nat.add_comm]
    omega
  rw [hnat, unpack_pack_finite_normal spec .positive (n <<< k) (-k) hm hbits
    hbiasedPos.le hbiasedPos hnoOverflow]
  change roundWithAccuracy spec .positive
    ((n <<< k) * 2 ^ spec.mantissaBitsWithoutImplicit)
    (-k + -(spec.mantissaBitsWithoutImplicit : Int)) .exact = _
  have hmul : (n <<< k) * 2 ^ spec.mantissaBitsWithoutImplicit =
      n <<< (k + spec.mantissaBitsWithoutImplicit) := by
    simp [Nat.shiftLeft_eq, pow_add, Nat.mul_assoc]
  have hexp : -(k : Int) + -(spec.mantissaBitsWithoutImplicit : Int) =
      0 - (k + spec.mantissaBitsWithoutImplicit : Nat) := by push_cast; omega
  rw [hmul, hexp]
  rw [roundWithAccuracy_exact_eq_round_of_le_targetExponent]
  · rw [round_shiftLeft spec .positive n _ 0 hn, ← ofNat_eq_round spec n hn, hnat]
  · unfold Format.targetExponent totalExponent
    rw [Nat.log2_shiftLeft_of_ne_zero _ _ hn]
    have := le_max_left
      ((((n.log2 + (k + spec.mantissaBitsWithoutImplicit) : Nat) : Int) + 1 +
        (0 - ((k + spec.mantissaBitsWithoutImplicit : Nat) : Int))) -
        spec.mantissaBits) spec.minExponent
    simp only [Format.mantissaBits] at hk ⊢
    push_cast at this ⊢
    omega

private theorem unpack_packComponents_neg (spec : Format) (sign : Sign)
    (exponent : BitVec spec.exponentBits)
    (mantissa : BitVec spec.mantissaBitsWithoutImplicit) :
    unpack spec (packComponents spec (-sign) exponent mantissa) =
      Float.Model.UnpackedFloat.neg
        (unpack spec (packComponents spec sign exponent mantissa)) := by
  have hs (s : Sign) : Sign.ofBitVec s.toBitVec = s := by cases s <;> rfl
  simp only [Float.Model.UnpackedFloat.unpack,
    unpackExponent_packComponents, unpackMantissa_packComponents,
    unpackSign_packComponents, hs]
  split_ifs <;> rfl

private theorem unpack_pack_neg (spec : Format) (value : UnpackedFloat) :
    unpack spec (pack spec (Float.Model.UnpackedFloat.neg value)) =
      Float.Model.UnpackedFloat.neg (unpack spec (pack spec value)) := by
  cases value with
  | notANumber => simp [Float.Model.UnpackedFloat.neg]
  | infinity sign => simp [Float.Model.UnpackedFloat.neg]
  | zero sign => simp [Float.Model.UnpackedFloat.neg]
  | finite sign mantissa exponent hm =>
      change unpack spec (pack spec (.finite (-sign) mantissa exponent hm)) = _
      simp only [Float.Model.UnpackedFloat.pack]
      split_ifs <;>
        simp only [packedInfinity, unpack_packComponents_neg]

private theorem pack_neg_unpack_pack (spec : Format) (value : UnpackedFloat) :
    pack spec (Float.Model.UnpackedFloat.neg (unpack spec (pack spec value))) =
      pack spec (Float.Model.UnpackedFloat.neg value) := by
  rw [← unpack_pack_neg, pack_unpack_of_valid _ _ valid_pack]

private theorem neg_round (spec : Format) (sign : Sign) (n : Nat) (e : Int) (hn : n ≠ 0) :
    Float.Model.UnpackedFloat.neg (Float.Model.UnpackedFloat.round spec sign n e) =
      Float.Model.UnpackedFloat.round spec (-sign) n e := by
  rw [round_exact_eq_finishRoundedMantissa _ _ _ _ hn,
    round_exact_eq_finishRoundedMantissa _ _ _ _ hn]
  unfold finishRoundedMantissa
  dsimp only
  split <;> rfl

private theorem neg_ofNat_succ (spec : Format) (n : Nat) :
    Float.Model.UnpackedFloat.neg (Float.Model.UnpackedFloat.ofNat spec (n + 1)) =
      Float.Model.UnpackedFloat.ofInt spec (.negSucc n) := by
  rw [ofNat_eq_round spec (n + 1) (by omega), neg_round _ _ _ _ (by omega)]
  simp [Float.Model.UnpackedFloat.ofInt, Float.Model.UnpackedFloat.normalize,
    Int.compare_eq_lt.mpr]
  rfl

end FloatLib.Floats.Formats.BinaryInterchange.Model

namespace FloatLib.Floats.ExecFloat.Binary

open Formats.BinaryInterchange
open FloatLib.Numerics

/-- The exposed binary64 natural constructor agrees with the shared packed logical constructor. -/
private theorem float_ofNat_eq_ofModel (n : Nat) :
    Float.ofNat n = Float.ofModel (Float.Model.ofNat n) := by
  change Float.ofScientific n false 0 = _
  unfold Float.ofScientific
  by_cases hn : n < 2 ^ 53
  · simp only [hn, Nat.zero_le, and_self, ↓reduceDIte, Bool.false_eq_true, ite_false]
    have hcast : n.toUInt64.toNat = n := by
      simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
    change Float.ofModel (Float.Model.pack
      (Float.Model.UnpackedFloat.mul Float.Model.Format.binary64
        (Float.Model.UnpackedFloat.unpack _ (Float.Model.UnpackedFloat.pack _
          (Float.Model.UnpackedFloat.ofNat _ n.toUInt64.toNat)))
        (Float.Model.UnpackedFloat.unpack _ _))) = _
    rw [hcast]
    have hone : (Float.ofBits 0x3FF0000000000000).toModel.unpack =
        .finite .positive (2 ^ 52) (-52) (by decide) := by rfl
    change Float.ofModel (Float.Model.pack
      (Float.Model.UnpackedFloat.mul Float.Model.Format.binary64
        (Float.Model.UnpackedFloat.unpack _ (Float.Model.UnpackedFloat.pack _
          (Float.Model.UnpackedFloat.ofNat _ n)))
        (Float.ofBits 0x3FF0000000000000).toModel.unpack)) = _
    rw [hone]
    exact congrArg (fun value => Float.ofModel (Float.Model.pack value))
      (Model.mul_one_ofNat_small Float.Model.Format.binary64 n hn
        (by decide) (by decide) (by decide))
  · simp only [hn, false_and, ↓reduceDIte, Bool.false_eq_true, ite_false]
    change Float.ofModel (Float.Model.pack
      (Float.Model.UnpackedFloat.ofScientific Float.Model.Format.binary64 n 0)) = _
    rw [Model.ofScientific_zero_eq_ofNat]
    rfl

private theorem float32_ofNat_eq_ofModel (n : Nat) :
    Float32.ofNat n = Float32.ofModel (Float32.Model.ofNat n) := by
  change Float32.ofScientific n false 0 = _
  unfold Float32.ofScientific
  by_cases hn : n < 2 ^ 23
  · simp only [hn, Nat.zero_le, and_self, ↓reduceDIte, Bool.false_eq_true, ite_false]
    have hcast : n.toUInt64.toNat = n := by
      simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
    change Float32.ofModel (Float32.Model.pack
      (Float.Model.UnpackedFloat.mul Float.Model.Format.binary32
        (Float.Model.UnpackedFloat.unpack _ (Float.Model.UnpackedFloat.pack _
          (Float.Model.UnpackedFloat.ofNat _ n.toUInt64.toNat)))
        (Float.Model.UnpackedFloat.unpack _ _))) = _
    rw [hcast]
    have hone : (Float32.ofBits 0x3F800000).toModel.unpack =
        .finite .positive (2 ^ 23) (-23) (by decide) := by rfl
    change Float32.ofModel (Float32.Model.pack
      (Float.Model.UnpackedFloat.mul Float.Model.Format.binary32
        (Float.Model.UnpackedFloat.unpack _ (Float.Model.UnpackedFloat.pack _
          (Float.Model.UnpackedFloat.ofNat _ n)))
        (Float32.ofBits 0x3F800000).toModel.unpack)) = _
    rw [hone]
    exact congrArg (fun value => Float32.ofModel (Float32.Model.pack value))
      (Model.mul_one_ofNat_small Float.Model.Format.binary32 n
        (by change n < 2 ^ 24; omega) (by decide) (by decide) (by decide))
  · simp only [hn, false_and, ↓reduceDIte, Bool.false_eq_true, ite_false]
    change Float32.ofModel (Float32.Model.pack
      (Float.Model.UnpackedFloat.ofScientific Float.Model.Format.binary32 n 0)) = _
    rw [Model.ofScientific_zero_eq_ofNat]
    rfl

private theorem float_ofInt_eq_ofModel (n : Int) :
    Float.ofInt n = Float.ofModel (Float.Model.ofInt n) := by
  cases n with
  | ofNat n => exact float_ofNat_eq_ofModel n
  | negSucc n =>
      change Float.neg (Float.ofNat (n + 1)) = _
      rw [float_ofNat_eq_ofModel]
      apply congrArg Float.ofModel
      change Float.Model.mk _ _ = Float.Model.mk _ _
      congr 1
      change UInt64.ofBitVec (Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
        (Float.Model.UnpackedFloat.neg (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64
          (Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
            (Float.Model.UnpackedFloat.ofNat Float.Model.Format.binary64 (n + 1)))))) =
        UInt64.ofBitVec (Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
          (Float.Model.UnpackedFloat.ofInt Float.Model.Format.binary64 (.negSucc n)))
      rw [Model.pack_neg_unpack_pack, Model.neg_ofNat_succ]

private theorem float32_ofInt_eq_ofModel (n : Int) :
    Float32.ofInt n = Float32.ofModel (Float32.Model.ofInt n) := by
  cases n with
  | ofNat n => exact float32_ofNat_eq_ofModel n
  | negSucc n =>
      change Float32.neg (Float32.ofNat (n + 1)) = _
      rw [float32_ofNat_eq_ofModel]
      apply congrArg Float32.ofModel
      change Float32.Model.mk _ _ = Float32.Model.mk _ _
      congr 1
      change UInt32.ofBitVec (Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
        (Float.Model.UnpackedFloat.neg (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32
          (Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
            (Float.Model.UnpackedFloat.ofNat Float.Model.Format.binary32 (n + 1)))))) =
        UInt32.ofBitVec (Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
          (Float.Model.UnpackedFloat.ofInt Float.Model.Format.binary32 (.negSucc n)))
      rw [Model.pack_neg_unpack_pack, Model.neg_ofNat_succ]

/-- Binary64 natural construction is nearest-even rounding of a denominator-one rational. -/
theorem toModel_ofFloat_ofNat (n : Nat) :
    toModel (ofFloat (Float.ofNat n)) = Model.roundRat FloatFormat.binary64 false n 1 := by
  rw [float_ofNat_eq_ofModel, toModel_ofFloat]
  change Model.ofModel FloatFormat.binary64
    (Float.Model.UnpackedFloat.ofInt FloatFormat.binary64.toModel (n : Int)) = _
  rw [Model.ofModel_ofInt_eq_roundRat _ (by decide)]
  simp [SignedRat.negative_ofRat, show ¬(n : Rat) < 0 from not_lt.mpr (Nat.cast_nonneg n)]

/-- Binary32 natural construction is nearest-even rounding of a denominator-one rational. -/
theorem toModel_ofFloat32_ofNat (n : Nat) :
    toModel (ofFloat32 (Float32.ofNat n)) = Model.roundRat FloatFormat.binary32 false n 1 := by
  rw [float32_ofNat_eq_ofModel, toModel_ofFloat32]
  change Model.ofModel FloatFormat.binary32
    (Float.Model.UnpackedFloat.ofInt FloatFormat.binary32.toModel (n : Int)) = _
  rw [Model.ofModel_ofInt_eq_roundRat _ (by decide)]
  simp [SignedRat.negative_ofRat, show ¬(n : Rat) < 0 from not_lt.mpr (Nat.cast_nonneg n)]

/-- Binary64 integer construction uses the shared dyadic rounder, including signed overflow. -/
theorem toModel_ofFloat_ofInt (n : Int) :
    toModel (ofFloat (Float.ofInt n)) =
      Model.roundDyadic FloatFormat.binary64 (Dyadic.ofScaledInt n 0) := by
  rw [float_ofInt_eq_ofModel, toModel_ofFloat]
  exact Model.ofModel_ofInt_eq_roundDyadic FloatFormat.binary64 (by decide) n

/-- Binary32 integer construction uses the shared dyadic rounder, including signed overflow. -/
theorem toModel_ofFloat32_ofInt (n : Int) :
    toModel (ofFloat32 (Float32.ofInt n)) =
      Model.roundDyadic FloatFormat.binary32 (Dyadic.ofScaledInt n 0) := by
  rw [float32_ofInt_eq_ofModel, toModel_ofFloat32]
  exact Model.ofModel_ofInt_eq_roundDyadic FloatFormat.binary32 (by decide) n

/-- The arbitrary-precision integer cast to binary64 has the same rounding specification. -/
theorem toModel_ofFloat_intToFloat (n : Int) :
    toModel (ofFloat n.toFloat) =
      Model.roundDyadic FloatFormat.binary64 (Dyadic.ofScaledInt n 0) :=
  toModel_ofFloat_ofInt n

/-- The arbitrary-precision integer cast to binary32 has the same rounding specification. -/
theorem toModel_ofFloat32_intToFloat32 (n : Int) :
    toModel (ofFloat32 n.toFloat32) =
      Model.roundDyadic FloatFormat.binary32 (Dyadic.ofScaledInt n 0) :=
  toModel_ofFloat32_ofInt n

end FloatLib.Floats.ExecFloat.Binary
