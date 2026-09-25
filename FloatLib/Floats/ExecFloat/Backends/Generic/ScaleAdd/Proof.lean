/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.ScaleAdd.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.AddDyadic.Proof
public import FloatLib.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Special
import FloatLib.Numerics.ShiftRightJam.Proof

/-!
# Correctness of unsigned-scale exact addition

For conventional IEEE descriptors, `roundSum_eq` identifies unsigned-scale alignment and rounding
with exact dyadic addition followed by `roundDyadic`. The proof includes zero operands and the
signed-zero result of cancellation. The `roundOffset` parameter accommodates both addition scales
and the product scales used by FMA.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteScaleAdd

/-- Unsigned-scale rounding is the corresponding exact dyadic rounding. -/
theorem roundMagnitude_eq
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (roundOffset : Nat) (sign : Bool) (mantissa scale : Nat) :
    roundMagnitude fmt roundOffset sign mantissa scale =
      roundDyadic fmt {
        negative := sign
        significand := mantissa
        exponent := exponent fmt scale roundOffset } := by
  exact FiniteProductRound.round_eq_roundDyadic
    fmt hfmt sign mantissa (scale + roundOffset)

private theorem roundDyadic_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (exp : Int) :
    roundDyadic fmt {
      negative := sign
      significand := 0
      exponent := exp } = zero fmt sign := by
  have hencoding : fmt.encoding = .ieee :=
    ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  cases sign <;>
    simp [roundDyadic, hfmt, ieeeRoundDyadic, zero,
      FloatFormat.supportsSignedZero, hencoding,
      posZero_eq_ofModel_zero, negZero_eq_ofModel_zero]

private theorem exponent_le_iff
    (fmt : FloatFormat) (roundOffset leftScale rightScale : Nat) :
    exponent fmt leftScale roundOffset ≤ exponent fmt rightScale roundOffset ↔
      leftScale ≤ rightScale := by
  unfold exponent
  simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

private theorem exponent_sub_toNat
    (fmt : FloatFormat) (roundOffset leftScale rightScale : Nat)
    (hscale : leftScale ≤ rightScale) :
    Int.toNat
        (exponent fmt rightScale roundOffset -
          exponent fmt leftScale roundOffset) =
      rightScale - leftScale := by
  unfold exponent
  simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

/-- The signed-magnitude helper rounds the exact dyadic magnitude sum. -/
theorem roundMagnitudes_eq
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (roundOffset : Nat) (leftSign rightSign : Bool)
    (left right scale : Nat) :
    roundMagnitudes fmt roundOffset leftSign rightSign left right scale =
      roundDyadic fmt
        (addDyadicMagnitudes leftSign rightSign left right
          (exponent fmt scale roundOffset)) := by
  unfold roundMagnitudes addDyadicMagnitudes
  by_cases hsign : leftSign = rightSign
  · simp [hsign, roundMagnitude_eq fmt hfmt]
  · by_cases heq : left = right
    · simp [hsign, heq, roundDyadic_zero fmt hfmt]
    · by_cases hlt : left < right
      · simp [hsign, heq, hlt, roundMagnitude_eq fmt hfmt]
      · simp [hsign, heq, hlt, roundMagnitude_eq fmt hfmt]

/-- Bounded alignment preserves the result of aligning the complete significands. -/
theorem roundAligned_eq (fmt : FloatFormat) (roundOffset : Nat)
    (highSign lowSign : Bool) (high low gap scale : Nat) :
    roundAligned fmt roundOffset highSign lowSign high low gap scale =
      roundMagnitudes fmt roundOffset highSign lowSign (high <<< gap) low scale := by
  unfold roundAligned
  dsimp only
  split
  · rename_i h
    obtain ⟨hgap, hlowLog, hhigh⟩ := h
    let keep := fmt.fracWidth + 3
    let discard := gap - keep
    have hsplit : keep + discard = gap := by dsimp [keep, discard]; omega
    have hroundWidth : discard + fmt.fracWidth + 2 = gap - 1 := by
      dsimp [discard, keep]
      omega
    have hgapPos : 0 < gap := by omega
    have hpower : 2 ^ gap = 2 ^ (gap - 1) + 2 ^ (gap - 1) := by
      calc
        2 ^ gap = 2 ^ ((gap - 1) + 1) :=
          congrArg (2 ^ ·) (Nat.sub_add_cancel hgapPos).symm
        _ = 2 ^ (gap - 1) + 2 ^ (gap - 1) := by rw [pow_succ]; omega
    have hlow : low < 2 ^ (gap - 1) :=
      Nat.lt_log2_self.trans_le <| Nat.pow_le_pow_right (by decide) (by omega)
    have hhighBound : 2 ^ gap ≤ high * 2 ^ gap := by
      simpa using Nat.mul_le_mul_right (2 ^ gap) (show 1 ≤ high by omega)
    have hlowHigh : low < high * 2 ^ gap := by omega
    have hsumBound : 2 ^ (gap - 1) ≤ high * 2 ^ gap + low := by omega
    have hdiffBound : 2 ^ (gap - 1) ≤ high * 2 ^ gap - low := by omega
    have hleading (magnitude : Nat) (hbound : 2 ^ (gap - 1) ≤ magnitude) :
        discard + fmt.fracWidth + 2 ≤ magnitude.log2 := by
      have hpositive := (Nat.two_pow_pos (gap - 1)).trans_le hbound
      rw [hroundWidth]
      exact (Nat.le_log2 hpositive.ne').2 hbound
    have hshift : high * 2 ^ gap = (high * 2 ^ keep) * 2 ^ discard := by
      rw [← hsplit, pow_add, Nat.mul_assoc]
    have hexact : low = low / 2 ^ discard * 2 ^ discard ↔ low % 2 ^ discard = 0 := by
      have := Nat.div_add_mod' low (2 ^ discard)
      omega
    have hadd := Numerics.shiftRightJam_add_mul_two_pow (high * 2 ^ keep) low discard
    rw [← hshift] at hadd
    have hsub := Numerics.shiftRightJam_mul_two_pow_sub (high * 2 ^ keep) low discard
      (by rw [← hshift]; omega)
    rw [← hshift] at hsub
    have hround (magnitude : Nat) (hbound : 2 ^ (gap - 1) ≤ magnitude) :
        roundMagnitude fmt roundOffset highSign (Numerics.shiftRightJam magnitude discard)
            (scale + discard) =
          roundMagnitude fmt roundOffset highSign magnitude scale := by
      unfold roundMagnitude
      rw [show scale + discard + roundOffset = (scale + roundOffset) + discard by omega]
      exact FiniteProductRound.round_shiftRightJam fmt highSign magnitude
        (scale + roundOffset) discard (hleading magnitude hbound)
    change
      roundMagnitude fmt roundOffset highSign
          (if highSign == lowSign then
            if low == (low >>> discard) <<< discard then
              (high <<< keep) + (low >>> discard)
            else ((high <<< keep) + (low >>> discard)) ||| 1
          else
            if low == (low >>> discard) <<< discard then
              (high <<< keep) - (low >>> discard)
            else ((high <<< keep) - (low >>> discard) - 1) ||| 1)
          (scale + discard) = _
    simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, beq_iff_eq, hexact]
    by_cases hsign : highSign = lowSign
    · simp only [hsign, ite_true]
      rw [← hadd]
      simp only [roundMagnitudes, beq_self_eq_true, ite_true]
      simpa only [hsign] using hround _ hsumBound
    · simp only [hsign, ite_false]
      rw [← hsub]
      simp only [roundMagnitudes, beq_iff_eq, hsign,
        ne_of_gt hlowHigh, not_lt_of_ge hlowHigh.le, ite_false]
      exact hround _ hdiffBound
  · rfl

/-- Exchanging two signed magnitudes preserves their rounded sum, including cancellation. -/
theorem roundMagnitudes_comm (fmt : FloatFormat) (roundOffset : Nat)
    (leftSign rightSign : Bool) (left right scale : Nat) :
    roundMagnitudes fmt roundOffset leftSign rightSign left right scale =
      roundMagnitudes fmt roundOffset rightSign leftSign right left scale := by
  unfold roundMagnitudes
  by_cases hsign : leftSign = rightSign
  · simp [hsign, Nat.add_comm]
  · by_cases heq : left = right
    · simp [hsign, Ne.symm hsign, heq, Bool.and_comm]
    · by_cases hlt : left < right
      · simp [hsign, Ne.symm hsign, heq, Ne.symm heq, hlt, not_lt_of_ge hlt.le]
      · have hgt : right < left := by omega
        simp [hsign, Ne.symm hsign, heq, Ne.symm heq, hlt, hgt]

/-- `roundSum` is exactly dyadic addition followed by one IEEE rounding step. -/
theorem roundSum_eq
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (roundOffset : Nat) (leftSign rightSign : Bool)
    (leftMantissa leftScale rightMantissa rightScale : Nat) :
    roundSum fmt roundOffset leftSign rightSign
        leftMantissa leftScale rightMantissa rightScale =
      roundDyadic fmt
        (addDyadic
          { negative := leftSign
            significand := leftMantissa
            exponent := exponent fmt leftScale roundOffset }
          { negative := rightSign
            significand := rightMantissa
            exponent := exponent fmt rightScale roundOffset }) := by
  rw [← addDyadicImpl_eq]
  unfold roundSum addDyadicImpl
  by_cases hleft : leftMantissa = 0
  · by_cases hright : rightMantissa = 0
    · simp [hleft, hright, roundDyadic_zero fmt hfmt]
    · simp [hleft, hright, roundMagnitude_eq fmt hfmt]
  · by_cases hright : rightMantissa = 0
    · simp [hleft, hright, roundMagnitude_eq fmt hfmt]
    · by_cases hscale : leftScale ≤ rightScale
      · have hexponent :
            exponent fmt leftScale roundOffset ≤
              exponent fmt rightScale roundOffset := by
          exact (exponent_le_iff fmt roundOffset leftScale rightScale).2 hscale
        have hshift :
            Int.toNat
                (exponent fmt rightScale roundOffset -
                  exponent fmt leftScale roundOffset) =
              rightScale - leftScale := by
          exact exponent_sub_toNat fmt roundOffset leftScale rightScale hscale
        simp only [hleft, hright, beq_iff_eq, ite_false, hexponent, ite_true,
          hscale, hshift]
        rw [roundAligned_eq, roundMagnitudes_comm]
        exact roundMagnitudes_eq fmt hfmt roundOffset leftSign rightSign
          leftMantissa (rightMantissa <<< (rightScale - leftScale))
          leftScale
      · have hexponent :
            ¬exponent fmt leftScale roundOffset ≤
              exponent fmt rightScale roundOffset := by
          simpa only [exponent_le_iff] using hscale
        have hrightScale : rightScale ≤ leftScale := by omega
        have hshift :
            Int.toNat
                (exponent fmt leftScale roundOffset -
                  exponent fmt rightScale roundOffset) =
              leftScale - rightScale := by
          exact exponent_sub_toNat fmt roundOffset rightScale leftScale
            hrightScale
        simp only [hleft, hright, beq_iff_eq, ite_false, hscale, hexponent,
          hshift]
        rw [roundAligned_eq]
        exact roundMagnitudes_eq fmt hfmt roundOffset leftSign rightSign
          (leftMantissa <<< (leftScale - rightScale)) rightMantissa
          rightScale

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteScaleAdd
