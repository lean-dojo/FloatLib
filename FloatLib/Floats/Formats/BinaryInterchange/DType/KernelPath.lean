/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.DType.Cast
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Exact
public import FloatLib.Numerics.Representations.FixedInt.Semantics.Basic

/-!
# Kernel rules for the integer conversions of the descriptor model

IEEE 754-2019 §5.4.1 names the conversions between a floating-point format and an integer
format: `convertFromInt`, the five `convertToInteger…` and the five `convertToIntegerExact…`.
`ExecDType` defines them between the descriptor model and a fixed-width signed integer, with a
checked result. This module gives them their kernel forms on encodings:

* `KernelPath.convertToIntegerExact fmt width mode a` is `ExecDType.convertToIntegerExact` on
  the word `a`: the integer is `KernelPath.intMagnitude` of the word with its sign bit, and the
  range test is one comparison of natural numbers (`convertToIntegerExact_eq_spec`,
  `inRangeCode_eq`). `Configured.convertToIntegerExact_eq` rewrites
  the conversion of a decoded configured value with it, in every storage plan, and
  `ExecDType.convertToInteger` and the ten members under the names of the standard are
  unfolded to it.
* `Value.ofInteger mode z` is the stored value of the integer `z` rounded once in the direction
  `mode`, with the rule `Value.toNat_ofInteger`: its encoding is `KernelPath.roundInteger` of
  the sign and the magnitude of `z`. `Configured.convertFromInt_eq` rewrites
  `ExecDType.convertFromInt`, stored in a configured format, with it.
* `toInt_ofInt_eq` reads back a fixed-width integer that was built from an integer, as one
  balanced remainder.

Every statement holds for every format descriptor, integer width and rounding direction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics
open FloatLib.Numerics.Representations

/--
One when the integer of sign `negative` and magnitude `magnitude` fits `width` signed bits
(`inRangeCode_eq`): the magnitude is at most `2 ^ (width - 1) - 1`, or `2 ^ (width - 1)` for a
negative integer of a positive width.
-/
def inRangeCode (width : Nat) (negative : Bool) (magnitude : Nat) : Bool :=
  (fun half =>
    Nat.ble magnitude
      (Bool.casesOn (motive := fun _ => Nat) negative (Nat.sub half 1)
        (Nat.sub half (Nat.sub 1 width))))
    (Nat.pow 2 (Nat.sub width 1))

/--
`ExecDType.convertToIntegerExact` on the word `a` (`convertToIntegerExact_eq_spec`): a finite
word is rounded to an integer in the direction `mode`, which is delivered when it fits `width`
signed bits, with `inexact` when the value was not integral; an infinity and a NaN fail with
their classification. The integer is `intMagnitude` of the word with its sign bit.
-/
def convertToIntegerExact (fmt : FloatFormat) (width : Nat) (mode : Model.IEEERoundingMode)
    (a : Nat) : FloatLib.Floats.ExecFloat.ConversionOutcome (FixedInt width) :=
  Bool.casesOn (motive := fun _ => FloatLib.Floats.ExecFloat.ConversionOutcome (FixedInt width))
    (Nat.beq (finiteCode fmt a) 1)
    (Bool.casesOn
      (motive := fun _ => FloatLib.Floats.ExecFloat.ConversionOutcome (FixedInt width))
      (Nat.beq (infCode fmt a) 1)
      (.failure (.exceptional .source
        (.nan (some (Model.payloadOfNaNField (Nat.beq (signalingCode fmt a) 1) (fracCode fmt a)
          fmt.encoding)) (Nat.beq (signCode fmt a) 1) (Nat.beq (signalingCode fmt a) 1))))
      (.failure (.infinity .source (Nat.beq (signCode fmt a) 1))))
    ((fun negative magnitude =>
        Bool.casesOn
          (motive := fun _ => FloatLib.Floats.ExecFloat.ConversionOutcome (FixedInt width))
          (inRangeCode width negative magnitude)
          (.failure .outOfRange)
          (.success (FixedInt.ofInt (signedInt negative magnitude))
            { inexact := !Model.dyadicIsIntegral (decode fmt a) }))
      (Nat.beq (signCode fmt a) 1) (intMagnitude fmt mode a))

/-- `inRangeCode` decides the signed range of `width` bits. -/
theorem inRangeCode_eq (width : Nat) (negative : Bool) (magnitude : Nat) :
    inRangeCode width negative magnitude =
      decide (FixedInt.InRange width (signedInt negative magnitude)) := by
  have hpos : 0 < 2 ^ (width - 1) := Nat.two_pow_pos _
  have hcast : ((2 ^ (width - 1) : Nat) : Int) = (2 : Int) ^ (width - 1) := by push_cast; rfl
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  unfold inRangeCode FixedInt.InRange
  rw [FixedInt.maxValue_eq, signedInt_eq, ← hcast]
  simp only [Nat.pow_eq, Nat.sub_eq, Nat.ble_eq]
  rcases Nat.eq_zero_or_pos width with rfl | hwidth
  · have hmin : FixedInt.minValue 0 = 0 := rfl
    have hone : 2 ^ (0 - 1) = 1 := rfl
    rw [hmin]
    cases negative <;>
      simp only [hone, Bool.false_eq_true, ite_false, ite_true, Int.ofNat_eq_natCast] <;> omega
  · rw [FixedInt.minValue_eq hwidth, ← hcast]
    cases negative <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, Int.ofNat_eq_natCast] <;> omega

/--
`convertToIntegerExact` computes `ExecDType.convertToIntegerExact x mode` on the encoding of
`x`, for every format descriptor, integer width, rounding direction and value.
-/
theorem convertToIntegerExact_eq_spec {fmt : FloatFormat} {width : Nat}
    (mode : Model.IEEERoundingMode) (x : Model fmt) :
    convertToIntegerExact fmt width mode x.toNatBits =
      ExecDType.convertToIntegerExact x mode := by
  unfold convertToIntegerExact ExecDType.convertToIntegerExact Model.exactValue
  simp only [finiteCode_eq, infCode_eq, signCode_eq, signalingCode_eq, fracCode_eq,
    inRangeCode_eq]
  cases hfinite : Model.isFinite x
  · rw [toDyadic?_eq_none_of_isFinite_eq_false x hfinite]
    cases Model.isInfinite x <;> rfl
  · have hd := toDyadic?_eq_decode x hfinite
    rw [hd, ← intMagnitude_eq mode x _ hd]
    dsimp only
    by_cases hrange : FixedInt.InRange width (Model.roundDyadicToInt mode (decode fmt x.toNatBits))
    · rw [decide_eq_true hrange, ite_eq_left hrange]
    · rw [decide_eq_false hrange, ite_eq_right hrange]

/-- Whether an integer is negative, by its constructor. -/
def isNegative (z : Int) : Bool :=
  Int.casesOn (motive := fun _ => Bool) z (fun _ => false) (fun _ => true)

/-- `isNegative` decides `z < 0`. -/
theorem isNegative_eq (z : Int) : isNegative z = decide (z < 0) := by
  cases z with
  | ofNat n => exact (decide_eq_false (Int.not_lt.mpr (Int.natCast_nonneg n))).symm
  | negSucc n => exact (decide_eq_true (Int.negSucc_lt_zero n)).symm

namespace Value

universe u

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/--
The stored value of the integer `z` rounded once in the direction `mode`: the reference
rounding of the dyadic `± |z| * 2 ^ 0` (`ofInteger_eq_lift`).
-/
def ofInteger (mode : Model.IEEERoundingMode) (z : Int) : FloatLib.Floats.ExecFloat F :=
  nullary (roundInteger format mode (isNegative z) z.natAbs)
    (Model.Internal.Directed.roundDyadic format mode ⟨isNegative z, z.natAbs, 0⟩)
    (roundInteger_eq format mode _ _)

/-- The kernel rounding of an integer is the reference rounding carried through the packing. -/
theorem ofInteger_eq_lift (mode : Model.IEEERoundingMode) (z : Int) :
    ofInteger (F := F) mode z =
      FloatLib.Floats.ExecFloat.ofRaw (view.ofModel
        (Model.Internal.Directed.roundDyadic format mode ⟨isNegative z, z.natAbs, 0⟩)) :=
  nullary_eq _ _ _

/-- The encoding of a rounded integer is `roundInteger` of its sign and magnitude. -/
@[kernel_optimize] theorem toNat_ofInteger (mode : Model.IEEERoundingMode) (z : Int) :
    toNat (ofInteger (F := F) mode z) = roundInteger format mode (isNegative z) z.natAbs :=
  toNat_nullary _ _ _

end Value

/--
A fixed-width integer built from an integer reads back as the balanced remainder modulo
`2 ^ width`.
-/
@[kernel_optimize] theorem toInt_ofInt_eq (width : Nat) (z : Int) :
    FixedInt.toInt (FixedInt.ofInt (width := width) z) = Int.bmod z (2 ^ width) :=
  BitVec.toInt_ofInt z

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Floats.ExecFloat.KernelPath
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath
open FloatLib.Numerics.Representations

variable {format : FloatFormat}

/--
The checked integer conversion of a configured value, as the descriptor model defines it, is
the kernel conversion on its encoding, for every integer width and rounding direction.
-/
@[kernel_optimize] theorem convertToIntegerExact_eq {width : Nat} {plan : StoragePlan format}
    (mode : Model.IEEERoundingMode)
    (x : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    ExecDType.convertToIntegerExact (width := width)
        (FloatLib.Floats.ExecFloat.Binary.toModel x) mode =
      KernelPath.convertToIntegerExact format width mode (toNat x) := by
  rw [KernelPath.toNat_eq, ← toModel_eq_natView, KernelPath.convertToIntegerExact_eq_spec]

/--
The conversion of a fixed-width integer into a configured format, rounded once in the
direction `mode`, is the kernel rounding of the integer.
-/
@[kernel_optimize] theorem convertFromInt_eq {width : Nat} {plan : StoragePlan format}
    (mode : Model.IEEERoundingMode) (x : FixedInt width) :
    (FloatLib.Floats.ExecFloat.Binary.ofModel (ExecDType.convertFromInt format x mode) :
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) =
      KernelPath.Value.ofInteger mode (FixedInt.toInt x) := by
  rw [KernelPath.Value.ofInteger_eq_lift, ofModel_eq_natView, isNegative_eq]
  rfl

end FloatLib.Floats.Formats.BinaryInterchange.Configured

/-
The conversion without the inexact signal is the checked conversion with that flag cleared, and
the members under the names of the standard are the two conversions at one direction:
`float_decide` unfolds them, and the rule of the checked conversion applies.
-/
attribute [kernel_optimize unfold]
  FloatLib.Floats.Formats.BinaryInterchange.ExecDType.convertToInteger

ieee_tag_members [kernel_optimize unfold]
  FloatLib.Floats.Formats.BinaryInterchange.ExecDType.convertToInteger by direction

ieee_tag_members [kernel_optimize unfold]
  FloatLib.Floats.Formats.BinaryInterchange.ExecDType.convertToIntegerExact by direction
