/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Extrema
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# `nextUp` and `nextDown` on encodings

IEEE 754-2019 §5.3.1 `nextUp` and `nextDown` deliver the neighbor of a value in the format. The
reference `Model.nextUp` and `Model.nextDown` step the stored word by one, with the cases of a
NaN (quieted), an infinity at the end of the range, a zero (the least subnormal of the right
sign), and the ends of the range of an encoding without infinities or without a signed zero.

`nextUp fmt a` and `nextDown fmt a` compute the encoding of the result from the word `a` with
the classification codes of `KernelPath.Compare` and one addition modulo `2 ^ bitWidth`.
`nextUp_eq_spec` and `nextDown_eq_spec` prove them equal to the encodings of the reference
operations, for every format descriptor and every value.

`Value.nextUp` and `Value.nextDown` are the operations on stored values, with their
`_eq_lift` theorems and the rules `Value.toNat_nextUp` and `Value.toNat_nextDown`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/-- Encoding of the negative subnormal number of least magnitude: the sign bit and one. -/
def negMinSubnormalWord (fmt : FloatFormat) : Nat :=
  Nat.lor (Nat.pow 2 (Nat.sub fmt.bitWidth 1)) 1

/-- Encoding of the finite value of greatest magnitude with sign `negative`. -/
def maxFiniteWord (fmt : FloatFormat) (negative : Bool) : Nat :=
  (Model.maxFinite fmt negative).toNatBits

/-- The word after `a`, modulo `2 ^ bitWidth`. -/
def wordSucc (fmt : FloatFormat) (a : Nat) : Nat :=
  Nat.mod (Nat.add a 1) (Nat.pow 2 fmt.bitWidth)

/-- The word before `a`, modulo `2 ^ bitWidth`. -/
def wordPred (fmt : FloatFormat) (a : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.sub (Nat.pow 2 fmt.bitWidth) 1) a) (Nat.pow 2 fmt.bitWidth)

/--
Encoding of the least value of the format above the value that `a` encodes (`nextUp_eq_spec`):
a NaN is quieted, `+∞` and the largest finite value of a format without infinities stay, a zero
gives the least positive subnormal, and every other word moves by one.
-/
def nextUp (fmt : FloatFormat) (a : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nanCode fmt a) 1)
    (Bool.casesOn (motive := fun _ => Nat)
      (Bool.casesOn (motive := fun _ => Bool) (Nat.beq (infCode fmt a) 1) false
        (Nat.beq (signCode fmt a) 0))
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (zeroCode fmt a) 1)
        (Bool.casesOn (motive := fun _ => Nat)
          (Bool.casesOn (motive := fun _ => Bool) fmt.supportsSignedZero
            (Nat.beq a (negMinSubnormalWord fmt)) false)
          (Bool.casesOn (motive := fun _ => Nat)
            (Bool.casesOn (motive := fun _ => Bool) fmt.supportsInfinity
              (Nat.beq a (maxFiniteWord fmt false)) false)
            (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (signCode fmt a) 1)
              (wordSucc fmt a) (wordPred fmt a))
            a)
          0)
        1)
      a)
    (Nat.lor a (quietMask fmt))

/--
Encoding of the greatest value of the format below the value that `a` encodes
(`nextDown_eq_spec`): a NaN is quieted, `-∞` and the most negative finite value of a format
without infinities stay, a zero gives the negative subnormal of least magnitude, and every
other word moves by one.
-/
def nextDown (fmt : FloatFormat) (a : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nanCode fmt a) 1)
    (Bool.casesOn (motive := fun _ => Nat)
      (Bool.casesOn (motive := fun _ => Bool) (Nat.beq (infCode fmt a) 1) false
        (Nat.beq (signCode fmt a) 1))
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (zeroCode fmt a) 1)
        (Bool.casesOn (motive := fun _ => Nat)
          (Bool.casesOn (motive := fun _ => Bool) fmt.supportsInfinity
            (Nat.beq a (maxFiniteWord fmt true)) false)
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (signCode fmt a) 1)
            (wordPred fmt a) (wordSucc fmt a))
          a)
        (negMinSubnormalWord fmt))
      a)
    (Nat.lor a (quietMask fmt))

/-- Two values have equal encodings exactly when their stored words are equal. -/
theorem beq_toNatBits {fmt : FloatFormat} (x y : Model fmt) :
    Nat.beq x.toNatBits y.toNatBits = (x.bits == y.bits) := by
  rw [Bool.eq_iff_iff]
  simp only [Nat.beq_eq, beq_iff_eq]
  exact BitVec.toNat_inj

/-- The sign code of an encoding is zero exactly when the sign bit is clear. -/
theorem signCode_beq_zero {fmt : FloatFormat} (x : Model fmt) :
    Nat.beq (signCode fmt x.toNatBits) 0 = !Model.signBit x := by
  unfold signCode
  simp only [Nat.shiftRight_eq', sign_toNatBits]
  cases Model.signBit x <;> rfl

/-- The encoding of the least positive subnormal number is one. -/
theorem toNatBits_posMinSubnormal (fmt : FloatFormat) :
    (Model.posMinSubnormal fmt).toNatBits = 1 :=
  Model.toNatBits_ofNatBits_of_lt 1
    (Nat.one_lt_two_pow (by unfold FloatFormat.bitWidth; omega))

/-- `negMinSubnormalWord` is the encoding of the negative subnormal of least magnitude. -/
theorem negMinSubnormalWord_eq (fmt : FloatFormat) :
    negMinSubnormalWord fmt = (Model.negMinSubnormal fmt).toNatBits := by
  have hone : 1 < 2 ^ fmt.bitWidth :=
    Nat.one_lt_two_pow (by unfold FloatFormat.bitWidth; omega)
  change 2 ^ (fmt.bitWidth - 1) ||| 1 =
    (FloatFormat.signMask fmt ||| FloatFormat.ofWordNat fmt 1).toNat
  rw [BitVec.toNat_or, FloatFormat.signMask_toNat]
  change _ = _ ||| (BitVec.ofNat fmt.bitWidth 1).toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hone]

/-- `wordSucc` is the encoding of the stored word plus one. -/
theorem wordSucc_eq {fmt : FloatFormat} (x : Model fmt) :
    wordSucc fmt x.toNatBits = (Model.ofBits (x.bits + 1)).toNatBits := by
  have hone : 1 < 2 ^ fmt.bitWidth :=
    Nat.one_lt_two_pow (by unfold FloatFormat.bitWidth; omega)
  change (x.bits.toNat + 1) % 2 ^ fmt.bitWidth = (x.bits + 1).toNat
  rw [BitVec.toNat_add]
  change _ = (x.bits.toNat + (BitVec.ofNat fmt.bitWidth 1).toNat) % _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hone]

/-- `wordPred` is the encoding of the stored word minus one. -/
theorem wordPred_eq {fmt : FloatFormat} (x : Model fmt) :
    wordPred fmt x.toNatBits = (Model.ofBits (x.bits - 1)).toNatBits := by
  have hone : 1 < 2 ^ fmt.bitWidth :=
    Nat.one_lt_two_pow (by unfold FloatFormat.bitWidth; omega)
  change (2 ^ fmt.bitWidth - 1 + x.bits.toNat) % 2 ^ fmt.bitWidth = (x.bits - 1).toNat
  rw [BitVec.toNat_sub]
  change _ = (2 ^ fmt.bitWidth - (BitVec.ofNat fmt.bitWidth 1).toNat + x.bits.toNat) % _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hone]

/--
`nextUp` computes the encoding of `Model.nextUp x`, for every format descriptor and every
value.
-/
theorem nextUp_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    nextUp fmt x.toNatBits = (Model.nextUp x).toNatBits := by
  unfold nextUp maxFiniteWord
  rw [nanCode_eq, infCode_eq, zeroCode_eq, signCode_eq, signCode_beq_zero,
    negMinSubnormalWord_eq, beq_toNatBits, beq_toNatBits, wordSucc_eq, wordPred_eq]
  change _ = (Model.Internal.Value.nextUp x).toNatBits
  unfold Model.Internal.Value.nextUp
  cases hnan : Model.isNaN x
  · cases hinf : Model.isInfinite x <;> cases hsign : Model.signBit x <;>
      cases hzero : Model.isZero x <;> cases hsigned : fmt.supportsSignedZero <;>
      cases hinfinity : fmt.supportsInfinity <;>
      cases hmin : (x.bits == (Model.negMinSubnormal fmt).bits) <;>
      cases hmax : (x.bits == (Model.posMaxFinite fmt).bits) <;>
      simp only [Model.posMaxFinite] at hmax <;>
      simp only [hmax, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.and_true,
        Bool.not_true, Bool.not_false, toNatBits_posZero, toNatBits_posMinSubnormal]
  · simp only [↓reduceIte]
    exact (quietNaN_bits x hnan).symm

/--
`nextDown` computes the encoding of `Model.nextDown x`, for every format descriptor and every
value.
-/
theorem nextDown_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    nextDown fmt x.toNatBits = (Model.nextDown x).toNatBits := by
  unfold nextDown maxFiniteWord
  rw [nanCode_eq, infCode_eq, zeroCode_eq, signCode_eq, negMinSubnormalWord_eq, beq_toNatBits,
    wordSucc_eq, wordPred_eq]
  change _ = (Model.Internal.Value.nextDown x).toNatBits
  unfold Model.Internal.Value.nextDown
  cases hnan : Model.isNaN x
  · cases hinf : Model.isInfinite x <;> cases hsign : Model.signBit x <;>
      cases hzero : Model.isZero x <;> cases hinfinity : fmt.supportsInfinity <;>
      cases hmax : (x.bits == (Model.negMaxFinite fmt).bits) <;>
      simp only [Model.negMaxFinite] at hmax <;>
      simp only [hmax, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.and_true,
        Bool.not_true, Bool.not_false]
  · simp only [↓reduceIte]
    exact (quietNaN_bits x hnan).symm

namespace Value

universe u

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/-- Kernel `nextUp` of a stored value. -/
def nextUp (x : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  unary (KernelPath.nextUp format) (fun x => Model.nextUp x) nextUp_eq_spec x

/-- The kernel `nextUp` is the model operation carried through the conversions. -/
theorem nextUp_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    nextUp x = NatView.liftUnary (fun x => Model.nextUp x) x :=
  unary_eq _ _ _ x

/-- The encoding of a `nextUp` is the flat operation on the encoding. -/
@[kernel_optimize] theorem toNat_nextUp (x : FloatLib.Floats.ExecFloat F) :
    toNat (nextUp x) = KernelPath.nextUp format (toNat x) :=
  toNat_unary _ _ _ x

/-- Kernel `nextDown` of a stored value. -/
def nextDown (x : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  unary (KernelPath.nextDown format) (fun x => Model.nextDown x) nextDown_eq_spec x

/-- The kernel `nextDown` is the model operation carried through the conversions. -/
theorem nextDown_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    nextDown x = NatView.liftUnary (fun x => Model.nextDown x) x :=
  unary_eq _ _ _ x

/-- The encoding of a `nextDown` is the flat operation on the encoding. -/
@[kernel_optimize] theorem toNat_nextDown (x : FloatLib.Floats.ExecFloat F) :
    toNat (nextDown x) = KernelPath.nextDown format (toNat x) :=
  toNat_unary _ _ _ x

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
