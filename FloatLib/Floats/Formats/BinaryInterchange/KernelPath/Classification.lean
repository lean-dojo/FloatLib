/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Predicates
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Classification.Runtime

/-!
# The class of an encoding

IEEE 754-2019 §5.7.2 classifies a value without an exception: `class` gives one of ten classes,
and `isNormal` and `isSubnormal` test two of them. On a natural-number encoding these read the
exponent field and the fraction field next to the codes of `KernelPath.Compare`:

* `expCode fmt a` and `fracCode fmt a` are the biased exponent field and the fraction field of
  the word `a` (`expCode_eq`, `fracCode_eq`);
* `normalCode_eq` and `subnormalCode_eq` state `Model.isNormal` and `Model.isSubnormal` as tests
  on these fields;
* `classOf fmt a` is the class of the word `a`, and `classOf_eq` proves it equal to
  `Model.classify`.

Every theorem holds for every format descriptor and every word.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/-- The biased exponent field of the word `a` (`expCode_eq`). -/
def expCode (fmt : FloatFormat) (a : Nat) : Nat :=
  Nat.shiftRight (Nat.land a (magnitudeMask fmt)) fmt.fracWidth

/-- The fraction field of the word `a` (`fracCode_eq`). -/
def fracCode (fmt : FloatFormat) (a : Nat) : Nat :=
  Nat.land a (Nat.sub (Nat.pow 2 fmt.fracWidth) 1)

/--
The class of the word `a` (`classOf_eq`): a NaN by its signaling state, and an infinity, a zero,
a subnormal or a normal number by its sign.
-/
def classOf (fmt : FloatFormat) (a : Nat) : IEEEClass :=
  (fun negative =>
    Bool.casesOn (motive := fun _ => IEEEClass) (Nat.beq (nanCode fmt a) 1)
      (Bool.casesOn (motive := fun _ => IEEEClass) (Nat.beq (infCode fmt a) 1)
        (Bool.casesOn (motive := fun _ => IEEEClass) (Nat.beq (zeroCode fmt a) 1)
          (Bool.casesOn (motive := fun _ => IEEEClass)
            (Nat.beq (expCode fmt a) 0 && !Nat.beq (fracCode fmt a) 0)
            (Bool.casesOn (motive := fun _ => IEEEClass) negative .positiveNormal
              .negativeNormal)
            (Bool.casesOn (motive := fun _ => IEEEClass) negative .positiveSubnormal
              .negativeSubnormal))
          (Bool.casesOn (motive := fun _ => IEEEClass) negative .positiveZero .negativeZero))
        (Bool.casesOn (motive := fun _ => IEEEClass) negative .positiveInfinity
          .negativeInfinity))
      (Bool.casesOn (motive := fun _ => IEEEClass) (Nat.beq (signalingCode fmt a) 1) .quietNaN
        .signalingNaN))
    (Nat.beq (signCode fmt a) 1)

/-- `expCode` is the biased exponent field. -/
theorem expCode_eq {fmt : FloatFormat} (x : Model fmt) :
    expCode fmt x.toNatBits = Model.expField x := by
  change (x.toNatBits &&& magnitudeMask fmt) >>> fmt.fracWidth = _
  rw [magnitude_toNatBits]
  exact fields_shiftRight _ _ _ (Model.fracField_lt_pow2 x)

/-- `fracCode` is the fraction field. -/
theorem fracCode_eq {fmt : FloatFormat} (x : Model fmt) :
    fracCode fmt x.toNatBits = Model.fracField x := by
  have hsign : (if Model.signBit x then 2 ^ signPos fmt else 0) =
      (if Model.signBit x then 2 ^ fmt.expWidth else 0) * 2 ^ fmt.fracWidth := by
    unfold signPos
    cases Model.signBit x <;> simp [Nat.pow_add]
  change x.toNatBits &&& (2 ^ fmt.fracWidth - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, toNatBits_eq_fields, hsign, ← Nat.add_assoc, ← Nat.add_mul,
    Nat.mul_add_mod', Nat.mod_eq_of_lt (Model.fracField_lt_pow2 x)]

/-- A test of a natural number against zero is its Boolean equality with zero. -/
theorem beq_zero_eq (n : Nat) : Nat.beq n 0 = (n == 0) := by
  cases n <;> rfl

/-- `Model.isNormal` on an encoding: the word is finite and its exponent field is not zero. -/
theorem normalCode_eq {fmt : FloatFormat} (x : Model fmt) :
    (Nat.beq (finiteCode fmt x.toNatBits) 1 && !Nat.beq (expCode fmt x.toNatBits) 0) =
      Model.isNormal x := by
  rw [finiteCode_eq, expCode_eq, beq_zero_eq]
  rfl

/--
`Model.isSubnormal` on an encoding: the exponent field is zero and the fraction field is not.
-/
theorem subnormalCode_eq {fmt : FloatFormat} (x : Model fmt) :
    (Nat.beq (expCode fmt x.toNatBits) 0 && !Nat.beq (fracCode fmt x.toNatBits) 0) =
      Model.isSubnormal x := by
  rw [expCode_eq, fracCode_eq, beq_zero_eq, beq_zero_eq]
  rfl

/-- `classOf` is `Model.classify`, for every format descriptor and every word. -/
theorem classOf_eq {fmt : FloatFormat} (x : Model fmt) :
    classOf fmt x.toNatBits = Model.classify x := by
  unfold classOf Model.classify
  simp only [nanCode_eq, infCode_eq, zeroCode_eq, signCode_eq, signalingCode_eq,
    subnormalCode_eq]
  cases Model.isNaN x <;> cases Model.isSignaling x <;> cases Model.isInfinite x <;>
    cases Model.signBit x <;> cases Model.isZero x <;> cases Model.isSubnormal x <;> rfl

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
