/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Scale

/-!
# `logB` on encodings

IEEE 754-2019 §5.3.3 `logB` delivers the exponent of the leading bit of a value. `Model.logB`
decodes the operand to its exact dyadic value, adds the position of the leading bit of the
significand to the exponent, and rounds that integer into the format to nearest-even.

`logB fmt a` computes the encoding of the result from the word `a`: the bit length of the
significand and the exponent field give the exponent as a difference of two natural numbers,
whose magnitude `KernelPath.roundInteger` rounds. A zero and an infinity give the overflow
words of the format, and a NaN is quieted. `logB_eq_spec` proves it equal to the encoding of
`Model.logB` for every format descriptor and value.

`Value.logB` is the operation on stored values, with `Value.logB_eq_lift` and the rule
`Value.toNat_logB`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
Encoding of the exponent of the leading bit of the value that `a` encodes, rounded to
nearest-even (`logB_eq_spec`).
-/
def logB (fmt : FloatFormat) (a : Nat) : Nat :=
  (fun sa ua =>
    Bool.casesOn (motive := fun _ => Nat)
      (Nat.beq
        (Nat.add (Nat.sub ua (maxFinite fmt)) (Nat.mul (negZeroNaN fmt) (Nat.sub sa ua))) 0)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nanCode fmt a) 1)
        (overflowWord fmt false) (Nat.lor a (quietMask fmt)))
      ((fun ha =>
          (fun significand =>
            Bool.casesOn (motive := fun _ => Nat) (Nat.beq significand 0)
              ((fun position offset =>
                  Bool.casesOn (motive := fun _ => Nat) (Nat.ble offset position)
                    (roundInteger fmt .nearest true (Nat.sub offset position))
                    (roundInteger fmt .nearest false (Nat.sub position offset)))
                (Nat.add (Nat.sub (significandLength fmt.fracWidth significand) 1) ha)
                (Nat.sub (Nat.add fmt.exponentBias fmt.fracWidth) 1))
              (overflowWord fmt true))
            (Nat.sub ua (Nat.shiftLeft ha fmt.fracWidth)))
        (Nat.sub (Nat.shiftRight ua fmt.fracWidth) 1)))
    (Nat.shiftRight a (signPos fmt)) (Nat.land a (magnitudeMask fmt))

/--
`logB` computes the encoding of `Model.logB x`, for every format descriptor and every value.
-/
theorem logB_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    logB fmt x.toNatBits = (Model.logB x).toNatBits := by
  have hfx := Model.fracField_lt_pow2 x
  have hfrac := fmt.fracWidth_pos
  unfold logB
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, sign_toNatBits, magnitude_toNatBits, fields_shiftRight _ _ _ hfx,
    fields_sub_shiftLeft]
  by_cases hguard :
      Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x - maxFinite fmt +
        negZeroNaN fmt * ((if Model.signBit x then 1 else 0) -
          (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x)) = 0
  · have hfinite := isFinite_of_nonFinite_eq_zero x hguard
    obtain ⟨d, hd, _, hs, he⟩ := toDyadic?_of_isFinite x hfinite
    have hexact := Model.exactValue_eq_finite_of_toDyadic?_eq_some hd
    rw [hguard, ← hs]
    by_cases hzero : d.significand = 0
    · have hspec : Model.logB x = Model.nativeOverflow fmt true := by
        rw [← Model.value_logB, Model.logB_status_of_zero x d hexact hzero]
      rw [hspec, hzero]
      simp only [overflowWord_eq]
      rfl
    · have hbeq : Nat.beq d.significand 0 = false := by
        rw [← Bool.not_eq_true, Nat.beq_eq]
        exact hzero
      have hlt : d.significand < 2 ^ (fmt.fracWidth + 1) := by
        rw [hs]
        exact decoded_significand_lt x
      have hspec : Model.logB x = Model.Internal.Directed.roundDyadic fmt .nearest
          (Numerics.Dyadic.ofScaledInt (Int.ofNat d.significand.log2 + d.exponent) 0) := by
        rw [← Model.value_logB, Model.logB_status_of_finite_nonzero x d hexact hzero]
        rfl
      rw [hbeq, hspec, significandLength_eq hlt, ite_eq_right hzero, he hzero]
      change Bool.rec (motive := fun _ => Nat) _ _ _ = _
      generalize hp : d.significand.log2 + 1 - 1 + (Model.expField x - 1) = position
      generalize hm : fmt.exponentBias + fmt.fracWidth - 1 = offset
      have hexponent : Int.ofNat d.significand.log2 +
          (((Model.expField x - 1 : Nat) : Int) + fmt.minSubnormalExponent) =
            (position : Int) - (offset : Int) := by
        simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
          Int.ofNat_eq_natCast]
        omega
      rw [hexponent]
      by_cases hle : offset ≤ position
      · rw [Nat.ble_eq_true_of_le hle]
        change roundInteger fmt .nearest false (position - offset) = _
        rw [roundInteger_eq]
        change _ = (Model.Internal.Directed.roundDyadic fmt .nearest
          ⟨decide ((position : Int) - (offset : Int) < 0),
            ((position : Int) - (offset : Int)).natAbs, 0⟩).toNatBits
        rw [decide_eq_false (by omega),
          show ((position : Int) - (offset : Int)).natAbs = position - offset from by omega]
      · rw [show Nat.ble offset position = false from by
          rw [← Bool.not_eq_true, Nat.ble_eq]
          exact hle]
        change roundInteger fmt .nearest true (offset - position) = _
        rw [roundInteger_eq]
        change _ = (Model.Internal.Directed.roundDyadic fmt .nearest
          ⟨decide ((position : Int) - (offset : Int) < 0),
            ((position : Int) - (offset : Int)).natAbs, 0⟩).toNatBits
        rw [decide_eq_true (by omega),
          show ((position : Int) - (offset : Int)).natAbs = offset - position from by omega]
  · obtain ⟨hnone, hinf⟩ := not_finite_cases x (isFinite_eq_false_of_nonFinite_ne_zero x hguard)
    rw [beq_zero_eq_false hguard, nanCode_eq]
    cases hnan : Model.isNaN x
    · rw [hnan] at hinf
      have hspec : Model.logB x = Model.nativeOverflow fmt false := by
        rw [← Model.value_logB, Model.logB_status_of_infinity x (Model.signBit x)
          (by simp [Model.exactValue, hnone, hinf])]
      rw [hspec]
      simp only [overflowWord_eq]
    · rw [hnan] at hinf
      have hspec : Model.logB x = Model.quietNaN x := by
        rw [← Model.value_logB, Model.logB_status_of_nan x (Model.signBit x)
          (Model.isSignaling x) (Model.fracField x) (by simp [Model.exactValue, hnone, hinf])]
      rw [hspec, quietNaN_bits x hnan]
      rfl

namespace Value

universe u

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/-- Kernel `logB` of a stored value: the exponent of its leading bit, in its own format. -/
def logB (x : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  unary (KernelPath.logB format) (fun x => Model.logB x) logB_eq_spec x

/-- The kernel `logB` is the model operation carried through the conversions. -/
theorem logB_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    logB x = NatView.liftUnary (fun x => Model.logB x) x :=
  unary_eq _ _ _ x

/-- The encoding of a `logB` is the flat operation on the encoding. -/
@[kernel_optimize] theorem toNat_logB (x : FloatLib.Floats.ExecFloat F) :
    toNat (logB x) = KernelPath.logB format (toNat x) :=
  toNat_unary _ _ _ x

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
