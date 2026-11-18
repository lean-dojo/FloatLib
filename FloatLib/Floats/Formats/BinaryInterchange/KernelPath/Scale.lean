/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Cast
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Compare
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Lift
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.Exponent

/-!
# `scaleB` on encodings

IEEE 754-2019 §5.3.3 `scaleB` multiplies a value by a power of two and rounds once.
`Model.scale` decodes the operand to its exact dyadic value, adds `n` to the exponent and rounds
with `Model.Internal.Directed.roundDyadic`.

`scale fmt mode n a` computes the encoding of the result from the word `a`: the significand with
its implicit bit and the exponent field are read off the word, as `KernelPath.cast` reads them,
`n` moves the exponent, and `KernelPath.round` rounds in the direction `mode`. An infinity is
returned as it is and a NaN is quieted. `scale_eq_spec` proves it equal to the encoding of
`Model.scale` for every format descriptor, rounding direction, integer `n` and value.

`Value.scale` is the operation on stored values, with `Value.scale_eq_lift` and the rule
`Value.toNat_scale`. `roundInteger` rounds an integer into a format on encodings
(`roundInteger_eq`), which `KernelPath.logB` uses.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
Encoding of the value that `a` encodes times `2 ^ n`, rounded in the direction `mode`
(`scale_eq_spec`).
-/
def scale (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (n : Int) (a : Nat) : Nat :=
  (fun sa ua =>
    Bool.casesOn (motive := fun _ => Nat)
      (Nat.beq
        (Nat.add (Nat.sub ua (maxFinite fmt)) (Nat.mul (negZeroNaN fmt) (Nat.sub sa ua))) 0)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nanCode fmt a) 1) a
        (Nat.lor a (quietMask fmt)))
      ((fun ha =>
          (fun significand =>
            Int.casesOn (motive := fun _ => Nat) n
              (fun k =>
                round fmt mode (Nat.succ fmt.fracWidth) sa sa significand (Nat.add ha k) 0 0 0)
              (fun k =>
                round fmt mode (Nat.succ fmt.fracWidth) sa sa significand ha (Nat.succ k) 0 0))
            (Nat.sub ua (Nat.shiftLeft ha fmt.fracWidth)))
        (Nat.sub (Nat.shiftRight ua fmt.fracWidth) 1)))
    (Nat.shiftRight a (signPos fmt)) (Nat.land a (magnitudeMask fmt))

/-- A word whose finiteness test is not zero encodes a value that is not finite. -/
theorem isFinite_eq_false_of_nonFinite_ne_zero {fmt : FloatFormat} (x : Model fmt)
    (hflag : nonFinite fmt (if Model.signBit x then 1 else 0)
      (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) ≠ 0) :
    Model.isFinite x = false := by
  cases hfinite : Model.isFinite x
  · rfl
  · exact absurd (nonFinite_eq_zero_of_isFinite x hfinite) hflag

/--
A value that is not finite has no exact dyadic value, and it is an infinity exactly when it is
not a NaN.
-/
theorem not_finite_cases {fmt : FloatFormat} (x : Model fmt)
    (hfinite : Model.isFinite x = false) :
    Model.toDyadic? x = none ∧ Model.isInfinite x = !Model.isNaN x := by
  refine ⟨Model.toDyadic?_eq_none_of_isFinite_eq_false hfinite, ?_⟩
  have hclass := isNaN_eq_not_isFinite_and_not_isInfinite x
  rw [hfinite] at hclass
  cases hnan : Model.isNaN x <;> cases hinf : Model.isInfinite x <;> simp_all

/-- The kernel test of a nonzero natural number against zero is `false`. -/
theorem beq_zero_eq_false {m : Nat} (hm : m ≠ 0) : Nat.beq m 0 = false := by
  rw [← Bool.not_eq_true, Nat.beq_eq]
  exact hm

/--
`scale` computes the encoding of `Model.scale x n mode`, for every format descriptor, every
rounding direction, every integer `n` and every value.
-/
theorem scale_eq_spec {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (n : Int)
    (x : Model fmt) :
    scale fmt mode n x.toNatBits = (Model.scale x n mode).toNatBits := by
  have hfx := Model.fracField_lt_pow2 x
  unfold scale
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.succ_eq_add_one, sign_toNatBits, magnitude_toNatBits,
    fields_shiftRight _ _ _ hfx, fields_sub_shiftLeft]
  by_cases hguard :
      Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x - maxFinite fmt +
        negZeroNaN fmt * ((if Model.signBit x then 1 else 0) -
          (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x)) = 0
  · have hfinite := isFinite_of_nonFinite_eq_zero x hguard
    obtain ⟨d, hd, hn, hs, he⟩ := toDyadic?_of_isFinite x hfinite
    have hspec : Model.scale x n mode =
        Model.Internal.Directed.roundDyadic fmt mode { d with exponent := d.exponent + n } := by
      rw [← Model.value_scale, Model.scale_status_of_finite x n mode d
        (Model.exactValue_eq_finite_of_toDyadic?_eq_some hd)]
    rw [hguard, hspec]
    rcases n with k | k
    · change round fmt mode _ _ _ _ _ _ 0 0 = _
      refine round_eq fmt mode (fmt.fracWidth + 1) _ _ _ _ _ _ _ (decoded_significand_lt x) hs
        (by rw [hn]; rfl) ?_ (fun _ => rfl)
      intro hne
      change d.exponent + Int.ofNat k = _
      rw [he (by rw [hs]; exact hne)]
      simp only [Int.ofNat_eq_natCast]
      push_cast
      omega
    · change round fmt mode _ _ _ _ _ _ 0 0 = _
      refine round_eq fmt mode (fmt.fracWidth + 1) _ _ _ _ _ _ _ (decoded_significand_lt x) hs
        (by rw [hn]; rfl) ?_ (fun _ => rfl)
      intro hne
      change d.exponent + Int.negSucc k = _
      rw [he (by rw [hs]; exact hne), Int.negSucc_eq]
      push_cast
      omega
  · obtain ⟨hnone, hinf⟩ := not_finite_cases x (isFinite_eq_false_of_nonFinite_ne_zero x hguard)
    rw [beq_zero_eq_false hguard, nanCode_eq]
    cases hnan : Model.isNaN x
    · rw [hnan] at hinf
      have hscale : Model.scale x n mode = x := by
        rw [← Model.value_scale]
        simp [Model.scale, Model.Internal.Status.scale, Model.exactValue, hnone, hinf,
          Model.outcomeWithInvalid]
      rw [hscale]
    · rw [hnan] at hinf
      have hscale : Model.scale x n mode = Model.quietNaN x := by
        rw [← Model.value_scale]
        simp [Model.scale, Model.Internal.Status.scale, Model.exactValue, hnone, hinf,
          Model.outcomeWithInvalid]
      rw [hscale, quietNaN_bits x hnan]
      rfl

/--
Encoding of the integer of sign `negative` and magnitude `magnitude` rounded into `fmt` in the
direction `mode` (`roundInteger_eq`): `KernelPath.round` of the magnitude at the exponent zero,
with the bit length of the magnitude as its bound, so that the cost does not grow with the
exponent range of the format.
-/
def roundInteger (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (negative : Bool)
    (magnitude : Nat) : Nat :=
  round fmt mode (Numerics.Kernel.size magnitude) (signNat negative) (signNat negative) magnitude
    (Nat.sub (Nat.add fmt.exponentBias fmt.fracWidth) 1) 0 0 0

/--
`roundInteger` computes the encoding of the reference rounding of an integer, for every format
descriptor, rounding direction, sign and magnitude.
-/
theorem roundInteger_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (negative : Bool)
    (magnitude : Nat) :
    roundInteger fmt mode negative magnitude =
      (Model.Internal.Directed.roundDyadic fmt mode ⟨negative, magnitude, 0⟩).toNatBits := by
  have hfrac := fmt.fracWidth_pos
  refine round_eq fmt mode _ _ _ _ _ _ _ ⟨negative, magnitude, 0⟩ ?_ rfl rfl ?_ (fun _ => rfl)
  · rw [Numerics.Kernel.size_eq]
    exact Nat.lt_size_self _
  · intro _
    change (0 : Int) = ((fmt.exponentBias + fmt.fracWidth - 1 : Nat) : Int) - ((0 : Nat) : Int) +
      fmt.minSubnormalExponent
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    omega

namespace Value

universe u

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/-- Kernel `scaleB` of a stored value: the value times `2 ^ n`, rounded in `mode`. -/
def scale (mode : Model.IEEERoundingMode) (n : Int) (x : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat F :=
  unary (KernelPath.scale format mode n) (fun x => Model.scale x n mode)
    (scale_eq_spec mode n) x

/-- The kernel `scaleB` is the model operation carried through the conversions. -/
theorem scale_eq_lift (mode : Model.IEEERoundingMode) (n : Int)
    (x : FloatLib.Floats.ExecFloat F) :
    scale mode n x = NatView.liftUnary (fun x => Model.scale x n mode) x :=
  unary_eq _ _ _ x

/-- The encoding of a scaled value is the flat operation on the encoding. -/
@[kernel_optimize] theorem toNat_scale (mode : Model.IEEERoundingMode) (n : Int)
    (x : FloatLib.Floats.ExecFloat F) :
    toNat (scale mode n x) = KernelPath.scale format mode n (toNat x) :=
  toNat_unary _ _ _ x

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
