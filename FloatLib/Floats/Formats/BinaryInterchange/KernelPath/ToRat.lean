/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Status

/-!
# Kernel path: the exact rational value of a word

`ratValue fmt a` is the rational number that a finite word `a` encodes: its significand with the
implicit bit, shifted by its exponent field, over `2 ^ (exponentBias + fracWidth - 1)`, with its
sign. The kernel builds it with one shift and one normalization of a fraction. `ratValue_eq`
proves it equal to the exact value `Numerics.Dyadic.toRat` of the decoded word, for every format
descriptor and every finite value, which is what `Model.toRat?` returns.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The exact rational value of the finite word `a` (`ratValue_eq`): the signed significand shifted
by the exponent field, over `2 ^ (exponentBias + fracWidth - 1)`.
-/
def ratValue (fmt : FloatFormat) (a : Nat) : ℚ :=
  (fun s u =>
    (fun h =>
      (fun N =>
        mkRat (Bool.casesOn (motive := fun _ => Int) (Nat.beq s 0) (Int.negOfNat N) (Int.ofNat N))
          (Nat.shiftLeft 1 (Nat.sub (Nat.add fmt.exponentBias fmt.fracWidth) 1)))
        (Nat.shiftLeft (Nat.sub u (Nat.shiftLeft h fmt.fracWidth)) h))
      (Nat.sub (Nat.shiftRight u fmt.fracWidth) 1))
    (Nat.shiftRight a (signPos fmt)) (Nat.land a (magnitudeMask fmt))

/--
`ratValue` is the exact rational value of a finite value, for every format descriptor: the
value of the dyadic that `Model.toDyadic?` decodes.
-/
theorem ratValue_eq {fmt : FloatFormat} (x : Model fmt) (d : Numerics.Dyadic)
    (hd : Model.toDyadic? x = some d) : ratValue fmt x.toNatBits = d.toRat := by
  have hfx := Model.fracField_lt_pow2 x
  have hbias := fmt.exponentBias_pos
  have hexp : fmt.minSubnormalExponent - ((0 : ℕ) : Int) - 2 =
      -((fmt.exponentBias + fmt.fracWidth - 1 + 2 : ℕ) : Int) := by
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    omega
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  rw [decoded_toRat x d hd 0, hexp, zpow_neg, zpow_natCast]
  unfold ratValue
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    sign_toNatBits, magnitude_toNatBits, fields_shiftRight _ _ _ hfx, fields_sub_shiftLeft]
  generalize (if Model.expField x = 0 then Model.fracField x
    else 2 ^ fmt.fracWidth + Model.fracField x) = m
  simp only [Rat.mkRat_eq_div, Nat.shiftLeft_eq, Nat.one_mul, Nat.add_zero]
  cases Model.signBit x
  · simp only [Bool.false_eq_true, ite_false, show Nat.beq 0 0 = true from rfl,
      show ((0 : ℕ) = 1) = False from by simp, Int.ofNat_eq_natCast, Int.cast_natCast]
    push_cast
    rw [pow_add, pow_add]
    field_simp
  · simp only [ite_true, show Nat.beq 1 0 = false from rfl, Int.negOfNat_eq, Int.ofNat_eq_natCast,
      Int.cast_neg, Int.cast_natCast]
    push_cast
    rw [pow_add, pow_add]
    field_simp

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
