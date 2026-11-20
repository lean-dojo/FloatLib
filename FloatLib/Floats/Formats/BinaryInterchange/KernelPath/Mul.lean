/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Reference

/-!
# Kernel multiplication on encodings

`mul fmt mode a b` is the natural-number encoding of the product of the values encoded by `a` and
`b` in `fmt`, rounded in the direction `mode`: the exact product of the two significands, rounded
once by `round`. Operands that are not both finite go to `mulSpecial`, which applies the NaN and
infinity rules of the reference with flags computed on the encodings; these rules do not depend
on the direction.

`mul_eq_spec` proves that it is the encoding of `Model.mul x y (mode := mode)`, for every format
descriptor, every rounding direction and every operand.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/-- Bound on the bit length of a product of two significands of `fmt`. -/
def mulBits (fmt : FloatFormat) : Nat :=
  2 * fmt.fracWidth + 2

kernel_constant mulBits

/--
The product of two words that are not both finite, by the rules of `Model.Spec.mul`: a NaN
operand gives `nanChoice`, an infinity times a zero gives the invalid result, and an infinity
times another value gives the infinity with the product sign.
-/
def mulSpecial (fmt : FloatFormat) (a b : Nat) : Nat :=
  (fun sa sb ua ub =>
    (fun infA infB nanA nanB =>
      Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.add nanA nanB) 0)
        (nanChoice fmt a b (Nat.mul nanA (signalingFlag fmt a))
          (Nat.mul nanB (signalingFlag fmt b)) nanA)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq infA 0)
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (zeroFlag fmt sb ub) 0)
            (invalidWord fmt)
            (Bool.casesOn (motive := fun _ => Nat) (Nat.beq sa sb)
              (overflowWord fmt true) (overflowWord fmt false)))
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq infB 0)
            (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (zeroFlag fmt sa ua) 0)
              (invalidWord fmt)
              (Bool.casesOn (motive := fun _ => Nat) (Nat.beq sa sb)
                (overflowWord fmt true) (overflowWord fmt false)))
            (invalidWord fmt))))
      (infFlag fmt ua) (infFlag fmt ub) (nanFlag fmt sa ua) (nanFlag fmt sb ub))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

kernel_constant mulSpecial

/--
Encoding of the product of the values encoded by `a` and `b`, rounded in the direction `mode`
(`mul_eq_spec`).
-/
def mul (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  (fun sa sb ua ub =>
    (fun ha hb =>
      round fmt mode (mulBits fmt) (Nat.xor sa sb) (Nat.xor sa sb)
        (Nat.mul (Nat.sub ua (Nat.shiftLeft ha fmt.fracWidth))
          (Nat.sub ub (Nat.shiftLeft hb fmt.fracWidth)))
        (Nat.succ (Nat.add ha hb)) (Nat.add fmt.exponentBias fmt.fracWidth)
        (Nat.add
          (Nat.add (Nat.sub ua (maxFinite fmt)) (Nat.mul (negZeroNaN fmt) (Nat.sub sa ua)))
          (Nat.add (Nat.sub ub (maxFinite fmt)) (Nat.mul (negZeroNaN fmt) (Nat.sub sb ub))))
        (mulSpecial fmt a b))
      (Nat.sub (Nat.shiftRight ua fmt.fracWidth) 1) (Nat.sub (Nat.shiftRight ub fmt.fracWidth) 1))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

/--
`mulSpecial` computes the encoding of the reference product when an operand is not finite, in
every encoding.
-/
theorem mulSpecial_eq {fmt : FloatFormat} (x y : Model fmt)
    (h : Model.isFinite x = false ∨ Model.isFinite y = false) :
    mulSpecial fmt x.toNatBits y.toNatBits = (Model.Spec.mul x y).toNatBits := by
  have hspec : Model.Spec.mul x y =
      (Model.chooseNaN2 x y).getD
        (if Model.isInfinite x then
          if Model.isZero y then Model.invalidResult fmt
          else Model.nativeOverflow fmt (Model.signBit x != Model.signBit y)
        else if Model.isInfinite y then
          if Model.isZero x then Model.invalidResult fmt
          else Model.nativeOverflow fmt (Model.signBit x != Model.signBit y)
        else Model.invalidResult fmt) := by
    unfold Model.Spec.mul
    rcases h with h | h
    · rw [toDyadic?_eq_none_of_isFinite_eq_false x h]
      cases Model.toDyadic? y <;> cases Model.chooseNaN2 x y <;> rfl
    · rw [toDyadic?_eq_none_of_isFinite_eq_false y h]
      cases Model.toDyadic? x <;> cases Model.chooseNaN2 x y <;> rfl
  unfold mulSpecial
  simp only [Nat.shiftRight_eq', Nat.land_eq, sign_toNatBits, magnitude_toNatBits, infFlag_eq,
    nanFlag_eq, zeroFlag_eq, beq_sign]
  rw [hspec]
  refine (chooseNaN2_getD_bits x y _ _ ?_).symm
  intro _ _
  simp only [bne, invalidWord_eq, overflowWord_eq]
  cases Model.isInfinite x <;> cases Model.isInfinite y <;> cases Model.isZero x <;>
    cases Model.isZero y <;> cases (Model.signBit x == Model.signBit y) <;> rfl

/--
`mul` computes the encoding of the reference multiplication `Model.mul x y (mode := mode)`, for
every format descriptor, every rounding direction and all operands.
-/
theorem mul_eq_spec {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    mul fmt mode x.toNatBits y.toNatBits = (Model.mul x y (mode := mode)).toNatBits := by
  have hfx := Model.fracField_lt_pow2 x
  have hfy := Model.fracField_lt_pow2 y
  unfold mul
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.xor_eq, Nat.succ_eq_add_one, sign_toNatBits, magnitude_toNatBits,
    fields_shiftRight _ _ _ hfx, fields_shiftRight _ _ _ hfy, fields_sub_shiftLeft, xor_sign]
  by_cases hguard :
      Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x - maxFinite fmt +
          negZeroNaN fmt * ((if Model.signBit x then 1 else 0) -
            (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x)) +
        (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y - maxFinite fmt +
          negZeroNaN fmt * ((if Model.signBit y then 1 else 0) -
            (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y))) = 0
  · obtain ⟨hgx, hgy⟩ := Nat.eq_zero_of_add_eq_zero hguard
    have hfinx := isFinite_of_nonFinite_eq_zero x hgx
    have hfiny := isFinite_of_nonFinite_eq_zero y hgy
    obtain ⟨dx, hdx, hnx, hsx, hex⟩ := toDyadic?_of_isFinite x hfinx
    obtain ⟨dy, hdy, hny, hsy, hey⟩ := toDyadic?_of_isFinite y hfiny
    have hmx := decoded_significand_lt x
    have hmy := decoded_significand_lt y
    rw [hguard, mul_of_finite mode x y dx dy hdx hdy]
    have hbound : (if Model.expField x = 0 then Model.fracField x
          else 2 ^ fmt.fracWidth + Model.fracField x) *
        (if Model.expField y = 0 then Model.fracField y
          else 2 ^ fmt.fracWidth + Model.fracField y) < 2 ^ mulBits fmt := by
      have hsplit : 2 ^ mulBits fmt = 2 ^ (fmt.fracWidth + 1) * 2 ^ (fmt.fracWidth + 1) := by
        rw [← Nat.pow_add]; congr 1; unfold mulBits; omega
      rw [hsplit]
      exact Nat.mul_lt_mul'' hmx hmy
    rw [← hsx, ← hsy] at hbound ⊢
    refine round_eq fmt mode (mulBits fmt) _ _ _ _ _ _ _ hbound rfl (by rw [hnx, hny]; rfl) ?_
      (fun _ => rfl)
    intro hne
    have hx0 : dx.significand ≠ 0 := fun h => hne (by rw [h, Nat.zero_mul])
    have hy0 : dy.significand ≠ 0 := fun h => hne (by rw [h, Nat.mul_zero])
    change dx.exponent + dy.exponent = _
    rw [hex hx0, hey hy0]
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    push_cast
    omega
  · rw [round_guard _ _ _ _ _ _ _ _ _ _ hguard]
    have hnonFinite : Model.isFinite x = false ∨ Model.isFinite y = false := by
      change ¬(nonFinite fmt _ _ + nonFinite fmt _ _ = 0) at hguard
      simpa only [Nat.add_eq_zero_iff, nonFinite_eq_zero_iff, not_and_or,
        Bool.not_eq_true] using hguard
    rw [mul_of_nonFinite mode x y hnonFinite]
    exact mulSpecial_eq x y hnonFinite

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
