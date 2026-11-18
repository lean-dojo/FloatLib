/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Fast.Rounding

/-!
# Short multiplication paths

`mulFast` reads the bit length of a significand product from its top two bits and uses the general
multiplier when a factor is subnormal. For every descriptor, rounding direction and operand pair,
`mulFast_eq_spec` proves that it computes the encoding of `Model.mul`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics
open FloatLib.Numerics.Kernel (bitLength bitLength_eq searchLength searchLength_eq)

/--
The short path of multiplication: the bit length of the product of two normal significands is
read off its top two bits, and every other case gives `special`.
-/
def mulFastWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b special : Nat) : Nat :=
  (fun sa sb ua ub =>
    (fun ha hb =>
      (fun product =>
        (fun v =>
          roundAt fmt mode (Nat.xor sa sb) (Nat.xor sa sb) product
            (Nat.succ (Nat.add ha hb)) (Nat.add fmt.exponentBias fmt.fracWidth)
            (Nat.add
              (Nat.add (Nat.sub ua (maxFinite fmt)) (Nat.sub ub (maxFinite fmt)))
              (Nat.add (Nat.sub 1 v) (negZeroNaN fmt)))
            special
            (Nat.add (Nat.succ (Nat.mul 2 fmt.fracWidth)) (Nat.shiftRight v 1)))
          (Nat.shiftRight product (Nat.mul 2 fmt.fracWidth)))
        (Nat.mul (Nat.sub ua (Nat.shiftLeft ha fmt.fracWidth))
          (Nat.sub ub (Nat.shiftLeft hb fmt.fracWidth))))
      (Nat.sub (Nat.shiftRight ua fmt.fracWidth) 1) (Nat.sub (Nat.shiftRight ub fmt.fracWidth) 1))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

/--
Encoding of the product of the values encoded by `a` and `b`, rounded in the direction `mode`:
the short path `mulFastWith`, and `mul` in every case that leaves it (`mulFast_eq`).
-/
def mulFast (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  mulFastWith fmt mode a b (mul fmt mode a b)

/-- `mulFast` computes `mul`, on all natural numbers. -/
theorem mulFast_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) :
    mulFast fmt mode a b = mul fmt mode a b := by
  unfold mulFast mulFastWith
  simp only []
  generalize hguard : Nat.add
      (Nat.add (Nat.sub (Nat.land a (magnitudeMask fmt)) (maxFinite fmt))
        (Nat.sub (Nat.land b (magnitudeMask fmt)) (maxFinite fmt)))
      (Nat.add
        (Nat.sub 1 (Nat.shiftRight
          (Nat.mul
            (Nat.sub (Nat.land a (magnitudeMask fmt))
              (Nat.shiftLeft (Nat.sub (Nat.shiftRight (Nat.land a (magnitudeMask fmt))
                fmt.fracWidth) 1) fmt.fracWidth))
            (Nat.sub (Nat.land b (magnitudeMask fmt))
              (Nat.shiftLeft (Nat.sub (Nat.shiftRight (Nat.land b (magnitudeMask fmt))
                fmt.fracWidth) 1) fmt.fracWidth)))
          (Nat.mul 2 fmt.fracWidth)))
        (negZeroNaN fmt)) = guard
  by_cases hzero : guard = 0
  · subst hzero
    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftRight_eq', Nat.shiftLeft_eq',
      Nat.land_eq] at hguard
    obtain ⟨hfinite, hrest⟩ := Nat.eq_zero_of_add_eq_zero hguard
    obtain ⟨hfa, hfb⟩ := Nat.eq_zero_of_add_eq_zero hfinite
    obtain ⟨hv, hnzn⟩ := Nat.eq_zero_of_add_eq_zero hrest
    unfold mul round
    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftRight_eq', Nat.shiftLeft_eq',
      Nat.land_eq, Nat.xor_eq, Nat.succ_eq_add_one, hfa, hfb, hnzn, Nat.zero_mul, Nat.add_zero]
    generalize hproduct : ((a &&& magnitudeMask fmt) -
        ((a &&& magnitudeMask fmt) >>> fmt.fracWidth - 1) <<< fmt.fracWidth) *
      ((b &&& magnitudeMask fmt) -
        ((b &&& magnitudeMask fmt) >>> fmt.fracWidth - 1) <<< fmt.fracWidth) = product at hv ⊢
    have hbound : product < 2 ^ mulBits fmt := by
      have hsplit : 2 ^ mulBits fmt = 2 ^ (fmt.fracWidth + 1) * 2 ^ (fmt.fracWidth + 1) := by
        rw [← Nat.pow_add]; congr 1; unfold mulBits; omega
      rw [← hproduct, hsplit]
      exact Nat.mul_lt_mul'' (significand_lt _ _) (significand_lt _ _)
    have hlow : 2 ^ (2 * fmt.fracWidth) ≤ product := by
      by_contra hlt
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)] at hv
      omega
    have hhigh : product < 2 ^ (2 * fmt.fracWidth + 2) := by
      unfold mulBits at hbound; exact hbound
    have hlength : bitLength (mulBits fmt) product =
        2 * fmt.fracWidth + 1 + (product >>> (2 * fmt.fracWidth)) >>> 1 := by
      have hpos : product ≠ 0 := by have := Nat.two_pow_pos (2 * fmt.fracWidth); omega
      rw [bitLength_eq hbound, ite_eq_right hpos, log2_eq_add_carry hlow hhigh,
        ← Nat.shiftRight_add]
      omega
    rw [hlength]
    exact roundAt_special fmt mode _ _ _ _ _ _ _ _
  · exact roundAt_guard fmt mode _ _ _ _ _ _ _ _ hzero

/--
`mulFast` computes the encoding of the reference multiplication `Model.mul x y (mode := mode)`,
for every format descriptor, every rounding direction and all operands.
-/
theorem mulFast_eq_spec {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    mulFast fmt mode x.toNatBits y.toNatBits = (Model.mul x y (mode := mode)).toNatBits := by
  rw [mulFast_eq, mul_eq_spec]

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
