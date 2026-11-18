/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Status
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Semantics

/-!
# Kernel path: the IEEE total order

`totalOrderCode fmt a b` is one when the value encoded by `a` precedes or equals the value
encoded by `b` in the total order of IEEE 754-2019 §5.10, `Model.totalOrder`, and zero
otherwise. `totalOrderCode_eq` proves this for every format descriptor and all operands.

Two words that are not NaNs are ordered by their comparison keys with the negative ones moved
down by one, which puts the negative zero before the positive zero and changes nothing else. A
negative NaN precedes every other value and a positive NaN follows it. Two NaNs of one sign are
ordered by `nanKey`, the signaling class and then the fraction, increasing for a clear sign and
decreasing for a set one.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The key of a NaN word `a` with fields `u` among the positive NaNs: the signaling ones first, and
each class by increasing fraction.
-/
def nanKey (fmt : FloatFormat) (a u : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.sub 1 (signalingFlag fmt a)) (Nat.pow 2 fmt.fracWidth))
    (Nat.mod u (Nat.pow 2 fmt.fracWidth))

/--
One when the value encoded by `a` precedes or equals the value encoded by `b` in the IEEE total
order, and zero otherwise (`totalOrderCode_eq`). See the module documentation.
-/
def totalOrderCode (fmt : FloatFormat) (a b : Nat) : Nat :=
  (fun sa sb ua ub =>
    (fun na nb =>
      Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.add na nb) 0)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.mul na nb) 0)
          ((fun ka kb =>
              Nat.add (Nat.mul sa (Nat.sub 1 sb))
                (Nat.mul (Nat.sub 1 (Nat.add (Nat.sub sa sb) (Nat.sub sb sa)))
                  (Nat.add (Nat.mul (Nat.sub 1 sa) (geFlag kb ka)) (Nat.mul sa (geFlag ka kb)))))
            (nanKey fmt a ua) (nanKey fmt b ub))
          (Nat.add (Nat.mul na sa) (Nat.mul nb (Nat.sub 1 sb))))
        (geFlag (Nat.sub (compareKey fmt sb ub) sb) (Nat.sub (compareKey fmt sa ua) sa)))
      (nanFlag fmt sa ua) (nanFlag fmt sb ub))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

/-- A word that is not a NaN and whose exponent and fraction fields are zero is a zero. -/
theorem isZero_of_fields_eq_zero {fmt : FloatFormat} (x : Model fmt)
    (hnan : Model.isNaN x = false)
    (hfields : Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x = 0) :
    Model.isZero x = true := by
  have hz := zeroFlag_eq x
  have hn := nanFlag_eq x
  rw [hfields] at hz hn
  rw [hnan] at hn
  have hinf : 0 < infMagnitude fmt := by
    unfold infMagnitude
    have hones : 0 < fmt.expAllOnesNat := by
      unfold FloatFormat.expAllOnesNat
      have := Nat.one_lt_two_pow (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2)
        fmt.expWidth_ge_two))
      omega
    cases fmt.encoding
    · exact Nat.mul_pos hones (Nat.two_pow_pos _)
    · exact Nat.two_pow_pos _
    · exact Nat.two_pow_pos _
    · exact Nat.two_pow_pos _
  unfold zeroFlag at hz
  unfold nanFlag nonFinite infFlag at hn
  simp only [Nat.mul_eq, Nat.sub_eq, Nat.add_eq, Bool.false_eq_true, ite_false, Nat.sub_zero,
    Nat.one_mul, Nat.zero_sub, Nat.zero_add] at hz hn
  cases hzero : Model.isZero x
  · rw [hzero] at hz
    simp only [Bool.false_eq_true, ite_false] at hz
    generalize negZeroNaN fmt * (if Model.signBit x then 1 else 0) = t at hz hn
    rcases Nat.mul_eq_zero.1 hn with h | h <;> omega
  · rfl

/-- Two values with the same sign and the same exponent and fraction fields are equal. -/
theorem eq_of_fields_eq {fmt : FloatFormat} (x y : Model fmt)
    (hsign : Model.signBit x = Model.signBit y)
    (hfields : Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x =
      Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y) : x = y := by
  have hbits : x.toNatBits = y.toNatBits := by
    rw [toNatBits_eq_fields x, toNatBits_eq_fields y, hsign, hfields]
  rw [← Model.ofNatBits_toNatBits x, ← Model.ofNatBits_toNatBits y, hbits]

/--
The order of two NaNs as arithmetic on their sign bits, signaling bits and fractions: the code
of `totalOrderCode` for two NaNs is one exactly when the rule of `Model.totalOrder_nan_iff`
holds.
-/
private theorem nanOrder_iff (sx sy gx gy : Bool) (fx fy F : Nat) (hfx : fx < F) (hfy : fy < F) :
    Nat.beq
        ((if sx then 1 else 0) * (1 - if sy then 1 else 0) +
          (1 - (((if sx then 1 else 0) - if sy then 1 else 0) +
              ((if sy then 1 else 0) - if sx then 1 else 0))) *
            ((1 - if sx then 1 else 0) *
                (if (1 - if gx then 1 else 0) * F + fx ≤ (1 - if gy then 1 else 0) * F + fy
                  then 1 else 0) +
              (if sx then 1 else 0) *
                (if (1 - if gy then 1 else 0) * F + fy ≤ (1 - if gx then 1 else 0) * F + fx
                  then 1 else 0))) 1 = true ↔
      (sx = true ∧ sy = false) ∨ sx = sy ∧
        (if sx then (gx = false ∧ gy = true) ∨ gx = gy ∧ fy ≤ fx
        else (gx = true ∧ gy = false) ∨ gx = gy ∧ fx ≤ fy) := by
  cases sx <;> cases sy <;> cases gx <;> cases gy <;>
    simp only [Bool.false_eq_true, ite_true, ite_false, Nat.sub_self, Nat.sub_zero, Nat.zero_mul,
      Nat.one_mul, Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, true_and, false_and,
      and_true, and_false, or_false, false_or, or_true, reduceCtorEq,
      show Nat.beq 0 1 = false from rfl, show Nat.beq 1 1 = true from rfl, iff_true, iff_false,
      Nat.zero_sub, Nat.add_le_add_iff_left] <;>
    first
      | done
      | (by_cases h : fx ≤ fy <;>
        simp only [h, ↓reduceIte, Nat.beq_refl, Nat.beq_eq, zero_ne_one, ite_eq_left_iff, not_le,
        imp_false, not_lt] <;> omega)

/--
`totalOrderCode` computes the IEEE total order `Model.totalOrder`, for every format descriptor
and all operands: the two zeros are ordered by sign, NaNs by sign, signaling class and fraction.
-/
theorem totalOrderCode_eq {fmt : FloatFormat} (x y : Model fmt) :
    Nat.beq (totalOrderCode fmt x.toNatBits y.toNatBits) 1 = Model.totalOrder x y := by
  have hfx := Model.fracField_lt_pow2 x
  have hfy := Model.fracField_lt_pow2 y
  have hux := fields_lt_two_pow_signPos x
  have huy := fields_lt_two_pow_signPos y
  have hfracx : (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) % 2 ^ fmt.fracWidth =
      Model.fracField x := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hfx]
  have hfracy : (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y) % 2 ^ fmt.fracWidth =
      Model.fracField y := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hfy]
  have hcompare := compareCode_eq x y
  unfold compareCode at hcompare
  unfold totalOrderCode nanKey
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.sub_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq,
    mod_def, sign_toNatBits, magnitude_toNatBits, nanFlag_eq, hfracx, hfracy, geFlag_eq]
    at hcompare ⊢
  cases hnx : Model.isNaN x <;> cases hny : Model.isNaN y
  · -- Neither is a NaN: the comparison keys, with the zeros apart.
    rw [hnx, hny] at hcompare
    simp only [Bool.false_eq_true, ite_false, show Nat.beq (0 + 0) 0 = true from rfl]
      at hcompare ⊢
    rw [decodeOrdering_keys, compareKey_eq fmt _ _ (le_of_lt hux),
      compareKey_eq fmt _ _ (le_of_lt huy)] at hcompare
    rw [compareKey_eq fmt _ _ (le_of_lt hux), compareKey_eq fmt _ _ (le_of_lt huy)]
    generalize hu : Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x = u at *
    generalize hv : Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y = v at *
    generalize 2 ^ signPos fmt = P at *
    rcases Nat.lt_trichotomy (if Model.signBit x then P - u else P + u)
        (if Model.signBit y then P - v else P + v) with hlt | heq | hgt
    · rw [(compare_lt_iff_lt).2 hlt] at hcompare
      rw [Model.totalOrder_of_compare_eq_lt hcompare.symm]
      cases hsx : Model.signBit x <;> cases hsy : Model.signBit y <;>
        simp only [hsx, hsy, Bool.false_eq_true, ite_true, ite_false] at hlt ⊢ <;>
        rw [ite_eq_left (by omega)] <;> rfl
    · cases hsx : Model.signBit x <;> cases hsy : Model.signBit y <;>
        simp only [hsx, hsy, Bool.false_eq_true, ite_true, ite_false] at heq ⊢
      · have hxy : x = y := eq_of_fields_eq x y (hsx.trans hsy.symm) (by rw [hu, hv]; omega)
        rw [hxy, Model.totalOrder_refl, ite_eq_left (by omega)]
        rfl
      · have hzx := isZero_of_fields_eq_zero x hnx (by rw [hu]; omega)
        have hzy := isZero_of_fields_eq_zero y hny (by rw [hv]; omega)
        rw [Model.totalOrder_zero_iff hzx hzy, hsx, hsy, ite_eq_right (by omega)]
        rfl
      · have hzx := isZero_of_fields_eq_zero x hnx (by rw [hu]; omega)
        have hzy := isZero_of_fields_eq_zero y hny (by rw [hv]; omega)
        rw [Model.totalOrder_zero_iff hzx hzy, hsx, hsy, ite_eq_left (by omega)]
        rfl
      · have hxy : x = y := eq_of_fields_eq x y (hsx.trans hsy.symm) (by rw [hu, hv]; omega)
        rw [hxy, Model.totalOrder_refl, ite_eq_left (by omega)]
        rfl
    · rw [(compare_gt_iff_gt).2 hgt] at hcompare
      rw [Model.totalOrder_eq_false_of_compare_eq_gt hcompare.symm]
      cases hsx : Model.signBit x <;> cases hsy : Model.signBit y <;>
        simp only [hsx, hsy, Bool.false_eq_true, ite_true, ite_false] at hgt ⊢ <;>
        rw [ite_eq_right (by omega)] <;> rfl
  · -- Only the second is a NaN.
    rw [Model.totalOrder_number_nan hnx hny]
    simp only [Bool.false_eq_true, ite_true, ite_false, Nat.zero_add, Nat.zero_mul, Nat.one_mul,
      show Nat.beq 1 0 = false from rfl, show Nat.beq 0 0 = true from rfl]
    cases Model.signBit y <;> rfl
  · -- Only the first is a NaN.
    rw [Model.totalOrder_nan_number hnx hny]
    simp only [Bool.false_eq_true, ite_true, ite_false, Nat.add_zero, Nat.mul_zero, Nat.one_mul,
      Nat.zero_mul, show Nat.beq 1 0 = false from rfl, show Nat.beq 0 0 = true from rfl]
    cases Model.signBit x <;> rfl
  · -- Two NaNs: sign, then signaling class, then fraction.
    rw [signalingFlag_eq x hnx, signalingFlag_eq y hny, Bool.eq_iff_iff,
      Model.totalOrder_nan_iff hnx hny]
    simp only [ite_true, Nat.one_mul, show Nat.beq (1 + 1) 0 = false from rfl,
      show Nat.beq 1 0 = false from rfl]
    exact nanOrder_iff _ _ _ _ _ _ _ hfx hfy

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
