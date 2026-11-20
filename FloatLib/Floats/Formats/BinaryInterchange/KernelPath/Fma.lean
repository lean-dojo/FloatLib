/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Reference

/-!
# Kernel fused multiply-add on encodings

`fma fmt mode a b c` is the natural-number encoding of `x * y + z` rounded once in the direction
`mode`, for the values encoded by `a`, `b` and `c` in `fmt`: the exact product of the two
significands and the addend go through `sumAligned`, which rounds the exact sum once. Operands
that are not all finite go to `fmaSpecial`, which applies the NaN and infinity rules of the
reference with flags computed on the encodings; these rules do not depend on the direction.

`fma_eq_spec` proves that it is the encoding of `Model.fma x y z (mode := mode)`, for every
format descriptor, every rounding direction and every operand.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/-- Largest exponent gap kept between an exact product and an addend of `fmt`. -/
def fmaGap (fmt : FloatFormat) : Nat :=
  3 * fmt.fracWidth + 6

kernel_constant fmaGap

/-- Bound on the bit length of an aligned sum of an exact product and an addend of `fmt`. -/
def fmaBits (fmt : FloatFormat) : Nat :=
  5 * fmt.fracWidth + 9

kernel_constant fmaBits

/--
The fused multiply-add of three words that are not all finite, by the rules of `Model.Spec.fma`:
a NaN operand gives `nanChoice3`; an infinite product with a zero factor, or with an addend that
is the opposite infinity, gives the invalid result; otherwise the infinite product or the
infinite addend is returned.
-/
def fmaSpecial (fmt : FloatFormat) (a b c : Nat) : Nat :=
  (fun sa sb sc ua ub uc =>
    (fun infA infB infC nanA nanB nanC =>
      Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.add (Nat.add nanA nanB) nanC) 0)
        (nanChoice3 fmt a b c (Nat.mul nanA (signalingFlag fmt a))
          (Nat.mul nanB (signalingFlag fmt b)) (Nat.mul nanC (signalingFlag fmt c)) nanA nanB)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.add infA infB) 0)
          (Bool.casesOn (motive := fun _ => Nat)
            (Nat.beq (Nat.add (zeroFlag fmt sa ua) (zeroFlag fmt sb ub)) 0)
            (invalidWord fmt)
            (Bool.casesOn (motive := fun _ => Nat) (Nat.beq infC 0)
              (Bool.casesOn (motive := fun _ => Nat) (Nat.beq sc (Nat.xor sa sb))
                (invalidWord fmt)
                (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.xor sa sb) 0)
                  (overflowWord fmt true) (overflowWord fmt false)))
              (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.xor sa sb) 0)
                (overflowWord fmt true) (overflowWord fmt false))))
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq infC 0) c (invalidWord fmt))))
      (infFlag fmt ua) (infFlag fmt ub) (infFlag fmt uc)
      (nanFlag fmt sa ua) (nanFlag fmt sb ub) (nanFlag fmt sc uc))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.shiftRight c (signPos fmt)) (Nat.land a (magnitudeMask fmt))
    (Nat.land b (magnitudeMask fmt)) (Nat.land c (magnitudeMask fmt))

kernel_constant fmaSpecial

/--
Encoding of `x * y + z` rounded once in the direction `mode`, for the values encoded by `a`, `b`
and `c` (`fma_eq_spec`). A zero product and a zero addend get the exponent zero, so that they
never count as the operand with the larger exponent.
-/
def fma (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b c : Nat) : Nat :=
  (fun sa sb sc ua ub uc =>
    (fun ha hb hc =>
      (fun mp mc =>
        sumAligned fmt mode (fmaGap fmt) (fmaBits fmt) fmt.subnormalAlignExp
          (Nat.xor sa sb) mp (Nat.mul (Nat.add ha hb) (Nat.sub 1 (Nat.sub 1 mp)))
          sc mc (Nat.mul (Nat.add hc fmt.subnormalAlignExp) (Nat.sub 1 (Nat.sub 1 mc)))
          (Nat.add
            (Nat.add
              (Nat.add (Nat.sub ua (maxFinite fmt)) (Nat.mul (negZeroNaN fmt) (Nat.sub sa ua)))
              (Nat.add (Nat.sub ub (maxFinite fmt)) (Nat.mul (negZeroNaN fmt) (Nat.sub sb ub))))
            (Nat.add (Nat.sub uc (maxFinite fmt)) (Nat.mul (negZeroNaN fmt) (Nat.sub sc uc))))
          (fmaSpecial fmt a b c))
        (Nat.mul (Nat.sub ua (Nat.shiftLeft ha fmt.fracWidth))
          (Nat.sub ub (Nat.shiftLeft hb fmt.fracWidth)))
        (Nat.sub uc (Nat.shiftLeft hc fmt.fracWidth)))
      (Nat.sub (Nat.shiftRight ua fmt.fracWidth) 1) (Nat.sub (Nat.shiftRight ub fmt.fracWidth) 1)
      (Nat.sub (Nat.shiftRight uc fmt.fracWidth) 1))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.shiftRight c (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))
    (Nat.land c (magnitudeMask fmt))

/--
`fmaSpecial` computes the encoding of the reference fused multiply-add when an operand is not
finite, in every encoding.
-/
theorem fmaSpecial_eq {fmt : FloatFormat} (x y z : Model fmt)
    (h : Model.isFinite x = false ∨ Model.isFinite y = false ∨ Model.isFinite z = false) :
    fmaSpecial fmt x.toNatBits y.toNatBits z.toNatBits = (Model.Spec.fma x y z).toNatBits := by
  have hspec : Model.Spec.fma x y z =
      (Model.chooseNaN3 x y z).getD
        (if Model.isInfinite x || Model.isInfinite y then
          if Model.isZero x || Model.isZero y then Model.invalidResult fmt
          else if Model.isInfinite z then
            if Model.signBit z != Bool.xor (Model.signBit x) (Model.signBit y) then
              Model.invalidResult fmt
            else Model.nativeOverflow fmt (Bool.xor (Model.signBit x) (Model.signBit y))
          else Model.nativeOverflow fmt (Bool.xor (Model.signBit x) (Model.signBit y))
        else if Model.isInfinite z then z
        else Model.invalidResult fmt) := by
    unfold Model.Spec.fma
    rcases h with h | h | h
    · rw [toDyadic?_eq_none_of_isFinite_eq_false x h]
      cases Model.toDyadic? y <;> cases Model.toDyadic? z <;>
        cases Model.chooseNaN3 x y z <;> rfl
    · rw [toDyadic?_eq_none_of_isFinite_eq_false y h]
      cases Model.toDyadic? x <;> cases Model.toDyadic? z <;>
        cases Model.chooseNaN3 x y z <;> rfl
    · rw [toDyadic?_eq_none_of_isFinite_eq_false z h]
      cases Model.toDyadic? x <;> cases Model.toDyadic? y <;>
        cases Model.chooseNaN3 x y z <;> rfl
  unfold fmaSpecial
  simp only [Nat.shiftRight_eq', Nat.land_eq, sign_toNatBits, magnitude_toNatBits, infFlag_eq,
    nanFlag_eq, zeroFlag_eq]
  rw [hspec]
  refine (chooseNaN3_getD_bits x y z _ _ ?_).symm
  intro _ _ _
  simp only [invalidWord_eq, overflowWord_eq]
  cases Model.isInfinite x <;> cases Model.isInfinite y <;> cases Model.isInfinite z <;>
    cases Model.isZero x <;> cases Model.isZero y <;>
    cases Model.signBit x <;> cases Model.signBit y <;> cases Model.signBit z <;> rfl

/--
`fma` computes the encoding of the reference fused multiply-add `Model.fma x y z (mode := mode)`,
for every format descriptor, every rounding direction and all operands.
-/
theorem fma_eq_spec {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y z : Model fmt) :
    fma fmt mode x.toNatBits y.toNatBits z.toNatBits =
      (Model.fma x y z (mode := mode)).toNatBits := by
  have hfx := Model.fracField_lt_pow2 x
  have hfy := Model.fracField_lt_pow2 y
  have hfz := Model.fracField_lt_pow2 z
  unfold fma
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.xor_eq, sign_toNatBits, magnitude_toNatBits, fields_shiftRight _ _ _ hfx,
    fields_shiftRight _ _ _ hfy, fields_shiftRight _ _ _ hfz, fields_sub_shiftLeft, xor_sign]
  by_cases hguard :
      Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x - maxFinite fmt +
            negZeroNaN fmt * ((if Model.signBit x then 1 else 0) -
              (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x)) +
          (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y - maxFinite fmt +
            negZeroNaN fmt * ((if Model.signBit y then 1 else 0) -
              (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y))) +
        (Model.expField z * 2 ^ fmt.fracWidth + Model.fracField z - maxFinite fmt +
          negZeroNaN fmt * ((if Model.signBit z then 1 else 0) -
            (Model.expField z * 2 ^ fmt.fracWidth + Model.fracField z))) = 0
  · obtain ⟨hgxy, hgz⟩ := Nat.eq_zero_of_add_eq_zero hguard
    obtain ⟨hgx, hgy⟩ := Nat.eq_zero_of_add_eq_zero hgxy
    obtain ⟨dx, hdx, hnx, hsx, hex⟩ :=
      toDyadic?_of_isFinite x (isFinite_of_nonFinite_eq_zero x hgx)
    obtain ⟨dy, hdy, hny, hsy, hey⟩ :=
      toDyadic?_of_isFinite y (isFinite_of_nonFinite_eq_zero y hgy)
    obtain ⟨dz, hdz, hnz, hsz, hez⟩ :=
      toDyadic?_of_isFinite z (isFinite_of_nonFinite_eq_zero z hgz)
    have hmx := decoded_significand_lt x
    have hmy := decoded_significand_lt y
    have hmz := decoded_significand_lt z
    rw [hguard, fma_of_finite mode x y z dx dy dz hdx hdy hdz]
    rw [← hsx] at hmx
    rw [← hsy] at hmy
    rw [← hsz] at hmz
    rw [← hsx, ← hsy, ← hsz, ← hnx, ← hny, ← hnz]
    have hproduct : dx.significand * dy.significand < 2 ^ (2 * fmt.fracWidth + 2) := by
      have hsplit : 2 ^ (2 * fmt.fracWidth + 2) =
          2 ^ (fmt.fracWidth + 1) * 2 ^ (fmt.fracWidth + 1) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [hsplit]
      exact Nat.mul_lt_mul'' hmx hmy
    have hbiasPos := fmt.exponentBias_pos
    have hfracPos := fmt.fracWidth_pos
    refine sumAligned_eq fmt mode (fmaGap fmt) (fmaBits fmt) fmt.subnormalAlignExp _ dz
      _ _ _ _ _ _ _ (by unfold fmaGap; omega) ?_ ?_ ?_ rfl rfl rfl rfl ?_ ?_ ?_ ?_
    · exact lt_of_lt_of_le hproduct
        (Nat.pow_le_pow_right (by decide) (by unfold fmaGap; omega))
    · exact lt_of_lt_of_le hmz
        (Nat.pow_le_pow_right (by decide) (by unfold fmaGap; omega))
    · have hsum : dx.significand * dy.significand + dz.significand <
          2 ^ (2 * fmt.fracWidth + 3) := by
        have h1 : 2 ^ (2 * fmt.fracWidth + 3) =
            2 ^ (2 * fmt.fracWidth + 2) + 2 ^ (2 * fmt.fracWidth + 2) := by
          rw [Nat.pow_succ]; omega
        have h2 : 2 ^ (fmt.fracWidth + 1) ≤ 2 ^ (2 * fmt.fracWidth + 2) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        omega
      calc _ < 2 ^ (2 * fmt.fracWidth + 3) * 2 ^ fmaGap fmt :=
            Nat.mul_lt_mul_of_pos_right hsum (Nat.two_pow_pos _)
        _ = 2 ^ fmaBits fmt := by
            rw [← Nat.pow_add]; congr 1; unfold fmaGap fmaBits; omega
    · intro hne
      have hx0 : dx.significand ≠ 0 := fun h => hne (by rw [h, Nat.zero_mul])
      have hy0 : dy.significand ≠ 0 := fun h => hne (by rw [h, Nat.mul_zero])
      have hone : 1 - (1 - dx.significand * dy.significand) = 1 := by omega
      change dx.exponent + dy.exponent = _
      rw [hex hx0, hey hy0, hone, Nat.mul_one]
      simp only [FloatFormat.subnormalAlignExp, FloatFormat.minSubnormalExponent,
        FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast]
      push_cast
      omega
    · intro hne
      have hone : 1 - (1 - dz.significand) = 1 := by omega
      rw [hez hne, hone, Nat.mul_one]
      push_cast
      omega
    · intro hzero
      rw [hzero]
      simp
    · intro hzero
      rw [hzero]
      simp
  · rw [sumAligned_guard _ _ _ _ _ _ _ _ _ _ _ _ _ hguard]
    have hnonFinite :
        Model.isFinite x = false ∨ Model.isFinite y = false ∨ Model.isFinite z = false := by
      change ¬(nonFinite fmt _ _ + nonFinite fmt _ _ + nonFinite fmt _ _ = 0) at hguard
      simpa only [Nat.add_eq_zero_iff, nonFinite_eq_zero_iff, not_and_or,
        Bool.not_eq_true, or_assoc] using hguard
    rw [fma_of_nonFinite mode x y z hnonFinite]
    exact fmaSpecial_eq x y z hnonFinite

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
