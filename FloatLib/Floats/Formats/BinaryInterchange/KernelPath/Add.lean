/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Reference

/-!
# Kernel addition, subtraction and negation on encodings

`add fmt mode a b` is the natural-number encoding of the sum of the values encoded by `a` and `b`
in `fmt`, rounded in the direction `mode`. For two finite operands it runs about eighty
kernel-accelerated operations on naturals and two branches. Operands that are not both finite go
to `addSpecial`, which applies the NaN and infinity rules of the reference with flags computed on
the encodings; these rules do not depend on the direction.

`add_eq_spec`, `sub_eq_spec` and `neg_eq_spec` prove that these are the encodings of
`Model.add x y (mode := mode)`, `Model.sub x y (mode := mode)` and `Model.neg`, for every format
descriptor, every rounding direction and every operand: signed zeros (with the sign that the
direction gives an exact zero sum), subnormals, infinities and NaN payloads included.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/-- Largest exponent gap kept when adding two values of `fmt`. -/
def addGap (fmt : FloatFormat) : Nat :=
  2 * fmt.fracWidth + 7

kernel_constant addGap

/-- Bound on the bit length of an aligned sum of two values of `fmt`. -/
def addBits (fmt : FloatFormat) : Nat :=
  3 * fmt.fracWidth + 9

kernel_constant addBits

/--
The sum of two words that are not both finite, by the rules of `Model.Spec.add`: a NaN operand
gives `nanChoice`, two infinities of opposite signs give the invalid result, and otherwise the
infinity is returned.
-/
def addSpecial (fmt : FloatFormat) (a b : Nat) : Nat :=
  (fun sa sb ua ub =>
    (fun infA infB nanA nanB =>
      Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.add nanA nanB) 0)
        (nanChoice fmt a b (Nat.mul nanA (signalingFlag fmt a))
          (Nat.mul nanB (signalingFlag fmt b)) nanA)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq infA 0)
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq infB 0)
            (Bool.casesOn (motive := fun _ => Nat) (Nat.beq sa sb) (invalidWord fmt) a)
            a)
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq infB 0) b (invalidWord fmt))))
      (infFlag fmt ua) (infFlag fmt ub) (nanFlag fmt sa ua) (nanFlag fmt sb ub))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

kernel_constant addSpecial

/--
Encoding of the sum of the values encoded by `a` and `b`, rounded in the direction `mode`
(`add_eq_spec`).
-/
def add (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  (fun sa sb ua ub =>
    (fun ha hb =>
      sumAligned fmt mode (addGap fmt) (addBits fmt) 0
        sa (Nat.sub ua (Nat.shiftLeft ha fmt.fracWidth)) ha
        sb (Nat.sub ub (Nat.shiftLeft hb fmt.fracWidth)) hb
        (Nat.add
          (Nat.add (Nat.sub ua (maxFinite fmt)) (Nat.mul (negZeroNaN fmt) (Nat.sub sa ua)))
          (Nat.add (Nat.sub ub (maxFinite fmt)) (Nat.mul (negZeroNaN fmt) (Nat.sub sb ub))))
        (addSpecial fmt a b))
      (Nat.sub (Nat.shiftRight ua fmt.fracWidth) 1) (Nat.sub (Nat.shiftRight ub fmt.fracWidth) 1))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

/-- One when zero is signed, so that negation flips the sign of every word. -/
def signedZero (fmt : FloatFormat) : Nat :=
  match fmt.encoding with
  | .finiteUnsignedZero => 0
  | .ieee | .finiteMaxNaN | .finite => 1

kernel_constant signedZero

/--
Encoding of the negation (`neg_eq_spec`): the sign bit is flipped, except for the zero and the NaN
of an unsigned-zero format, whose words have no exponent or fraction bit set.
-/
def neg (fmt : FloatFormat) (a : Nat) : Nat :=
  Nat.xor a
    (Nat.shiftLeft
      (Nat.sub 1 (Nat.sub 1 (Nat.add (Nat.land a (magnitudeMask fmt)) (signedZero fmt))))
      (signPos fmt))

/--
Encoding of the difference rounded in the direction `mode`: addition of the negated second
operand.
-/
def sub (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  add fmt mode a (neg fmt b)

/--
`addSpecial` computes the encoding of the reference sum when an operand is not finite, in every
encoding.
-/
theorem addSpecial_eq {fmt : FloatFormat} (x y : Model fmt)
    (h : Model.isFinite x = false ∨ Model.isFinite y = false) :
    addSpecial fmt x.toNatBits y.toNatBits = (Model.Spec.add x y).toNatBits := by
  have hspec : Model.Spec.add x y =
      (Model.chooseNaN2 x y).getD
        (if Model.isInfinite x then
          if Model.isInfinite y then
            if Model.signBit x == Model.signBit y then x else Model.invalidResult fmt
          else x
        else if Model.isInfinite y then y
        else Model.invalidResult fmt) := by
    unfold Model.Spec.add
    rcases h with h | h
    · rw [toDyadic?_eq_none_of_isFinite_eq_false x h]
      cases Model.toDyadic? y <;> cases Model.chooseNaN2 x y <;> rfl
    · rw [toDyadic?_eq_none_of_isFinite_eq_false y h]
      cases Model.toDyadic? x <;> cases Model.chooseNaN2 x y <;> rfl
  unfold addSpecial
  simp only [Nat.shiftRight_eq', Nat.land_eq, sign_toNatBits, magnitude_toNatBits, infFlag_eq,
    nanFlag_eq, beq_sign]
  rw [hspec]
  refine (chooseNaN2_getD_bits x y _ _ ?_).symm
  intro _ _
  simp only [invalidWord_eq]
  cases Model.isInfinite x <;> cases Model.isInfinite y <;>
    cases (Model.signBit x == Model.signBit y) <;> rfl

/--
`add` computes the encoding of the reference addition `Model.add x y (mode := mode)`, for every
format descriptor, every rounding direction and all operands.
-/
theorem add_eq_spec {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    add fmt mode x.toNatBits y.toNatBits = (Model.add x y (mode := mode)).toNatBits := by
  have hfx := Model.fracField_lt_pow2 x
  have hfy := Model.fracField_lt_pow2 y
  unfold add
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, sign_toNatBits, magnitude_toNatBits, fields_shiftRight _ _ _ hfx,
    fields_shiftRight _ _ _ hfy, fields_sub_shiftLeft]
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
    have hpow : 2 ^ (fmt.fracWidth + 1) ≤ 2 ^ (addGap fmt - (fmt.fracWidth + 3)) :=
      Nat.pow_le_pow_right (by decide) (by unfold addGap; omega)
    rw [hguard, add_of_finite mode x y dx dy hdx hdy]
    refine sumAligned_eq fmt mode (addGap fmt) (addBits fmt) 0 dx dy _ _ _ _ _ _ _
      (by unfold addGap; omega) (by omega) (by omega) ?_ (by rw [hnx]; rfl) (by rw [hny]; rfl)
      hsx hsy ?_ ?_ ?_ ?_
    · have hsum : (if Model.expField x = 0 then Model.fracField x
            else 2 ^ fmt.fracWidth + Model.fracField x) +
          (if Model.expField y = 0 then Model.fracField y
            else 2 ^ fmt.fracWidth + Model.fracField y) < 2 ^ (fmt.fracWidth + 2) := by
        have : 2 ^ (fmt.fracWidth + 2) = 2 ^ (fmt.fracWidth + 1) + 2 ^ (fmt.fracWidth + 1) := by
          rw [Nat.pow_succ]; omega
        omega
      calc _ < 2 ^ (fmt.fracWidth + 2) * 2 ^ addGap fmt :=
            Nat.mul_lt_mul_of_pos_right hsum (Nat.two_pow_pos _)
        _ = 2 ^ addBits fmt := by
            rw [← Nat.pow_add]; congr 1; unfold addGap addBits; omega
    · intro hne
      have := hex (by rw [hsx]; exact hne)
      rw [this]; simp
    · intro hne
      have := hey (by rw [hsy]; exact hne)
      rw [this]; simp
    · intro hzero
      have : Model.expField x = 0 := by
        by_contra hne
        rw [ite_eq_right hne] at hzero
        have := Nat.two_pow_pos fmt.fracWidth
        omega
      omega
    · intro hzero
      have : Model.expField y = 0 := by
        by_contra hne
        rw [ite_eq_right hne] at hzero
        have := Nat.two_pow_pos fmt.fracWidth
        omega
      omega
  · rw [sumAligned_guard _ _ _ _ _ _ _ _ _ _ _ _ _ hguard]
    have hnonFinite : Model.isFinite x = false ∨ Model.isFinite y = false := by
      change ¬(nonFinite fmt _ _ + nonFinite fmt _ _ = 0) at hguard
      simpa only [Nat.add_eq_zero_iff, nonFinite_eq_zero_iff, not_and_or,
        Bool.not_eq_true] using hguard
    rw [add_of_nonFinite mode x y hnonFinite]
    exact addSpecial_eq x y hnonFinite

/-- Toggling the stored sign bit of a value xors its encoding with the sign bit. -/
theorem toNatBits_toggleSign {fmt : FloatFormat} (x : Model fmt) :
    (Model.toggleSign x).toNatBits = x.toNatBits ^^^ 2 ^ signPos fmt := by
  have hwidth : fmt.bitWidth - 1 = signPos fmt := by
    unfold FloatFormat.bitWidth signPos; omega
  unfold Model.toggleSign Model.ofBits Model.toNatBits
  rw [BitVec.toNat_xor, FloatFormat.signMask_toNat, hwidth]

/-- `neg` computes the encoding of `Model.neg`, for every format descriptor. -/
theorem neg_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    neg fmt x.toNatBits = (Model.neg x).toNatBits := by
  have hlt := fields_lt_two_pow_signPos x
  have hword := toNatBits_eq_fields x
  unfold neg
  simp only [Nat.xor_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq, Nat.land_eq,
    magnitude_toNatBits, Nat.shiftLeft_eq]
  unfold Model.neg
  by_cases hsigned : fmt.supportsSignedZero = true
  · have hflag : signedZero fmt = 1 := by
      unfold signedZero
      cases hencoding : fmt.encoding <;>
        simp_all [FloatFormat.supportsSignedZero]
    have h1 : 1 - (1 - (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x + 1)) = 1 := by
      omega
    rw [ite_eq_left hsigned, toNatBits_toggleSign, hflag, h1, Nat.one_mul]
  · have hencoding : fmt.encoding = .finiteUnsignedZero := by
      cases h : fmt.encoding <;> simp_all [FloatFormat.supportsSignedZero]
    have hflag : signedZero fmt = 0 := by simp [signedZero, hencoding]
    have hwidth : fmt.bitWidth - 1 = signPos fmt := by
      unfold FloatFormat.bitWidth signPos; omega
    have hnan : Model.isNaN x = true ↔ x.toNatBits = 2 ^ signPos fmt := by
      simp only [Model.isNaN, hencoding, beq_iff_eq]
      rw [← hwidth, ← FloatFormat.signMask_toNat]
      exact BitVec.toNat_inj.symm
    have hzero : Model.isZero x = true ↔ x.toNatBits = 0 := by
      simp only [Model.isZero, hencoding, beq_iff_eq]
      exact BitVec.toNat_inj.symm
    rw [ite_eq_right hsigned, hflag, Nat.add_zero]
    generalize Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x = u at hlt hword ⊢
    by_cases hmagnitude : u = 0
    · subst hmagnitude
      have hcond : (Model.isNaN x || Model.isZero x) = true := by
        rw [Bool.or_eq_true, hnan, hzero, hword]
        cases Model.signBit x <;> simp
      rw [ite_eq_left hcond]
      simp
    · have h1 : 1 - (1 - u) = 1 := by omega
      have hcond : ¬ (Model.isNaN x || Model.isZero x) = true := by
        rw [Bool.or_eq_true, hnan, hzero, hword]
        cases Model.signBit x
        · simp only [Bool.false_eq_true, ↓reduceIte, zero_add, not_or]
          omega
        · simp only [↓reduceIte, Nat.add_eq_left, Nat.add_eq_zero_iff, Nat.pow_eq_zero,
          OfNat.ofNat_ne_zero, ne_eq, false_and, or_false]
          omega
      rw [ite_eq_right hcond, toNatBits_toggleSign, h1, Nat.one_mul]

/--
`sub` computes the encoding of the reference subtraction `Model.sub x y (mode := mode)`, for
every format descriptor, every rounding direction and all operands.
-/
theorem sub_eq_spec {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    sub fmt mode x.toNatBits y.toNatBits = (Model.sub x y (mode := mode)).toNatBits := by
  unfold sub
  rw [sub_eq_add_neg, neg_eq_spec, add_eq_spec]

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
