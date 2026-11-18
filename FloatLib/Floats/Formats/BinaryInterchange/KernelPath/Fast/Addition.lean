/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Fast.Rounding

/-!
# Ordered addition paths

`addFast` orders operands by exponent and fraction fields, so that the larger operand determines
the sign and only its significand is shifted. The top three bits determine a carry, an unchanged
exponent, or one lost bit. Greater cancellation is exact and is packed without a rounding step.
The path falls back to the general adder for nonfinite operands, zero results, overflow and
unsigned-zero encodings. Its refinement holds for every descriptor and direction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics
open FloatLib.Numerics.Kernel (bitLength bitLength_eq searchLength searchLength_eq)

/--
The sum of a larger operand (sign `sbig`, significand `mb`, exponent `hb`) and a smaller one
(significand `ms`, exponent `hs`) whose signs differ when `x` is one: the larger significand is
shifted by the clamped exponent gap and the smaller one added or subtracted. The leading bit of
the result is read off its top three bits: it sits one place below the leading bit of the
larger operand (a subtraction lost one bit), at that place, or one above (a carry), and the
quotient is rounded directly with the exponent field that goes with it. When a subtraction
cancels more, the difference has at most `fracWidth + 1` bits and is exact: its bit length is
computed and `packExact` shifts it to its place, with no rounding step. `special` is the answer
when `guard` is not zero or the difference is zero.
-/
def sumOrdered (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sbig x mb hb ms hs guard special : Nat) : Nat :=
  (fun g =>
    (fun W A =>
      (fun S =>
        (fun u =>
          (fun k =>
            Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.mul u (Nat.add g k)) 0)
              (roundQuotient fmt mode sbig sbig guard special (Nat.sub (Nat.add hb k) 1) S
                (Nat.pow 2 (Nat.sub (Nat.add g k) 1)))
              (packExact fmt mode sbig sbig S (Nat.sub hb g) (Nat.add guard (Nat.sub 1 S)) special
                (bitLength (Nat.succ fmt.fracWidth) S)))
            (Nat.add (Nat.sub 1 (Nat.sub 1 (Nat.shiftRight u 1))) (Nat.shiftRight u 2)))
          (Nat.shiftRight S (Nat.sub (Nat.add g fmt.fracWidth) 1)))
        (Nat.sub (Nat.sub (Nat.add A ms) W) W))
      (Nat.mul x ms) (Nat.shiftLeft mb g))
    ((fun d => Nat.sub d (Nat.sub d (addGap fmt))) (Nat.sub hb hs))

/--
The short path of addition: the operands are ordered by their exponent and fraction fields and
added by `sumOrdered`, and every case that leaves the short path gives `special`.
-/
def addFastWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b special : Nat) : Nat :=
  (fun sa sb ua ub =>
    (fun D x =>
      (fun big small =>
        (fun hb hs =>
          sumOrdered fmt mode (Nat.xor sa (Nat.land x (Nat.sub 1 D))) x
            (Nat.sub big (Nat.shiftLeft hb fmt.fracWidth)) hb
            (Nat.sub small (Nat.shiftLeft hs fmt.fracWidth)) hs
            (Nat.add (Nat.sub big (maxFinite fmt)) (negZeroNaN fmt))
            special)
          (Nat.sub (Nat.shiftRight big fmt.fracWidth) 1)
          (Nat.sub (Nat.shiftRight small fmt.fracWidth) 1))
        (Nat.add ub D) (Nat.sub ua D))
      (Nat.sub ua ub) (Nat.xor sa sb))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

/--
Encoding of the sum of the values encoded by `a` and `b`, rounded in the direction `mode`: the
short path `addFastWith`, and `add` in every case that leaves it (`addFast_eq`).
-/
def addFast (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  addFastWith fmt mode a b (add fmt mode a b)

/--
For aligned magnitudes `Bv ≤ A` whose signed sum is not zero, the branch-free signed sum of
`sumSigned` is `A + Bv` for equal signs and `A - Bv` otherwise, with the sign of `A`.
-/
theorem sumSigned_ordered (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (B Em sa sb A Bv E guard special : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1) (hle : Bv ≤ A)
    (hpos : 1 ≤ A + Bv - (sa ^^^ sb) * Bv - (sa ^^^ sb) * Bv) :
    sumSigned fmt mode B Em sa sb A Bv E guard special =
      round fmt mode B sa sa (A + Bv - (sa ^^^ sb) * Bv - (sa ^^^ sb) * Bv) E Em guard special := by
  unfold sumSigned
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
  generalize hS : A + Bv - (sa ^^^ sb) * Bv - (sa ^^^ sb) * Bv = S at hpos
  generalize hN : sa * A + sb * Bv = N
  have hvalues : (sa = sb ∧ S = A + Bv ∧ N = sa * (A + Bv)) ∨
      (sa = 0 ∧ sb = 1 ∧ S = A - Bv ∧ N = Bv) ∨ (sa = 1 ∧ sb = 0 ∧ S = A - Bv ∧ N = A) := by
    obtain rfl | rfl : sa = 0 ∨ sa = 1 := by omega
    · obtain rfl | rfl : sb = 0 ∨ sb = 1 := by omega
      · left
        simp only [Nat.xor_self, Nat.zero_mul, Nat.sub_zero, Nat.add_zero] at hS hN
        exact ⟨rfl, hS.symm, by rw [Nat.zero_mul]; exact hN.symm⟩
      · right; left
        have hx : (0 : Nat) ^^^ 1 = 1 := rfl
        simp only [hx, Nat.zero_mul, Nat.one_mul, Nat.zero_add] at hS hN
        exact ⟨rfl, rfl, by omega, hN.symm⟩
    · obtain rfl | rfl : sb = 0 ∨ sb = 1 := by omega
      · right; right
        have hx : (1 : Nat) ^^^ 0 = 1 := rfl
        simp only [hx, Nat.zero_mul, Nat.one_mul, Nat.add_zero] at hS hN
        exact ⟨rfl, rfl, by omega, hN.symm⟩
      · left
        simp only [Nat.xor_self, Nat.zero_mul, Nat.sub_zero, Nat.one_mul] at hS hN
        exact ⟨rfl, hS.symm, by omega⟩
  have hsign : 1 - (1 - (N - (A + Bv - N))) = sa := by
    rcases hvalues with ⟨rfl, hs, hn⟩ | ⟨rfl, rfl, _, _⟩ | ⟨rfl, rfl, hs, _⟩
    · obtain rfl | rfl : sa = 0 ∨ sa = 1 := by omega
      · simp only [Nat.zero_mul] at hn; omega
      · simp only [Nat.one_mul] at hn; omega
    · omega
    · omega
  have hmag : A + Bv - N - N + (N - (A + Bv - N)) = S := by
    rcases hvalues with ⟨rfl, hs, hn⟩ | ⟨rfl, rfl, hs, _⟩ | ⟨rfl, rfl, hs, _⟩
    · obtain rfl | rfl : sa = 0 ∨ sa = 1 := by omega
      · simp only [Nat.zero_mul] at hn; omega
      · simp only [Nat.one_mul] at hn; omega
    · omega
    · omega
  have hnonzero : 1 - S = 0 := by omega
  rw [hsign, hmag, hnonzero, Nat.zero_mul, Nat.add_zero]

/-- A nonzero guard makes `sumOrdered` return the special result. -/
theorem sumOrdered_guard (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sbig x mb hb ms hs guard special : Nat) (hguard : guard ≠ 0) :
    sumOrdered fmt mode sbig x mb hb ms hs guard special = special := by
  unfold sumOrdered
  simp only []
  generalize Nat.beq _ 0 = leading
  cases leading
  · exact roundQuotient_guard fmt mode _ _ _ _ _ _ _ hguard
  · exact packExact_guard fmt mode _ _ _ _ _ _ _ (by simp only [Nat.add_eq]; omega)

/--
`sumOrdered` computes `sumAligned` when its first operand is the larger one: a significand `ma`
with exponent `ha` that is normal when `ha` is not zero, against `mb` with exponent `hb ≤ ha` and
`mb ≤ ma` when the exponents agree. The special result of `sumOrdered` is that `sumAligned`.
-/
theorem sumOrdered_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sa sb ma ha mb hb special : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1)
    (hma : ma < 2 ^ (fmt.fracWidth + 1)) (hmb : mb < 2 ^ (fmt.fracWidth + 1))
    (hnormal : 1 ≤ ha → 2 ^ fmt.fracWidth ≤ ma) (hle : hb ≤ ha) (hmag : ha = hb → mb ≤ ma) :
    sumOrdered fmt mode sa (sa ^^^ sb) ma ha mb hb 0
        (sumAligned fmt mode (addGap fmt) (addBits fmt) 0 sa ma ha sb mb hb 0 special) =
      sumAligned fmt mode (addGap fmt) (addBits fmt) 0 sa ma ha sb mb hb 0 special := by
  unfold sumOrdered
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftRight_eq',
    Nat.pow_eq, Nat.zero_add]
  generalize hg : ha - hb - (ha - hb - addGap fmt) = g
  have hgle : g ≤ ha := by omega
  have hgG : g ≤ addGap fmt := by omega
  -- The aligned larger significand dominates the smaller one.
  have hA : mb ≤ ma <<< g := by
    rw [Nat.shiftLeft_eq]
    rcases Nat.eq_zero_or_pos g with h0 | hpos
    · rw [h0, Nat.pow_zero, Nat.mul_one]
      exact hmag (by unfold addGap at hg; omega)
    · have hn := hnormal (by omega)
      have h2 : 2 ≤ 2 ^ g := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ g := Nat.pow_le_pow_right (by decide) hpos
      calc mb ≤ 2 ^ fmt.fracWidth * 2 := by omega
        _ ≤ ma * 2 ^ g := Nat.mul_le_mul hn h2
  have hAlt : ma <<< g < 2 ^ (fmt.fracWidth + 1 + g) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right hma (Nat.two_pow_pos _)
  generalize hS : ma <<< g + mb - (sa ^^^ sb) * mb - (sa ^^^ sb) * mb = S
  have hShigh : S < 2 ^ (g + fmt.fracWidth + 2) := by
    have hpow : 2 ^ (g + fmt.fracWidth + 2) = 2 ^ (fmt.fracWidth + 1 + g) * 2 := by
      rw [show g + fmt.fracWidth + 2 = fmt.fracWidth + 1 + g + 1 by omega, Nat.pow_succ]
    omega
  have hbits : S < 2 ^ addBits fmt :=
    lt_of_lt_of_le hShigh
      (Nat.pow_le_pow_right (by decide) (by unfold addGap at hgG; unfold addBits; omega))
  -- The aligned sum of ordered operands is one rounding of the sum `S` when it is not zero.
  have hround : 1 ≤ S →
      sumAligned fmt mode (addGap fmt) (addBits fmt) 0 sa ma ha sb mb hb 0 special =
        round fmt mode (addBits fmt) sa sa S (ha - g) 0 0 special := by
    intro hSpos
    unfold sumAligned
    simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq']
    have hd2 : hb - ha = 0 := by omega
    rw [hd2, hg]
    simp only [Nat.zero_sub, Nat.shiftLeft_zero, Nat.add_zero]
    rw [sumSigned_ordered fmt mode _ _ sa sb _ _ _ _ _ hsa hsb hA (by rw [hS]; exact hSpos), hS]
  have hK : g + fmt.fracWidth - 1 + 3 = g + fmt.fracWidth + 2 := by
    have := fmt.fracWidth_pos
    omega
  by_cases hfast : S >>> (g + fmt.fracWidth - 1) *
      (g + ((1 - (1 - (S >>> (g + fmt.fracWidth - 1)) >>> 1)) +
        (S >>> (g + fmt.fracWidth - 1)) >>> 2)) = 0
  · -- The difference lost more than one leading bit: it is exact, and its normalization is
    -- the rounding of the general path.
    rw [hfast, show Nat.beq 0 0 = true from rfl]
    change packExact fmt mode sa sa S (ha - g) (1 - S) _ (bitLength (Nat.succ fmt.fracWidth) S) = _
    by_cases hS0 : S = 0
    · exact packExact_guard fmt mode _ _ _ _ _ _ _ (by omega)
    · have hx : sa ^^^ sb ≤ 1 := by
        obtain rfl | rfl : sa = 0 ∨ sa = 1 := by omega
        all_goals obtain rfl | rfl : sb = 0 ∨ sb = 1 := by omega
        all_goals decide
      have hsmall : S < 2 ^ (fmt.fracWidth + 1) := by
        refine cancelled_lt fmt.fracWidth_pos (A := ma <<< g) (m := mb) ?_ ?_ hmb hfast
        · obtain h | h : sa ^^^ sb = 0 ∨ sa ^^^ sb = 1 := by omega
          · rw [h] at hS; omega
          · rw [h] at hS; omega
        · intro hg0
          rw [Nat.shiftLeft_eq]
          exact Nat.mul_le_mul_right _ (hnormal (by omega))
      rw [show 1 - S = 0 by omega, hround (by omega)]
      exact packExact_eq_round fmt mode (addBits fmt) sa sa S (ha - g) _ _ hsmall
        (by unfold addBits; omega)
  · -- The leading bit is one of three places: both sides round the same quotient.
    have hu : S >>> (g + fmt.fracWidth - 1) ≠ 0 := fun h => hfast (by rw [h, Nat.zero_mul])
    have hSlow : 2 ^ (g + fmt.fracWidth - 1) ≤ S := by
      by_contra hlt
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)] at hu
      exact hu rfl
    have hSpos : 1 ≤ S := le_trans (Nat.two_pow_pos _) hSlow
    have hlog := log2_eq_add_offset hSlow (by rw [hK]; exact hShigh)
    have hbeq : Nat.beq (S >>> (g + fmt.fracWidth - 1) *
        (g + ((1 - (1 - (S >>> (g + fmt.fracWidth - 1)) >>> 1)) +
          (S >>> (g + fmt.fracWidth - 1)) >>> 2))) 0 = false := by
      cases h : Nat.beq (S >>> (g + fmt.fracWidth - 1) *
        (g + ((1 - (1 - (S >>> (g + fmt.fracWidth - 1)) >>> 1)) +
          (S >>> (g + fmt.fracWidth - 1)) >>> 2))) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hfast
    rw [hbeq, hround hSpos]
    change roundQuotient fmt mode sa sa 0 _ _ S _ = _
    unfold round
    rw [roundAt_def]
    rw [bitLength_eq hbits, ite_eq_right (by omega : ¬ S = 0), hlog]
    simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.pow_eq, Nat.zero_add,
      Nat.add_zero]
    generalize (1 - (1 - (S >>> (g + fmt.fracWidth - 1)) >>> 1)) +
      (S >>> (g + fmt.fracWidth - 1)) >>> 2 = k at hfast
    have hgk : 1 ≤ g + k := by
      rcases Nat.eq_zero_or_pos (g + k) with h | h
      · exact absurd (by rw [h, Nat.mul_zero]) hfast
      · exact h
    have ht : g + fmt.fracWidth - 1 + k + 1 + (ha - g) - (fmt.fracWidth + 1) = ha + k - 1 := by
      omega
    rw [ht, show ha - g - (ha + k - 1) = 0 by omega, Nat.shiftLeft_zero,
      show ha + k - 1 - (ha - g) = g + k - 1 by omega]
    exact roundQuotient_special fmt mode _ _ _ _ _ _ _

/-- A sign bit as a natural number is at most one. -/
theorem sign_le_one (negative : Bool) : (if negative then 1 else 0 : Nat) ≤ 1 := by
  cases negative <;> simp

/-- The exponent fields of two packed words are ordered as the words. -/
theorem exponent_le_of_fields_le {ea fa eb fb F : Nat} (hfa : fa < F)
    (h : eb * F + fb ≤ ea * F + fa) : eb ≤ ea := by
  by_contra hlt
  have : (ea + 1) * F ≤ eb * F := Nat.mul_le_mul_right F (by omega)
  have hexpand : (ea + 1) * F = ea * F + F := by rw [add_mul]; ac_rfl
  omega

/--
When the exponent fields give the same exponent, the decoded significands of two packed words
are ordered as the words.
-/
theorem significand_le_of_fields_le {ea fa eb fb F : Nat} (hfa : fa < F)
    (h : eb * F + fb ≤ ea * F + fa) (heq : ea - 1 = eb - 1) :
    (if eb = 0 then fb else F + fb) ≤ (if ea = 0 then fa else F + fa) := by
  have hle := exponent_le_of_fields_le hfa h
  by_cases hsame : ea = eb
  · subst hsame
    split <;> omega
  · have ha : ea = 1 := by omega
    have hb : eb = 0 := by omega
    subst ha hb
    simp only [Nat.one_ne_zero, ite_true, ite_false]
    omega

/--
`addFast` computes `add` on the encodings of two values, for every format descriptor and every
rounding direction.
-/
theorem addFast_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    addFast fmt mode x.toNatBits y.toNatBits = add fmt mode x.toNatBits y.toNatBits := by
  have hfx := Model.fracField_lt_pow2 x
  have hfy := Model.fracField_lt_pow2 y
  have hmx := decoded_significand_lt x
  have hmy := decoded_significand_lt y
  -- The general addition, for finite operands of a format with a signed zero or no zero NaN.
  have hgeneral : ∀ special : Nat,
      Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x ≤ maxFinite fmt →
      Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y ≤ maxFinite fmt →
      negZeroNaN fmt = 0 →
      add fmt mode x.toNatBits y.toNatBits =
        sumAligned fmt mode (addGap fmt) (addBits fmt) 0
          (if Model.signBit x then 1 else 0)
          (if Model.expField x = 0 then Model.fracField x
            else 2 ^ fmt.fracWidth + Model.fracField x) (Model.expField x - 1)
          (if Model.signBit y then 1 else 0)
          (if Model.expField y = 0 then Model.fracField y
            else 2 ^ fmt.fracWidth + Model.fracField y) (Model.expField y - 1)
          0 special := by
    intro special hx hy hnzn
    unfold add
    simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
      Nat.mul_eq, sign_toNatBits, magnitude_toNatBits, fields_shiftRight _ _ _ hfx,
      fields_shiftRight _ _ _ hfy, fields_sub_shiftLeft, hnzn, Nat.zero_mul, Nat.add_zero,
      Nat.sub_eq_zero_of_le hx, Nat.sub_eq_zero_of_le hy]
    unfold sumAligned sumSigned round
    simp only [roundAt_def]
    unfold roundQuotient
    simp only [pack_eq, ne_eq, not_true_eq_false, ite_false]
  unfold addFast addFastWith
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.xor_eq, sign_toNatBits, magnitude_toNatBits]
  by_cases hD : Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y <
      Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x
  · -- The first operand is the larger one.
    have hbig : Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y +
        (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x -
          (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y)) =
        Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x := by omega
    have hsmall : Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x -
        (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x -
          (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y)) =
        Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y := by omega
    have hflag : 1 - (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x -
        (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y)) = 0 := by omega
    rw [hbig, hsmall, hflag, Nat.and_zero, Nat.xor_zero]
    simp only [fields_shiftRight _ _ _ hfx, fields_shiftRight _ _ _ hfy, fields_sub_shiftLeft]
    by_cases hguard : Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x - maxFinite fmt +
        negZeroNaN fmt = 0
    · obtain ⟨_, hnzn⟩ := Nat.eq_zero_of_add_eq_zero hguard
      have hle : Model.expField y ≤ Model.expField x :=
        exponent_le_of_fields_le (fb := Model.fracField y) hfx (by omega)
      rw [hguard, hgeneral 0 (by omega) (by omega) hnzn]
      refine sumOrdered_eq fmt mode _ _ _ _ _ _ 0 (sign_le_one _) (sign_le_one _) hmx hmy ?_
        (by omega) ?_
      · intro h1
        have : Model.expField x ≠ 0 := by omega
        simp [this]
      · intro heq
        exact significand_le_of_fields_le (fb := Model.fracField y) hfx (by omega) heq
    · exact sumOrdered_guard fmt mode _ _ _ _ _ _ _ _ hguard
  · -- The second operand is the larger one, or the fields are equal.
    have hzero : Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x -
        (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y) = 0 := by omega
    rw [hzero, Nat.add_zero]
    simp only [Nat.sub_zero, fields_shiftRight _ _ _ hfx, fields_shiftRight _ _ _ hfy,
      fields_sub_shiftLeft]
    have hsign : ∀ p q : Bool, (if p then 1 else 0 : Nat) ^^^
        (((if p then 1 else 0) ^^^ if q then 1 else 0) &&& 1) = if q then 1 else 0 := by
      intro p q
      cases p <;> cases q <;> rfl
    rw [hsign, Nat.xor_comm (if Model.signBit x then 1 else 0)]
    by_cases hguard : Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y - maxFinite fmt +
        negZeroNaN fmt = 0
    · obtain ⟨_, hnzn⟩ := Nat.eq_zero_of_add_eq_zero hguard
      have hle : Model.expField x ≤ Model.expField y :=
        exponent_le_of_fields_le (fb := Model.fracField x) hfy (by omega)
      rw [hguard, hgeneral 0 (by omega) (by omega) hnzn, sumAligned_comm]
      refine sumOrdered_eq fmt mode _ _ _ _ _ _ 0 (sign_le_one _) (sign_le_one _) hmy hmx ?_
        (by omega) ?_
      · intro h1
        have : Model.expField y ≠ 0 := by omega
        simp [this]
      · intro heq
        exact significand_le_of_fields_le (fb := Model.fracField x) hfy (by omega) heq
    · exact sumOrdered_guard fmt mode _ _ _ _ _ _ _ _ hguard

/--
`addFast` computes the encoding of the reference addition `Model.add x y (mode := mode)`, for
every format descriptor, every rounding direction and all operands.
-/
theorem addFast_eq_spec {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    addFast fmt mode x.toNatBits y.toNatBits = (Model.add x y (mode := mode)).toNatBits := by
  rw [addFast_eq, add_eq_spec]

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
