/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Decode
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime

import FloatLib.Numerics.Bitwise

/-!
# Exact signed sums on natural-number encodings

`sumAligned` adds two signed magnitudes `± ma * 2 ^ ha` and `± mb * 2 ^ hb` exactly and rounds the
sum once with `round`, in any of the six rounding directions. It is the common core of the kernel
addition, subtraction and fused multiply-add.

The operand with the larger exponent is shifted left to the smaller one. A gap above `G` is
clamped to `G`: the lower operand then lies wholly below the rounding position and only its
presence and sign matter, so no integer as wide as the exponent range is built. The signed sum is
formed without a branch from the negative part `N = sa * A + sb * B` and the positive part
`A + B - N`.

`sumAligned_eq` proves that the result is the encoding of `roundedSum fmt mode a b` for the exact
dyadic values `a` and `b`: the rounding of the exact sum by `Model.Internal.Directed.roundDyadic`,
and for an exact zero sum the zero whose sign the direction prescribes
(`Model.zeroForExactSum`). It holds for every format descriptor and every direction, under size
bounds that addition and fused multiply-add both meet.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The sign of an exact zero sum of operands with signs `sa` and `sb` (zero or one): negative when
both operands are, and toward negative infinity when either is (`IEEERoundingMode.zeroSumSign`).
-/
def zeroSumSign (mode : Model.IEEERoundingMode) (sa sb : Nat) : Nat :=
  Model.IEEERoundingMode.casesOn (motive := fun _ => Nat) mode
    (Nat.mul sa sb) (Nat.mul sa sb) (Nat.mul sa sb) (Nat.mul sa sb)
    (Nat.sub (Nat.add sa sb) (Nat.mul sa sb)) (Nat.mul sa sb)

/--
Round the signed sum of two aligned magnitudes `A` and `Bv` with signs `sa` and `sb` (zero or
one) at the exponent `E`, in the direction `mode`. An exact zero sum gets the sign `zeroSumSign`.
-/
def sumSigned (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (B Em sa sb A Bv E guard special : Nat) : Nat :=
  (fun N S =>
    (fun dn dp =>
      round fmt mode B (Nat.sub 1 (Nat.sub 1 dn))
        (Nat.add (Nat.sub 1 (Nat.sub 1 dn))
          (Nat.mul (Nat.sub 1 (Nat.add dp dn)) (zeroSumSign mode sa sb)))
        (Nat.add dp dn) E Em guard special)
      (Nat.sub N (Nat.sub S N)) (Nat.sub (Nat.sub S N) N))
    (Nat.add (Nat.mul sa A) (Nat.mul sb Bv)) (Nat.add A Bv)

/--
Encoding of `(± ma * 2 ^ ha) + (± mb * 2 ^ hb)`, in units of
`2 ^ (fmt.minSubnormalExponent - Em)`, rounded in the direction `mode`. `G` clamps the exponent
gap and `B` bounds the bit length of the aligned sum.
-/
def sumAligned (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (G B Em sa ma ha sb mb hb guard special : Nat) : Nat :=
  (fun d1 d2 =>
    (fun ga gb =>
      sumSigned fmt mode B Em sa sb (Nat.shiftLeft ma ga) (Nat.shiftLeft mb gb)
        (Nat.sub (Nat.add ha d2) (Nat.add ga gb)) guard special)
      (Nat.sub d1 (Nat.sub d1 G)) (Nat.sub d2 (Nat.sub d2 G)))
    (Nat.sub ha hb) (Nat.sub hb ha)

/--
The reference rounding of the exact sum of two dyadic values in the direction `mode`: the zero of
`Model.zeroForExactSum` for an exact zero sum, and `Model.Internal.Directed.roundDyadic` of the sum
otherwise. This is the finite branch of every directed addition and fused multiply-add of the
reference.
-/
def roundedSum (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Numerics.Dyadic) :
    Model fmt :=
  if (Model.addDyadic a b).significand == 0 then
    Model.zeroForExactSum fmt mode a.negative b.negative
  else
    Model.Internal.Directed.roundDyadic fmt mode (Model.addDyadic a b)

/-! ## Rounding does not see a common shift -/

/-- Nearest-even quotient rounding is invariant under a common factor. -/
theorem roundQuotientEven_mul_right (n d c : Nat) (hc : 0 < c) :
    roundQuotientEven (n * c) (d * c) = roundQuotientEven n d := by
  have h1 : 2 * (n % d * c) < d * c ↔ 2 * (n % d) < d := by
    rw [← Nat.mul_assoc]; exact Nat.mul_lt_mul_right hc
  have h2 : d * c < 2 * (n % d * c) ↔ d < 2 * (n % d) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_lt_mul_right hc
  simp only [roundQuotientEven, Nat.mul_div_mul_right _ _ hc, Nat.mul_mod_mul_right, h1, h2]

/--
Rounding does not depend on how a value is split between significand and exponent: shifting the
significand left by `g` and lowering the exponent by `g` leaves the rounded value unchanged, in
every direction.
-/
theorem roundDyadic_shiftLeft (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (negative : Bool) (mag Ep Em g : Nat) (hg : g ≤ Ep) :
    Model.Internal.Directed.roundDyadic fmt mode
        ⟨negative, mag <<< g, ((Ep - g : Nat) : Int) - Em + fmt.minSubnormalExponent⟩ =
      Model.Internal.Directed.roundDyadic fmt mode
        ⟨negative, mag, (Ep : Int) - Em + fmt.minSubnormalExponent⟩ := by
  by_cases hmag : mag = 0
  · subst hmag
    simp [roundDyadic_zero]
  · have hshift : mag <<< g ≠ 0 := by simp [Nat.shiftLeft_eq, hmag]
    refine (Model.ofNatBits_toNatBits _).symm.trans
      (Eq.trans (congrArg (Model.ofNatBits (fmt := fmt)) ?_) (Model.ofNatBits_toNatBits _))
    rw [roundDyadic_bits fmt mode 0 negative (mag <<< g) (Ep - g) Em hshift _ _ rfl rfl,
      roundDyadic_bits fmt mode 0 negative mag Ep Em hmag _ _ rfl rfl,
      Nat.log2_shiftLeft_of_ne_zero mag g hmag]
    have ht : mag.log2 + g + 1 + (Ep - g) - (Em + fmt.fracWidth + 1) =
        mag.log2 + 1 + Ep - (Em + fmt.fracWidth + 1) := by omega
    rw [ht]
    generalize mag.log2 + 1 + Ep - (Em + fmt.fracWidth + 1) = t
    have hM : Model.Policy.roundQuot mode.toRoundingMode negative 0
          ((mag <<< g) <<< (Ep - g - (t + Em))) (2 ^ (t + Em - (Ep - g))) =
        Model.Policy.roundQuot mode.toRoundingMode negative 0
          (mag <<< (Ep - (t + Em))) (2 ^ (t + Em - Ep)) := by
      refine roundQuot_eq_of_cross mode negative 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _) ?_
      simp only [Nat.shiftLeft_eq, Nat.mul_assoc, ← Nat.pow_add]
      congr 2
      omega
    rw [hM]

/-! ## Operands far apart -/

/--
For operands far apart whose lower significand lies below the kept bits, the aligned sum for
rounding depends on the higher operand and the two signs only.
-/
private theorem aligned_far (keep : Nat) (hkeep : 1 ≤ keep) (low high : Numerics.Dyadic)
    (gap : Nat) (hexp : high.exponent = low.exponent + gap) (hgap : 2 * keep < gap)
    (hlow : low.significand < 2 ^ (gap - keep)) (hlow0 : low.significand ≠ 0)
    (hhigh0 : high.significand ≠ 0) :
    Model.addDyadicForRounding.aligned keep low high =
      { negative := high.negative
        significand :=
          if high.negative == low.negative then (high.significand <<< keep) ||| 1
          else (high.significand <<< keep - 1) ||| 1
        exponent := high.exponent - keep } := by
  have hgapNat : (high.exponent - low.exponent).toNat = gap := by omega
  have hlog : low.significand.log2 + 1 < gap := by
    have := (Nat.log2_lt hlow0).2 hlow
    omega
  have hlower : low.significand >>> (gap - keep) = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hlow
  unfold Model.addDyadicForRounding.aligned
  simp only [hgapNat, hgap, hlog, hhigh0, hlow0, ne_eq, not_false_eq_true, and_self, ite_true,
    hlower]
  have hexpEq : low.exponent + ((gap - keep : Nat) : Int) = high.exponent - keep := by omega
  simp [hexpEq]

/-- The reference rounding of a sum, through the sum that keeps `fracWidth + 3` bits. -/
theorem roundedSum_eq_forRounding (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (a b : Numerics.Dyadic) :
    roundedSum fmt mode a b =
      if (Model.addDyadicForRounding (fmt.fracWidth + 3) a b).significand == 0 then
        Model.zeroForExactSum fmt mode a.negative b.negative
      else
        Model.Internal.Directed.roundDyadic fmt mode
          (Model.addDyadicForRounding (fmt.fracWidth + 3) a b) := by
  unfold roundedSum
  simp only [beq_iff_eq,
    Model.addDyadicForRounding_significand_eq_zero_iff (fmt.fracWidth + 3) (by omega),
    Model.Internal.Directed.roundDyadic_addDyadicForRounding]

/--
Lowering a gap above `G` to `G` does not change the rounded sum in any direction, when the lower
significand has fewer than `G - (fracWidth + 3)` bits and `G` exceeds `2 * (fracWidth + 3)`: the
lower operand stays below the rounding position, and only its sign reaches the result.
-/
theorem roundedSum_far (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (low high : Numerics.Dyadic) (G : Nat)
    (hG : 2 * (fmt.fracWidth + 3) < G)
    (hsig : low.significand < 2 ^ (G - (fmt.fracWidth + 3)))
    (hlow0 : low.significand ≠ 0) (hhigh0 : high.significand ≠ 0)
    (hgap : low.exponent + G < high.exponent) :
    roundedSum fmt mode low high =
      roundedSum fmt mode { low with exponent := high.exponent - G } high := by
  rw [roundedSum_eq_forRounding, roundedSum_eq_forRounding]
  have haligned : Model.addDyadicForRounding (fmt.fracWidth + 3) low high =
      Model.addDyadicForRounding (fmt.fracWidth + 3)
        { low with exponent := high.exponent - G } high := by
    obtain ⟨gap, hgapEq⟩ : ∃ gap : Nat, high.exponent = low.exponent + gap :=
      ⟨(high.exponent - low.exponent).toNat, by omega⟩
    have hle : low.exponent ≤ high.exponent := by omega
    have hle' : high.exponent - (G : Int) ≤ high.exponent := by omega
    have hsig' : low.significand < 2 ^ (gap - (fmt.fracWidth + 3)) :=
      lt_of_lt_of_le hsig (Nat.pow_le_pow_right (by decide) (by omega))
    unfold Model.addDyadicForRounding
    rw [ite_eq_left hle, ite_eq_left hle',
      aligned_far _ (by omega) low high gap hgapEq (by omega) hsig' hlow0 hhigh0,
      aligned_far _ (by omega) { low with exponent := high.exponent - G } high G
        (by simp) hG hsig hlow0 hhigh0]
  rw [haligned]

/-! ## The signed sum -/

/--
The branch-free signed sum of `sumSigned` computes `addDyadicMagnitudes`: the magnitude, and for
a nonzero sum the exponent and the sign.
-/
private theorem sumSigned_fields (ls rs : Bool) (sa sb A Bv : Nat) (e : Int)
    (hsa : sa = signNat ls) (hsb : sb = signNat rs) :
    (Model.addDyadicMagnitudes ls rs A Bv e).significand =
        (A + Bv - (sa * A + sb * Bv) - (sa * A + sb * Bv)) +
          (sa * A + sb * Bv - (A + Bv - (sa * A + sb * Bv))) ∧
      ((Model.addDyadicMagnitudes ls rs A Bv e).significand ≠ 0 →
        (Model.addDyadicMagnitudes ls rs A Bv e).exponent = e ∧
          (1 - (1 - (sa * A + sb * Bv - (A + Bv - (sa * A + sb * Bv))))) =
            signNat (Model.addDyadicMagnitudes ls rs A Bv e).negative) ∧
      (Model.addDyadicMagnitudes ls rs A Bv e).significand ≤ A + Bv := by
  subst hsa hsb
  unfold Model.addDyadicMagnitudes signNat
  rcases Nat.lt_trichotomy A Bv with h | h | h
  · have hne : A ≠ Bv := by omega
    cases ls <;> cases rs <;>
      simp only [BEq.rfl, ↓reduceIte, Bool.false_eq_true, zero_mul, add_zero, tsub_zero, zero_tsub,
      ne_eq, Nat.add_eq_zero_iff, not_and, tsub_self, and_self,
      implies_true, Std.le_refl, beq_true, beq_iff_eq, hne, h, one_mul, zero_add,
      add_tsub_cancel_right, Nat.right_eq_add, true_and, tsub_le_iff_right, beq_false,
      Bool.not_true, add_tsub_cancel_left, Nat.left_eq_add, and_true] <;> omega
  · subst h
    cases ls <;> cases rs <;> simp only [BEq.rfl, ↓reduceIte, Bool.false_eq_true, zero_mul,
      add_zero, tsub_zero, zero_tsub, ne_eq, Nat.add_eq_zero_iff,
      and_self, tsub_self, implies_true, Std.le_refl, beq_true, Bool.and_true, one_mul, zero_add,
      add_tsub_cancel_right, not_true_eq_false, and_true, IsEmpty.forall_iff, zero_le, beq_false,
      Bool.not_true, Bool.and_false, true_and]
    omega
  · have hne : A ≠ Bv := by omega
    have hnlt : ¬ A < Bv := by omega
    cases ls <;> cases rs <;>
      simp only [BEq.rfl, ↓reduceIte, Bool.false_eq_true, zero_mul, add_zero, tsub_zero, zero_tsub,
      ne_eq, Nat.add_eq_zero_iff, not_and, tsub_self, and_self,
      implies_true, Std.le_refl, beq_true, beq_iff_eq, hne, hnlt, one_mul, zero_add,
      add_tsub_cancel_right, Nat.left_eq_add, true_and, tsub_le_iff_right, beq_false,
      Bool.not_true, add_tsub_cancel_left, Nat.right_eq_add, and_true] <;> omega

/-- `zeroSumSign` computes `IEEERoundingMode.zeroSumSign` on signs as naturals. -/
theorem zeroSumSign_eq (mode : Model.IEEERoundingMode) (ls rs : Bool) :
    zeroSumSign mode (signNat ls) (signNat rs) = signNat (mode.zeroSumSign ls rs) := by
  cases mode <;> cases ls <;> cases rs <;> rfl

/-- The sum of two magnitudes with a zero significand is the zero that both signs give. -/
private theorem addDyadicMagnitudes_zero (ls rs : Bool) (A Bv : Nat) (e : Int)
    (h : (Model.addDyadicMagnitudes ls rs A Bv e).significand = 0) :
    (ls = rs → A = 0 ∧ Bv = 0) ∧ (ls ≠ rs → A = Bv) := by
  unfold Model.addDyadicMagnitudes at h
  constructor
  · intro heq
    subst heq
    simp only [beq_self_eq_true, ite_true] at h
    omega
  · intro hne
    have hbeq : (ls == rs) = false := by cases ls <;> cases rs <;> simp_all
    by_contra hAB
    simp only [hbeq, Bool.false_eq_true, ite_false, beq_iff_eq, hAB] at h
    split_ifs at h <;> (dsimp only at h; omega)

/-! ## The aligned sum computes the reference rounding of the exact sum -/

/-- A nonzero guard selects the caller's special result. -/
theorem sumAligned_guard (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (G B Em sa ma ha sb mb hb guard special : Nat) (hguard : guard ≠ 0) :
    sumAligned fmt mode G B Em sa ma ha sb mb hb guard special = special := by
  unfold sumAligned sumSigned
  exact round_guard fmt mode _ _ _ _ _ _ _ _ hguard

/-- `zeroSumSign` is symmetric. -/
theorem zeroSumSign_comm (mode : Model.IEEERoundingMode) (sa sb : Nat) :
    zeroSumSign mode sa sb = zeroSumSign mode sb sa := by
  unfold zeroSumSign
  cases mode <;> simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_comm sa sb,
    Nat.add_comm sa sb]

/-- `sumAligned` is symmetric in its two operands. -/
theorem sumAligned_comm (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (G B Em sa ma ha sb mb hb guard special : Nat) :
    sumAligned fmt mode G B Em sa ma ha sb mb hb guard special =
      sumAligned fmt mode G B Em sb mb hb sa ma ha guard special := by
  unfold sumAligned sumSigned
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq']
  have hE : hb + (ha - hb) - (hb - ha - (hb - ha - G) + (ha - hb - (ha - hb - G))) =
      ha + (hb - ha) - (ha - hb - (ha - hb - G) + (hb - ha - (hb - ha - G))) := by omega
  rw [zeroSumSign_comm mode sb sa, Nat.add_comm (sb * _) (sa * _),
    Nat.add_comm (mb <<< _) (ma <<< _), hE]

/-- The reference rounding of a sum is symmetric in its operands. -/
theorem roundedSum_comm (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (a b : Numerics.Dyadic) : roundedSum fmt mode a b = roundedSum fmt mode b a := by
  unfold roundedSum Model.zeroForExactSum
  rw [Model.addDyadic_comm a b]
  have hsign : mode.zeroSumSign a.negative b.negative = mode.zeroSumSign b.negative a.negative := by
    cases mode <;> cases a.negative <;> cases b.negative <;> rfl
  rw [hsign]

/-- The core of `sumAligned_eq`, for a first operand whose exponent is not the larger one. -/
private theorem sumAligned_eq_of_le (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (G B Em : Nat) (a b : Numerics.Dyadic) (sa ma ha sb mb hb special : Nat)
    (hG : 2 * (fmt.fracWidth + 3) < G)
    (hma : ma < 2 ^ (G - (fmt.fracWidth + 3)))
    (hbits : (ma + mb) * 2 ^ G < 2 ^ B)
    (hsa : sa = signNat a.negative) (hsb : sb = signNat b.negative)
    (hsiga : a.significand = ma) (hsigb : b.significand = mb)
    (hexpa : ma ≠ 0 → a.exponent = (ha : Int) - Em + fmt.minSubnormalExponent)
    (hexpb : mb ≠ 0 → b.exponent = (hb : Int) - Em + fmt.minSubnormalExponent)
    (hle : ha ≤ hb) (hlowb : mb = 0 → hb ≤ ha) :
    sumAligned fmt mode G B Em sa ma ha sb mb hb 0 special =
      (roundedSum fmt mode a b).toNatBits := by
  obtain ⟨an, asig, ae⟩ := a
  obtain ⟨bn, bsig, be⟩ := b
  dsimp only at hsa hsb hsiga hsigb hexpa hexpb
  subst hsiga hsigb
  -- The clamped shift of the second operand and the exponent of the aligned sum.
  obtain ⟨gb, hgb⟩ : ∃ gb, gb = hb - ha - (hb - ha - G) := ⟨_, rfl⟩
  have hgbG : gb ≤ G := by omega
  have hgbhb : gb ≤ hb := by omega
  have hfields := sumSigned_fields an bn sa sb asig (bsig <<< gb)
    (((hb - gb : Nat) : Int) - Em + fmt.minSubnormalExponent) hsa hsb
  obtain ⟨hsig, hnonzero, hbound⟩ := hfields
  have hshiftBound : bsig <<< gb ≤ bsig * 2 ^ G := by
    rw [Nat.shiftLeft_eq]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hgbG)
  have hmagBound : asig + bsig <<< gb < 2 ^ B := by
    have h1 : asig ≤ asig * 2 ^ G := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    have h2 : (asig + bsig) * 2 ^ G = asig * 2 ^ G + bsig * 2 ^ G := by ring
    omega
  -- The aligned sum, rounded: the zero of both signs for an exact zero, the rounding otherwise.
  have hstep :
      sumAligned fmt mode G B Em sa asig ha sb bsig hb 0 special =
        (if (Model.addDyadicMagnitudes an bn asig (bsig <<< gb)
              (((hb - gb : Nat) : Int) - Em + fmt.minSubnormalExponent)).significand == 0 then
            Model.zeroForExactSum fmt mode an bn
          else
            Model.Internal.Directed.roundDyadic fmt mode
              (Model.addDyadicMagnitudes an bn asig (bsig <<< gb)
                (((hb - gb : Nat) : Int) - Em + fmt.minSubnormalExponent))).toNatBits := by
    unfold sumAligned sumSigned
    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq']
    have h0 : ha - hb = 0 := by omega
    have hE : ha + (hb - ha) - (0 + gb) = hb - gb := by omega
    simp only [h0, Nat.zero_sub, Nat.shiftLeft_zero, ← hgb, hE, beq_iff_eq]
    generalize hdn : sa * asig + sb * bsig <<< gb -
      (asig + bsig <<< gb - (sa * asig + sb * bsig <<< gb)) = dn at hsig hnonzero ⊢
    generalize hdp : asig + bsig <<< gb - (sa * asig + sb * bsig <<< gb) -
      (sa * asig + sb * bsig <<< gb) = dp at hsig ⊢
    have hBpos : 0 < 2 ^ B := Nat.two_pow_pos B
    by_cases hzero : (Model.addDyadicMagnitudes an bn asig (bsig <<< gb)
        (((hb - gb : Nat) : Int) - Em + fmt.minSubnormalExponent)).significand = 0
    · have hdn0 : dn = 0 := by omega
      have hdp0 : dp = 0 := by omega
      subst hdn0 hdp0
      rw [ite_eq_left hzero, Model.zeroForExactSum,
        ← roundDyadic_zero fmt mode (mode.zeroSumSign an bn) 0]
      refine round_eq fmt mode B _ _ _ (hb - gb) Em special _ hBpos rfl ?_ ?_ ?_
      · dsimp only
        rw [hsa, hsb, zeroSumSign_eq]
        simp
      · intro hne
        exact absurd rfl hne
      · intro hne
        exact absurd rfl hne
    · rw [ite_eq_right hzero]
      refine round_eq fmt mode B _ _ _ (hb - gb) Em special _ ?_ hsig ?_ ?_ ?_
      · rw [← hsig]
        omega
      · have h1 := (hnonzero hzero).2
        have h2 : 1 - (dp + dn) = 0 := by omega
        rw [h2, Nat.zero_mul, Nat.add_zero]
        exact h1
      · intro _
        exact (hnonzero hzero).1
      · intro _
        have h2 : 1 - (dp + dn) = 0 := by omega
        rw [h2, Nat.zero_mul, Nat.add_zero]
  rw [hstep]
  congr 1
  by_cases hb0 : bsig = 0
  · -- A zero second operand: the exponents agree and nothing is shifted.
    subst hb0
    have hgb0 : gb = 0 := by have := hlowb rfl; lia
    subst hgb0
    by_cases ha0 : asig = 0
    · subst ha0
      cases an <;> cases bn <;>
        simp [roundedSum, Model.addDyadicMagnitudes, ← Model.Internal.addDyadic_eq,
          Model.Internal.addDyadic]
    · have hae := hexpa ha0
      have hhb : hb = ha := by have := hlowb rfl; omega
      subst hhb
      subst hae
      have hne : ¬ asig = 0 := ha0
      cases an <;> cases bn <;>
        simp [roundedSum, Model.addDyadicMagnitudes, ← Model.Internal.addDyadic_eq,
          Model.Internal.addDyadic, hne]
  · have hbe := hexpb hb0
    subst hbe
    by_cases ha0 : asig = 0
    · -- A zero first operand: the sum is the second one, shifted, which rounds the same.
      subst ha0
      have hshift0 : bsig <<< gb ≠ 0 := by simp [Nat.shiftLeft_eq, hb0]
      have hpos : 0 < bsig <<< gb := Nat.pos_of_ne_zero hshift0
      have hmagnitudes :
          Model.addDyadicMagnitudes an bn 0 (bsig <<< gb)
              (((hb - gb : Nat) : Int) - Em + fmt.minSubnormalExponent) =
            ⟨bn, bsig <<< gb, ((hb - gb : Nat) : Int) - Em + fmt.minSubnormalExponent⟩ := by
        cases an <;> cases bn <;>
          simp [Model.addDyadicMagnitudes, hshift0.symm, hpos]
      rw [hmagnitudes]
      simp only [beq_iff_eq, hshift0, ite_false]
      rw [roundDyadic_shiftLeft fmt mode bn bsig hb Em gb hgbhb]
      simp [roundedSum, ← Model.Internal.addDyadic_eq, Model.Internal.addDyadic, hb0]
    · have hae := hexpa ha0
      subst hae
      have hexpLe : (ha : Int) - Em + fmt.minSubnormalExponent ≤
          (hb : Int) - Em + fmt.minSubnormalExponent := by omega
      by_cases hfar : hb - ha ≤ G
      · -- The gap is within `G`: the alignment is the exact one.
        have hgbEq : gb = hb - ha := by lia
        have hshift : ((hb : Int) - Em + fmt.minSubnormalExponent -
            ((ha : Int) - Em + fmt.minSubnormalExponent)).toNat = gb := by omega
        have hbase : ((hb - gb : Nat) : Int) - Em + fmt.minSubnormalExponent =
            (ha : Int) - Em + fmt.minSubnormalExponent := by omega
        simp only [roundedSum, ← Model.Internal.addDyadic_eq, Model.Internal.addDyadic,
          beq_iff_eq, ha0, hb0, ite_false, hexpLe, ite_true, hshift, hbase, Nat.shiftLeft_eq']
      · -- The gap exceeds `G`: lowering it to `G` does not change the rounding.
        have hgbEq : gb = G := by lia
        subst hgbEq
        rw [roundedSum_far fmt mode
          ⟨an, asig, (ha : Int) - Em + fmt.minSubnormalExponent⟩
          ⟨bn, bsig, (hb : Int) - Em + fmt.minSubnormalExponent⟩ gb hG hma ha0 hb0
          (by dsimp only; omega)]
        have hexpLe' : (hb : Int) - Em + fmt.minSubnormalExponent - (gb : Int) ≤
            (hb : Int) - Em + fmt.minSubnormalExponent := by omega
        have hshift : ((hb : Int) - Em + fmt.minSubnormalExponent -
            ((hb : Int) - Em + fmt.minSubnormalExponent - (gb : Int))).toNat = gb := by omega
        have hbase : ((hb - gb : Nat) : Int) - Em + fmt.minSubnormalExponent =
            (hb : Int) - Em + fmt.minSubnormalExponent - (gb : Int) := by omega
        simp only [roundedSum, ← Model.Internal.addDyadic_eq, Model.Internal.addDyadic,
          beq_iff_eq, ha0, hb0, ite_false, hexpLe', ite_true, hshift, hbase, Nat.shiftLeft_eq']

/--
`sumAligned` computes the encoding of the reference rounding of the exact dyadic sum
(`roundedSum`), for every format descriptor and every rounding direction.

`a` and `b` are the exact dyadic operands: signs `sa` and `sb`, significands `ma` and `mb`, and
for a nonzero significand the exponent `h - Em + fmt.minSubnormalExponent`. A zero operand must
not have the larger exponent. `G` exceeds `2 * (fracWidth + 3)`, both significands have fewer than
`G - (fracWidth + 3)` bits, and `B` bounds the aligned sum.
-/
theorem sumAligned_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (G B Em : Nat)
    (a b : Numerics.Dyadic) (sa ma ha sb mb hb special : Nat)
    (hG : 2 * (fmt.fracWidth + 3) < G)
    (hma : ma < 2 ^ (G - (fmt.fracWidth + 3))) (hmb : mb < 2 ^ (G - (fmt.fracWidth + 3)))
    (hbits : (ma + mb) * 2 ^ G < 2 ^ B)
    (hsa : sa = signNat a.negative) (hsb : sb = signNat b.negative)
    (hsiga : a.significand = ma) (hsigb : b.significand = mb)
    (hexpa : ma ≠ 0 → a.exponent = (ha : Int) - Em + fmt.minSubnormalExponent)
    (hexpb : mb ≠ 0 → b.exponent = (hb : Int) - Em + fmt.minSubnormalExponent)
    (hlowa : ma = 0 → ha ≤ hb) (hlowb : mb = 0 → hb ≤ ha) :
    sumAligned fmt mode G B Em sa ma ha sb mb hb 0 special =
      (roundedSum fmt mode a b).toNatBits := by
  by_cases hle : ha ≤ hb
  · exact sumAligned_eq_of_le fmt mode G B Em a b sa ma ha sb mb hb special hG hma hbits hsa hsb
      hsiga hsigb hexpa hexpb hle hlowb
  · rw [sumAligned_comm, roundedSum_comm]
    exact sumAligned_eq_of_le fmt mode G B Em b a sb mb hb sa ma ha special hG hmb
      (by rw [Nat.add_comm]; exact hbits) hsb hsa hsigb hsiga hexpb hexpa (by omega) hlowa

/-- In the nearest-even direction the reference rounding of a sum is `roundDyadic` of the sum. -/
theorem roundedSum_nearest (fmt : FloatFormat) (a b : Numerics.Dyadic) :
    roundedSum fmt .nearest a b = Model.roundDyadic fmt (Model.addDyadic a b) := by
  unfold roundedSum
  by_cases hzero : (Model.addDyadic a b).significand = 0
  · have hsign : (Model.addDyadic a b).negative = (a.negative && b.negative) := by
      rw [← Model.Internal.addDyadic_eq] at hzero ⊢
      unfold Model.Internal.addDyadic at hzero ⊢
      split_ifs at hzero ⊢ with h1 h2 h3 h4
      · rfl
      · simp_all
      · simp_all
      · have := addDyadicMagnitudes_zero _ _ _ _ _ hzero
        dsimp only at this ⊢
        unfold Model.addDyadicMagnitudes
        cases ha : a.negative <;> cases hb : b.negative <;> simp_all
      · have := addDyadicMagnitudes_zero _ _ _ _ _ hzero
        dsimp only at this ⊢
        unfold Model.addDyadicMagnitudes
        cases ha : a.negative <;> cases hb : b.negative <;> simp_all
    have hround := roundDyadic_zero fmt .nearest (Model.addDyadic a b).negative
      (Model.addDyadic a b).exponent
    rw [← hzero] at hround
    simp only [beq_iff_eq, hzero, ite_true, Model.zeroForExactSum,
      Model.IEEERoundingMode.zeroSumSign]
    rw [← hsign]
    exact hround.symm
  · simp only [beq_iff_eq, hzero, ite_false]
    rfl

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
