/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Add
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Mul

/-!
# Rounding and leading-bit bounds for short arithmetic paths

Guarded packing agrees with the general rounder. Leading-bit and cancellation bounds identify the
normalization shift, while the rounding-increment identities justify parity, distant remainders
and carry paths.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics
open FloatLib.Numerics.Kernel (bitLength bitLength_eq searchLength searchLength_eq)

/-- A nonzero guard makes `roundQuotient` return the special result. -/
theorem roundQuotient_guard (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign zeroSign guard special t num den : Nat) (hguard : guard ≠ 0) :
    roundQuotient fmt mode sign zeroSign guard special t num den = special := by
  unfold roundQuotient
  simp only [pack_eq, ne_eq, hguard, not_false_eq_true, ite_true]

/-- With a zero guard `roundQuotient` does not use the special result. -/
theorem roundQuotient_special (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign zeroSign special special' t num den : Nat) :
    roundQuotient fmt mode sign zeroSign 0 special t num den =
      roundQuotient fmt mode sign zeroSign 0 special' t num den := by
  unfold roundQuotient
  simp only [pack_eq, ne_eq, not_true_eq_false, ite_false]

/-- A nonzero guard makes `roundAt` return the special result. -/
theorem roundAt_guard (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign zeroSign mag Ep Em guard special length : Nat) (hguard : guard ≠ 0) :
    roundAt fmt mode sign zeroSign mag Ep Em guard special length = special := by
  rw [roundAt_def]
  exact roundQuotient_guard fmt mode _ _ _ _ _ _ _ hguard

/-- With a zero guard `roundAt` does not use the special result. -/
theorem roundAt_special (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign zeroSign mag Ep Em special special' length : Nat) :
    roundAt fmt mode sign zeroSign mag Ep Em 0 special length =
      roundAt fmt mode sign zeroSign mag Ep Em 0 special' length := by
  rw [roundAt_def, roundAt_def]
  exact roundQuotient_special fmt mode _ _ _ _ _ _ _

/-- A nonzero guard makes `packExact` return the special result. -/
theorem packExact_guard (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign zeroSign mag e guard special length : Nat) (hguard : guard ≠ 0) :
    packExact fmt mode sign zeroSign mag e guard special length = special := by
  unfold packExact
  simp only [pack_eq, ne_eq, hguard, not_false_eq_true, ite_true]

/--
The exact normalization is the general rounding with the bit length taken over any bound `B`,
for a magnitude of at most `fracWidth + 1` bits: the two agree in every direction, and neither
uses its special result when the guard is zero.
-/
theorem packExact_eq_round (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (B sign zeroSign mag e special special' : Nat) (hmag : mag < 2 ^ (fmt.fracWidth + 1))
    (hB : fmt.fracWidth + 1 ≤ B) :
    packExact fmt mode sign zeroSign mag e 0 special (bitLength (Nat.succ fmt.fracWidth) mag) =
      round fmt mode B sign zeroSign mag e 0 0 special' := by
  have hbits : mag < 2 ^ B := lt_of_lt_of_le hmag (Nat.pow_le_pow_right (by decide) hB)
  have hlength : bitLength (Nat.succ fmt.fracWidth) mag = bitLength B mag := by
    rw [bitLength_eq hmag, bitLength_eq hbits]
  have hle : bitLength B mag ≤ fmt.fracWidth + 1 := by
    rw [bitLength_eq hbits]
    split
    · omega
    · rename_i hne
      have := (Nat.log2_lt hne).2 hmag
      omega
  unfold round
  rw [hlength, roundAt_exact fmt mode _ _ _ _ _ _ _ hle]
  unfold packExact
  simp only [pack_eq, ne_eq, not_true_eq_false, ite_false]

/--
When the three leading bits of an aligned sum `S` of ordered operands do not settle its leading
bit, the sum has at most `F + 1` bits: the exponent gap `g` is then at most one and the leading
bits cancelled, or the operands share their exponent. `A` is the larger operand shifted by the
gap and `m` the smaller significand.
-/
theorem cancelled_lt {F g S A m : Nat} (hF : 0 < F) (hS : A - m ≤ S)
    (hA : g ≠ 0 → 2 ^ F * 2 ^ g ≤ A) (hm : m < 2 ^ (F + 1))
    (hfast : S >>> (g + F - 1) *
      (g + ((1 - (1 - (S >>> (g + F - 1)) >>> 1)) + (S >>> (g + F - 1)) >>> 2)) = 0) :
    S < 2 ^ (F + 1) := by
  have hsplit : 2 ^ (F + 1) = 2 * 2 ^ F := by rw [Nat.pow_succ]; omega
  have hFpred : 2 ^ F = 2 * 2 ^ (F - 1) := by
    rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hF]
  have hhalves : ∀ v : Nat, v >>> 1 = v / 2 ∧ v >>> 2 = v / 4 := fun v =>
    ⟨by rw [Nat.shiftRight_eq_div_pow], by rw [Nat.shiftRight_eq_div_pow]⟩
  rw [Nat.shiftRight_eq_div_pow] at hfast
  generalize hU : S / 2 ^ (g + F - 1) = u at hfast
  rw [(hhalves u).1, (hhalves u).2] at hfast
  rcases Nat.mul_eq_zero.1 hfast with hu | hgk
  · -- The top three bits are zero.
    have hlt : S < 2 ^ (g + F - 1) := by
      by_contra hge
      have hpos : 0 < S / 2 ^ (g + F - 1) :=
        Nat.div_pos (Nat.le_of_not_lt hge) (Nat.two_pow_pos _)
      omega
    by_cases hg : g ≤ 2
    · exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
    · exfalso
      have hbig := hA (by omega)
      have hP : 2 ^ F * 2 ^ g = 2 * 2 ^ (g + F - 1) := by
        rw [← Nat.pow_add, ← Nat.pow_succ']
        congr 1
        omega
      have hQ : 2 * 2 ^ (F + 1) ≤ 2 ^ (g + F - 1) := by
        rw [← Nat.pow_succ']
        exact Nat.pow_le_pow_right (by decide) (by omega)
      omega
  · -- The operands share their exponent and the sum stays below the leading bit.
    have hg : g = 0 := by omega
    have hu1 : u ≤ 1 := by omega
    subst hg
    rw [Nat.zero_add] at hU
    have hlt : S < 2 * 2 ^ (F - 1) := by
      by_contra hge
      have h2 : 2 ≤ S / 2 ^ (F - 1) :=
        (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 (Nat.le_of_not_lt hge)
      omega
    omega

/-- The leading bit of a number known up to one position: bit `k` or bit `k + 1`. -/
theorem log2_eq_add_carry {S k : Nat} (hlow : 2 ^ k ≤ S) (hhigh : S < 2 ^ (k + 2)) :
    S.log2 = k + S >>> (k + 1) := by
  have hpos : S ≠ 0 := by have := Nat.two_pow_pos k; omega
  have hsplit : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; ac_rfl
  rw [Nat.shiftRight_eq_div_pow]
  by_cases hc : S < 2 ^ (k + 1)
  · rw [Nat.div_eq_of_lt hc, Nat.add_zero]
    exact (Nat.log2_eq_iff hpos).2 ⟨hlow, hc⟩
  · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    exact (Nat.log2_eq_iff hpos).2 ⟨by omega, hhigh⟩

/--
The leading bit of a number known up to two positions above bit `K`: its offset from `K` is
read off the three bits from `K` on.
-/
theorem log2_eq_add_offset {K S : Nat} (hlow : 2 ^ K ≤ S) (hhigh : S < 2 ^ (K + 3)) :
    S.log2 = K + ((1 - (1 - (S >>> K) >>> 1)) + (S >>> K) >>> 2) := by
  have hpos : S ≠ 0 := by have := Nat.two_pow_pos K; omega
  have hKpos : 0 < 2 ^ K := Nat.two_pow_pos K
  have h3 : 2 ^ (K + 3) = 2 ^ K * 8 := by rw [Nat.pow_add]
  have key : ∀ u : Nat, 1 ≤ u → u < 8 →
      2 ^ ((1 - (1 - u >>> 1)) + u >>> 2) ≤ u ∧ u < 2 ^ ((1 - (1 - u >>> 1)) + u >>> 2 + 1) := by
    intro u h1 h8
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5 ∨ u = 6 ∨ u = 7 := by omega
    all_goals decide
  obtain ⟨u, hu⟩ : ∃ u, u = S >>> K := ⟨_, rfl⟩
  rw [← hu]
  rw [Nat.shiftRight_eq_div_pow] at hu
  have hu1 : 1 ≤ u := by
    rw [hu]
    exact (Nat.le_div_iff_mul_le hKpos).2 (by omega)
  have hu8 : u < 8 := by
    rw [hu]
    exact (Nat.div_lt_iff_lt_mul hKpos).2 (by omega)
  obtain ⟨hk1, hk2⟩ := key u hu1 hu8
  generalize (1 - (1 - u >>> 1)) + u >>> 2 = k at hk1 hk2
  have hfloor : u * 2 ^ K ≤ S := by rw [hu]; exact Nat.div_mul_le_self _ _
  have hceil : S < (u + 1) * 2 ^ K := by
    rw [hu]
    exact Nat.lt_mul_of_div_lt (Nat.lt_succ_self _) hKpos
  rw [Nat.log2_eq_iff hpos]
  constructor
  · calc 2 ^ (K + k) = 2 ^ k * 2 ^ K := by rw [Nat.pow_add, Nat.mul_comm]
      _ ≤ u * 2 ^ K := Nat.mul_le_mul_right _ hk1
      _ ≤ S := hfloor
  · calc S < (u + 1) * 2 ^ K := hceil
      _ ≤ 2 ^ (k + 1) * 2 ^ K := Nat.mul_le_mul_right _ hk2
      _ = 2 ^ (K + k + 1) := by rw [← Nat.pow_add]; congr 1; omega

/--
The offset of the leading bit of an aligned sum whose significand `M` has its leading bit at
position `width + c`, read off the three bits from `width - 1` on: it is `c + 1`.
-/
theorem offset_of_significand {width M c : Nat} (hwidth : 0 < width) (hc : c ≤ 1)
    (hlow : 2 ^ (width + c) ≤ M) (hhigh : M < 2 ^ (width + c + 1)) :
    M >>> (width - 1) ≠ 0 ∧
      (1 - (1 - (M >>> (width - 1)) >>> 1)) + (M >>> (width - 1)) >>> 2 = c + 1 := by
  obtain ⟨f, rfl⟩ : ∃ f, width = f + 1 := ⟨width - 1, by omega⟩
  have hFpos : 0 < 2 ^ f := Nat.two_pow_pos f
  rw [Nat.add_sub_cancel, Nat.shiftRight_eq_div_pow]
  have hlow' : 2 ^ (c + 1) ≤ M / 2 ^ f := by
    apply (Nat.le_div_iff_mul_le hFpos).2
    calc 2 ^ (c + 1) * 2 ^ f = 2 ^ (f + 1 + c) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ M := hlow
  have hhigh' : M / 2 ^ f < 2 ^ (c + 2) := by
    apply (Nat.div_lt_iff_lt_mul hFpos).2
    calc M < 2 ^ (f + 1 + c + 1) := hhigh
      _ = 2 ^ (c + 2) * 2 ^ f := by rw [← Nat.pow_add]; congr 1; omega
  generalize M / 2 ^ f = u at hlow' hhigh'
  obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
  · obtain rfl | rfl : u = 2 ∨ u = 3 := by
      simp only [Nat.zero_add, Nat.pow_one] at hlow'
      have : (2 : Nat) ^ (0 + 2) = 4 := by decide
      omega
    all_goals decide
  · obtain rfl | rfl | rfl | rfl : u = 4 ∨ u = 5 ∨ u = 6 ∨ u = 7 := by
      omega
    all_goals decide

/-- A decoded significand, from any exponent-and-fraction word, is below `2 ^ (fracWidth + 1)`. -/
theorem significand_lt (width u : Nat) :
    u - (u >>> width - 1) <<< width < 2 ^ (width + 1) := by
  have hpos : 0 < 2 ^ width := Nat.two_pow_pos _
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hdiv := Nat.div_add_mod u (2 ^ width)
  have hmod := Nat.mod_lt u hpos
  generalize u / 2 ^ width = e at hdiv ⊢
  generalize u % 2 ^ width = f at hdiv hmod
  rcases e with _ | e
  · simp only [mul_zero, zero_add, zero_tsub, zero_mul, tsub_zero, gt_iff_lt] at hdiv ⊢; omega
  · have hexpand : 2 ^ width * (e + 1) = e * 2 ^ width + 2 ^ width := by rw [mul_add]; ac_rfl
    simp only [Nat.add_sub_cancel]
    omega

/-- The rounding increment reads only the parity of the floor of the quotient. -/
theorem roundUp_parity (mode : Model.IEEERoundingMode) (sign q q' r den : Nat)
    (h : q % 2 = q' % 2) : roundUp mode sign q r den = roundUp mode sign q' r den := by
  unfold roundUp
  simp only [Nat.land_eq, Nat.and_one_is_mod, h]

/--
A remainder far below two denominators gives the same rounding increment for both: zero in the
nearest directions, and the directed increment, which does not read the denominator.
-/
theorem roundUp_far (mode : Model.IEEERoundingMode) (sign q r den den' : Nat)
    (h : 2 * r < den) (h' : 2 * r < den') :
    roundUp mode sign q r den = roundUp mode sign q r den' := by
  have hparity : q % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold roundUp
  cases mode <;> simp only [Nat.add_eq, Nat.sub_eq, Nat.land_eq, Nat.and_one_is_mod, div_def]
  · rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  · rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

/-- A quotient without a remainder does not round up, in any direction. -/
theorem roundUp_exact (mode : Model.IEEERoundingMode) (sign q den : Nat) :
    roundUp mode sign q 0 den = 0 := by
  unfold roundUp
  cases mode
  · change (0 + 0 + (q &&& 1) - 1) / den = 0
    have : q &&& 1 ≤ 1 := Nat.and_le_right
    rw [show 0 + 0 + (q &&& 1) - 1 = 0 by omega, Nat.zero_div]
  · change (0 + 0) / den = 0
    exact Nat.zero_div den
  all_goals rfl

/-- A remainder below half of two denominators rounds the same way over both. -/
theorem roundUp_small (mode : Model.IEEERoundingMode) (sign q r den den' : Nat)
    (h : r + r < den) (h' : r + r < den') :
    roundUp mode sign q r den = roundUp mode sign q r den' := by
  unfold roundUp
  have hq : q &&& 1 ≤ 1 := Nat.and_le_right
  cases mode <;> simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.land_eq, div_def]
  · rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  · rw [Nat.div_eq_of_lt h, Nat.div_eq_of_lt h']

/--
The remainder of a sum that carries, a lost bit above a remainder below half of it, rounds the
same way at every scale that leaves the remainder below half of the bit.
-/
theorem roundUp_carry (mode : Model.IEEERoundingMode) (sign q bit r g g' : Nat)
    (hbit : bit ≤ 1) (h : r + r < 2 ^ g) (h' : r + r < 2 ^ g') :
    roundUp mode sign q (bit <<< g + r) (2 ^ (g + 1)) =
      roundUp mode sign q (bit <<< g' + r) (2 ^ (g' + 1)) := by
  obtain rfl | rfl : bit = 0 ∨ bit = 1 := by omega
  · rw [Nat.zero_shiftLeft, Nat.zero_shiftLeft, Nat.zero_add]
    refine roundUp_small mode sign q r _ _ ?_ ?_
    · rw [Nat.pow_succ]; omega
    · rw [Nat.pow_succ]; omega
  · have hq : q &&& 1 ≤ 1 := Nat.and_le_right
    have key : ∀ P : Nat, r + r < P →
        (P + r + (P + r) + (q &&& 1) - 1) / (P + P) = (if r + r + (q &&& 1) = 0 then 0 else 1) ∧
          (P + r + (P + r)) / (P + P) = 1 ∧ 1 - (1 - (P + r)) = 1 := by
      intro P hP
      refine ⟨?_, Nat.div_eq_of_lt_le (by omega) (by omega), by omega⟩
      split
      · exact Nat.div_eq_of_lt (by omega)
      · exact Nat.div_eq_of_lt_le (by omega) (by omega)
    obtain ⟨hn, ha, hd⟩ := key (2 ^ g) h
    obtain ⟨hn', ha', hd'⟩ := key (2 ^ g') h'
    unfold roundUp
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul,
      show 2 ^ (g + 1) = 2 ^ g + 2 ^ g by rw [Nat.pow_succ]; omega,
      show 2 ^ (g' + 1) = 2 ^ g' + 2 ^ g' by rw [Nat.pow_succ]; omega]
    cases mode <;>
      simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.land_eq, div_def, hn, hn', ha, ha', hd,
        hd']

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
