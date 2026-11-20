/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.KernelPath.Proof
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Literal

/-!
# The kernel P3109 rounding computes the reference precision rounding

P3109 Interim Report v4.1 (14 September 2026), §§4.7.3 and 4.7.4, an unapproved draft. The
reference `Format.roundFiniteRatToPrecision` reads the numerator and the denominator of a
normalized rational. The kernel rounds a ratio of natural numbers as it is given:

* `floorLog2_eq`: the binary exponent of a ratio from the bit lengths of its terms and one
  comparison;
* `quantumOf_eq`: `quantumOf` is the quantum exponent of the report, with its bias;
* `roundAway_eq`: `roundAway` is the reference decision in each of the nine modes, for every
  random word, and does not see a common factor of the remainder and the denominator;
* `roundFiniteRatToPrecision_eq`: the reference rounding of `(-1) ^ s * n / d` is the dyadic
  with the significand `roundedOf` and the exponent `quantumOf`, for every descriptor, every
  mode and every ratio with `n ≠ 0` and `d ≠ 0`, whatever common factor `n` and `d` have.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.KernelPath

open FloatLib.Numerics FloatLib.Numerics.Kernel
open FloatLib.Floats.Formats.P3109
open FloatLib.Floats.Formats.BinaryInterchange

/-! ## The quantum -/

/-- The binary exponent of a ratio of nonzero natural numbers: the difference of the positions
of the leading bits, less one when the aligned numerator is below the aligned denominator. -/
theorem floorLog2_eq (n d : Nat) (hn : n ≠ 0) (hd : d ≠ 0) :
    RationalBinary.floorLog2 n d =
      ((n.log2 + 1 - (if n * 2 ^ d.log2 < d * 2 ^ n.log2 then 1 else 0) : Nat) : Int) -
        ((d.log2 + 1 : Nat) : Int) := by
  have hshift := KernelPath.floorLog2_shiftLeft n d d.log2 n.log2 hn hd
  have hnlow := Nat.log2_self_le hn
  have hnup : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have hdlow := Nat.log2_self_le hd
  have hdup : d < 2 ^ (d.log2 + 1) := Nat.lt_log2_self
  have hN : 2 ^ (n.log2 + d.log2) ≤ n <<< d.log2 ∧ n <<< d.log2 < 2 ^ (n.log2 + d.log2 + 1) := by
    rw [Nat.shiftLeft_eq]
    constructor
    · rw [Nat.pow_add]
      exact Nat.mul_le_mul_right _ hnlow
    · rw [show n.log2 + d.log2 + 1 = n.log2 + 1 + d.log2 by omega, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right hnup (Nat.two_pow_pos _)
  have hD : 2 ^ (n.log2 + d.log2) ≤ d <<< n.log2 ∧ d <<< n.log2 < 2 ^ (n.log2 + d.log2 + 1) := by
    rw [Nat.shiftLeft_eq]
    constructor
    · rw [Nat.add_comm, Nat.pow_add]
      exact Nat.mul_le_mul_right _ hdlow
    · rw [show n.log2 + d.log2 + 1 = d.log2 + 1 + n.log2 by omega, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right hdup (Nat.two_pow_pos _)
  rw [Model.FiniteQuotientRound.floorLog2_eq_of_normal (n.log2 + d.log2) _ _ hN hD,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq] at hshift
  split_ifs at hshift ⊢ <;> omega

/-- The bit length of a nonzero number less one is the position of its leading bit. -/
theorem size_sub_one {n : Nat} (hn : n ≠ 0) : Nat.sub (size n) 1 = n.log2 := by
  change size n - 1 = _
  rw [size_eq_log2, ite_eq_right hn]
  omega

/--
P3109 interim report v4.1, §4.7.3: `quantumOf` is the quantum exponent `max (⌊log₂ (n / d)⌋) (1
    - B) - P + 1`
of the ratio plus the bias `log₂ d + 1 + B + P`, for every exponent bias `B` and precision `P`.
-/
theorem quantumOf_eq (B P n d : Nat) (hn : n ≠ 0) (hd : d ≠ 0) :
    ((quantumOf B n d : Nat) : Int) - ((d.log2 + 1 + (B + P) : Nat) : Int) =
      max (RationalBinary.floorLog2 n d) (1 - (B : Int)) - (P : Int) + 1 := by
  rw [floorLog2_eq n d hn hd]
  unfold quantumOf
  rw [size_sub_one hn, size_sub_one hd]
  kernel_notation
  simp only [Nat.add_one_le_iff]
  split_ifs <;> omega

/-! ## The rounding decision -/

/-- The nearest-even quotient does not see a common factor. -/
theorem nearestEven_mul (a b c : Nat) (hc : 0 < c) :
    nearestEven (a * c) (b * c) = roundQuotientEven a b := by
  unfold nearestEven roundQuotientEven
  kernel_notation
  rw [Nat.mul_div_mul_right a b hc, Nat.mul_mod_mul_right, Nat.and_one_is_mod]
  have h1 : (b * c ≤ 2 * (a % b * c)) ↔ (b ≤ 2 * (a % b)) := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right_iff hc
  have h2 : (b * c = 2 * (a % b * c)) ↔ (b = 2 * (a % b)) := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_left_inj (Nat.ne_of_gt hc)
  simp only [h1, h2, beq_iff_eq]
  generalize a / b = q
  generalize a % b = r
  split_ifs <;> omega

/--
P3109 interim report v4.1, §4.7.4: `roundAway` is the reference rounding decision in each of the
    nine modes,
for every supplied random word, sign and parity, and for every positive common factor `c` of
the remainder and the denominator.
-/
theorem roundAway_eq (mode : RoundingMode) (negative even : Bool) (rem den c : Nat)
    (hc : 0 < c) :
    roundAway (modeIndex mode) (modeWidth mode) (modeRandom mode) (if negative then 1 else 0)
        (if even then 1 else 0) (rem * c) (den * c) =
      if Format.Internal.roundRationalAwayWithParity mode negative even rem den then 1
      else 0 := by
  have h0 : (rem * c = 0) ↔ (rem = 0) := by
    constructor
    · intro h
      rcases Nat.mul_eq_zero.1 h with h | h
      · exact h
      · omega
    · rintro rfl
      exact Nat.zero_mul c
  have h1 : (den * c ≤ 2 * (rem * c)) ↔ (den ≤ 2 * rem) := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right_iff hc
  have h2 : (den * c = 2 * (rem * c)) ↔ (den = 2 * rem) := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_left_inj (Nat.ne_of_gt hc)
  have h3 (w : Nat) : rem * c * 2 ^ w / (den * c) = rem * 2 ^ w / den := by
    rw [Nat.mul_right_comm, Nat.mul_div_mul_right _ _ hc]
  have h4 (w : Nat) : nearestEven (rem * c * 2 ^ w) (den * c) =
      roundQuotientEven (rem * 2 ^ w) den := by
    rw [Nat.mul_right_comm, nearestEven_mul _ _ _ hc]
  unfold roundAway Format.Internal.roundRationalAwayWithParity
  kernel_notation
  simp only [h0, h1, h2, h3, h4, beq_iff_eq]
  by_cases hrem : rem = 0
  · simp [hrem]
  simp only [hrem, ↓reduceIte]
  cases mode <;> cases negative <;> cases even <;>
    dsimp only [modeIndex, modeWidth, modeRandom, Format.Internal.scaleRationalFractionFloor,
      Format.Internal.scaleRationalFractionNearestEven] <;>
    kernel_notation <;>
    simp only [Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte, tsub_zero,
      ite_self, Bool.not_false, Bool.and_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
      tsub_self, Bool.not_true, Bool.and_false, Bool.or_false] <;>
    split_ifs <;> first | rfl | omega | exact ite_eq_right ‹_› | exact ite_eq_left ‹_›

/-! ## Rounding a ratio as it is given -/

/-- The terms of a ratio of natural numbers are the numerator and the denominator of its normal
form times a positive common factor, and the sign of the normal form is the sign given. -/
theorem exists_common_factor (negative : Bool) (n d : Nat) (hn : n ≠ 0) (hd : d ≠ 0) :
    ∃ c, 0 < c ∧
      n = ((if negative then -(n : Rat) else (n : Rat)) / (d : Rat)).num.natAbs * c ∧
      d = ((if negative then -(n : Rat) else (n : Rat)) / (d : Rat)).den * c ∧
      decide (((if negative then -(n : Rat) else (n : Rat)) / (d : Rat)).num < 0) = negative := by
  have hcast : (if negative then -(n : Rat) else (n : Rat)) =
      (((if negative then -(n : Int) else (n : Int)) : Int) : Rat) := by
    cases negative <;> simp
  rw [hcast]
  generalize hz : (if negative then -(n : Int) else (n : Int)) = z
  obtain ⟨c, hzc, hdc⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den z
    (Int.natCast_ne_zero.mpr hd)
  have hden := Rat.den_pos ((z : Rat) / ((d : Int) : Rat))
  have hcpos : 0 < c := by
    by_contra hneg
    have hle : c ≤ 0 := not_lt.mp hneg
    have : c * (((z : Rat) / ((d : Int) : Rat)).den : Int) ≤ 0 :=
      Int.mul_nonpos_of_nonpos_of_nonneg hle (Int.natCast_nonneg _)
    omega
  have hcast2 : ((d : Int) : Rat) = (d : Rat) := by simp
  rw [hcast2] at hzc hdc hden
  generalize (z : Rat) / (d : Rat) = q at hzc hdc hden
  refine ⟨c.toNat, by omega, ?_, ?_, ?_⟩
  · have hn' : (n : Int) = z.natAbs := by
      rw [← hz]
      cases negative <;> simp
    have hmul : z.natAbs = c.toNat * q.num.natAbs := by
      rw [hzc, Int.natAbs_mul]
      congr 1
      omega
    rw [Nat.mul_comm]
    omega
  · have hmul : (d : Int) = ((q.den * c.toNat : Nat) : Int) := by
      push_cast
      rw [Int.toNat_of_nonneg hcpos.le, mul_comm]
      exact hdc
    exact_mod_cast hmul
  · have hzneg : z < 0 ↔ negative = true := by
      rw [← hz]
      cases negative <;> simp
      omega
    have hnum : q.num < 0 ↔ z < 0 := by
      rw [hzc]
      constructor
      · intro h
        exact Int.mul_neg_of_pos_of_neg hcpos h
      · intro h
        by_contra hge
        have := Int.mul_nonneg hcpos.le (not_lt.mp hge)
        omega
    cases hneg : negative
    · exact decide_eq_false (fun h => by simpa [hneg] using hzneg.1 (hnum.1 h))
    · exact decide_eq_true (hnum.2 (hzneg.2 hneg))

/-- The parity flag of `roundedOf` is the reference parity of the code of the floor. -/
theorem even_eq (format : Format) (Qb beta lower : Nat) :
    (if 2 ≤ format.precision then 1 - (lower &&& 1)
      else if lower = 0 then 1 else 1 - ((Qb + beta + format.exponentBias) &&& 1)) =
      if format.lowerCodeIsEven ((Qb : Int) - (beta : Int)) lower then 1 else 0 := by
  unfold Format.lowerCodeIsEven
  rw [Nat.and_one_is_mod, Nat.and_one_is_mod]
  by_cases hP : 2 ≤ format.precision
  · rw [ite_eq_left hP, ite_eq_left (by omega : 1 < format.precision)]
    rcases Nat.mod_two_eq_zero_or_one lower with h | h <;> simp [h]
  · rw [ite_eq_right hP, ite_eq_right (by omega : ¬1 < format.precision)]
    by_cases hlower : lower = 0
    · simp [hlower]
    · simp only [hlower, beq_iff_eq, ite_false, Int.ofNat_eq_natCast]
      have hparity : (((Qb : Int) - (beta : Int) + (format.exponentBias : Int)) % 2 = 0) ↔
          ((Qb + beta + format.exponentBias) % 2 = 0) := by omega
      rcases Nat.mod_two_eq_zero_or_one (Qb + beta + format.exponentBias) with h | h
      · simp [h, hparity.2 h]
      · have hne : ¬(((Qb : Int) - (beta : Int) + (format.exponentBias : Int)) % 2 = 0) :=
          fun h0 => by have := hparity.1 h0; omega
        simp [h, hne]

/--
P3109 interim report v4.1, §§4.7.3 and 4.7.4: the reference precision rounding of the ratio
`(-1) ^ s * n / d` is the dyadic with the significand `roundedOf` at the quantum `quantumOf`,
and zero when that significand is zero. This holds for every descriptor, every rounding mode
with every random word, and every ratio with `n ≠ 0` and `d ≠ 0`: the ratio need not be in
lowest terms.
-/
theorem roundFiniteRatToPrecision_eq (format : Format) (mode : RoundingMode) (negative : Bool)
    (n d : Nat) (hn : n ≠ 0) (hd : d ≠ 0) :
    format.roundFiniteRatToPrecision mode
        ((if negative then -(n : Rat) else (n : Rat)) / (d : Rat)) =
      if roundedOf format.precision format.exponentBias (modeIndex mode) (modeWidth mode)
          (modeRandom mode) (if negative then 1 else 0) n d
          (quantumOf format.exponentBias n d) = 0 then Numerics.Dyadic.zero
      else
        { negative := negative
          significand := roundedOf format.precision format.exponentBias (modeIndex mode)
            (modeWidth mode) (modeRandom mode) (if negative then 1 else 0) n d
            (quantumOf format.exponentBias n d)
          exponent := ((quantumOf format.exponentBias n d : Nat) : Int) -
            ((d.log2 + 1 + (format.exponentBias + format.precision) : Nat) : Int) } := by
  obtain ⟨c, hc, hnc, hdc, hsign⟩ := exists_common_factor negative n d hn hd
  generalize (if negative then -(n : Rat) else (n : Rat)) / (d : Rat) = q at hnc hdc hsign ⊢
  have ha : q.num.natAbs ≠ 0 := by
    intro h
    rw [h, Nat.zero_mul] at hnc
    exact hn hnc
  have hfl : RationalBinary.floorLog2 q.num.natAbs q.den = RationalBinary.floorLog2 n d := by
    rw [hnc, hdc, KernelPath.floorLog2_mul_right _ _ c ha q.den_nz (by omega)]
  have hQ := quantumOf_eq format.exponentBias format.precision n d hn hd
  have hmin : format.minimumNormalExponent = 1 - (format.exponentBias : Int) := rfl
  unfold Format.roundFiniteRatToPrecision
  simp only [beq_iff_eq, ha, ite_false, hfl, hsign, hmin, Int.ofNat_eq_natCast, ← hQ,
    KernelPath.scaleByPowerOfTwo_eq_shifts, Format.Internal.roundRationalAway]
  generalize quantumOf format.exponentBias n d = Qb
  generalize hbeta : d.log2 + 1 + (format.exponentBias + format.precision) = beta
  have hs1 : (-((Qb : Int) - (beta : Int))).toNat = beta - Qb := by omega
  have hs2 : (- -((Qb : Int) - (beta : Int))).toNat = Qb - beta := by omega
  rw [hs1, hs2]
  unfold roundedOf
  rw [size_sub_one hd]
  kernel_notation
  rw [hbeta, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have hnum : n * 2 ^ (beta - Qb) = q.num.natAbs * 2 ^ (beta - Qb) * c := by
    rw [hnc, Nat.mul_right_comm]
  have hden : d * 2 ^ (Qb - beta) = q.den * 2 ^ (Qb - beta) * c := by
    rw [hdc, Nat.mul_right_comm]
  rw [hnum, hden, Nat.mul_div_mul_right _ _ hc, Nat.mul_mod_mul_right]
  have heven := even_eq format Qb beta
    (q.num.natAbs * 2 ^ (beta - Qb) / (q.den * 2 ^ (Qb - beta)))
  rw [heven, roundAway_eq mode negative _ _ _ c hc]
  generalize q.num.natAbs * 2 ^ (beta - Qb) / (q.den * 2 ^ (Qb - beta)) = lower
  generalize Format.Internal.roundRationalAwayWithParity mode negative
    (format.lowerCodeIsEven ((Qb : Int) - (beta : Int)) lower)
    (q.num.natAbs * 2 ^ (beta - Qb) % (q.den * 2 ^ (Qb - beta)))
    (q.den * 2 ^ (Qb - beta)) = away
  cases away <;> simp

/-! ## Saturation -/

/-- Two scaled natural numbers compare as rationals as they compare after a common shift that
makes both exponents natural numbers. -/
theorem mul_zpow_lt_iff (a b : Nat) (x y : Int) (X Y t : Nat) (hX : (X : Int) = x + t)
    (hY : (Y : Int) = y + t) :
    (a : Rat) * (2 : Rat) ^ x < (b : Rat) * (2 : Rat) ^ y ↔ a * 2 ^ X < b * 2 ^ Y := by
  have htwo : (0 : Rat) < 2 ^ (t : Int) := zpow_pos (by norm_num) _
  have hx : (a : Rat) * (2 : Rat) ^ x = ((a * 2 ^ X : Nat) : Rat) / 2 ^ (t : Int) := by
    rw [eq_div_iff htwo.ne', mul_assoc, ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), ← hX]
    push_cast
    rw [zpow_natCast]
  have hy : (b : Rat) * (2 : Rat) ^ y = ((b * 2 ^ Y : Nat) : Rat) / 2 ^ (t : Int) := by
    rw [eq_div_iff htwo.ne', mul_assoc, ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), ← hY]
    push_cast
    rw [zpow_natCast]
  rw [hx, hy, div_lt_div_iff_of_pos_right htwo, Nat.cast_lt]

/-- The largest finite value is the value of the largest finite code. -/
theorem maxFinite_toRat (format : Format) :
    format.maxFinite.toRat =
      (significandOf format.precision format.maxFiniteBits : Rat) *
        (2 : Rat) ^ ((exponentOf format.precision format.maxFiniteBits : Int) -
          ((format.exponentBias + format.trailingBits : Nat) : Int)) := by
  rw [mul_zpow_eq_div]
  exact decodePositiveFinite_toRat format format.maxFiniteBits

/--
P3109 interim report v4.1, §4.7.5: `exceeds` decides whether the rounded magnitude `r * 2 ^ (Qb
    - beta)` is
above the largest finite value of the descriptor.
-/
theorem exceeds_eq (format : Format) (r Qb beta : Nat) :
    exceeds format.bitWidth format.precision (sgOf format) (exOf format) format.exponentBias r Qb
        beta =
      decide (format.maxFinite.toRat < (r : Rat) * (2 : Rat) ^ ((Qb : Int) - (beta : Int))) := by
  unfold exceeds
  rw [maxFiniteBits_eq, trailingBits_eq, maxFinite_toRat, Bool.eq_iff_iff, decide_eq_true_eq]
  kernel_notation
  rw [mul_zpow_lt_iff _ r _ _ (exponentOf format.precision format.maxFiniteBits + beta)
    (Qb + format.exponentBias + format.trailingBits)
    (format.exponentBias + format.trailingBits + beta) (by push_cast; omega) (by push_cast; omega)]
  exact Iff.rfl

end FloatLib.Floats.Formats.P3109.KernelPath
