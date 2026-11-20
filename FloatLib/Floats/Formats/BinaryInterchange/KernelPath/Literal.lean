/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Conversion
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Div

/-!
# Literals on natural-number encodings

A numeric literal of a binary format is the nearest-even rounding of an exact rational: a
natural number, or a mantissa times or over a power of ten. `ofRatio fmt sign num den` is the
encoding of `± num / den` rounded to nearest even, computed on naturals: the two operands are
normalized to a common bit length and rounded by the quotient stage of the kernel division.
`ofScientific` and `ofNatural` are the two shapes of literal.

`ofRatio_eq` proves that `ofRatio` is the encoding of `Model.roundRat`, for every format
descriptor and all operands, a zero denominator included. `ofScientific_eq` and `ofNatural_eq`
prove that the literal functions are the encodings of `Model.ofRat` of the literal's rational
value, which is how every binary family defines its literals.

`natLength` uses the shared exact-arithmetic bit length, `Numerics.Kernel.size`. Small operands
use packed lanes and large operands use a windowed search.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The bit length of a natural number, using the shared exact-arithmetic kernel.
-/
def natLength (n : Nat) : Nat :=
  FloatLib.Numerics.Kernel.size n

/--
Encoding of `± num / den` rounded in the direction `mode`: the operands are shifted to a common
bit length and the quotient is rounded by `divCore`. A zero denominator gives the invalid result.
-/
def ofRatio (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (sign num den : Nat) : Nat :=
  (fun L Ld =>
    (fun W =>
      divCore fmt mode sign (Nat.shiftLeft num (Nat.sub W L)) (Nat.shiftLeft den (Nat.sub W Ld))
        L Ld (Nat.sub 1 den) (invalidWord fmt))
      (Nat.add L (Nat.sub Ld L)))
    (natLength num) (natLength den)

/--
Encoding of the scientific literal with mantissa `mantissa` and decimal exponent `exponent`,
which divides when `exponentSign` is set and multiplies otherwise, rounded to nearest even.
-/
def ofScientific (fmt : FloatFormat) (mantissa : Nat) (exponentSign : Bool) (exponent : Nat) :
    Nat :=
  Bool.casesOn (motive := fun _ => Nat) exponentSign
    (ofRatio fmt .nearest 0 (Nat.mul mantissa (Nat.pow 10 exponent)) 1)
    (ofRatio fmt .nearest 0 mantissa (Nat.pow 10 exponent))

/-- Encoding of the natural-number literal `value`, rounded to nearest even. -/
def ofNatural (fmt : FloatFormat) (value : Nat) : Nat :=
  ofRatio fmt .nearest 0 value 1

/-- `natLength n` is the bit length of `n`: zero for zero, and `n.log2 + 1` otherwise. -/
theorem natLength_eq (n : Nat) : natLength n = if n = 0 then 0 else n.log2 + 1 :=
  FloatLib.Numerics.Kernel.size_eq_log2 n

/-- A nonzero number shifted to `W` bits lies between `2 ^ (W - 1)` and `2 ^ W`. -/
theorem shiftLeft_normalized {m W : Nat} (hm : m ≠ 0) (hW : m.log2 + 1 ≤ W) :
    2 ^ (W - 1) ≤ m <<< (W - (m.log2 + 1)) ∧ m <<< (W - (m.log2 + 1)) < 2 ^ (W - 1 + 1) := by
  have hlt : m < 2 ^ (W - 1 + 1) :=
    lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega))
  have h := normalized_bounds hm hlt
  rwa [show W - 1 - m.log2 = W - (m.log2 + 1) by omega] at h

/--
Zero over a nonzero denominator rounds to the zero of its sign, in every rounding direction.
-/
theorem directedRat_zero (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (negative : Bool)
    (den : Nat) (hden : den ≠ 0) :
    Model.Internal.Directed.roundRat fmt mode negative 0 den = Model.zero fmt negative := by
  have hnearest := Model.roundRat_num_zero fmt negative den hden
  unfold Model.roundRat at hnearest
  cases mode <;>
    simp [Model.Internal.Directed.roundRat, Model.Internal.Directed.roundRatScaled,
      Model.roundRatNearestAwayScaled, Model.rationalIsGridTieScaled,
      Model.roundRatMagnitudeDirectedScaled, hden, hnearest]

/--
`ofRatio` computes the encoding of the reference rounding of `± num / den` in the direction
`mode`, `Model.Internal.Directed.roundRat`, for every format descriptor, every rounding direction
and all naturals.
-/
theorem ofRatio_eq_directed (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (negative : Bool) (num den : Nat) :
    ofRatio fmt mode (signNat negative) num den =
      (Model.Internal.Directed.roundRat fmt mode negative num den).toNatBits := by
  unfold ofRatio
  simp only [natLength_eq, Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq']
  by_cases hden : den = 0
  · subst hden
    have hspec : Model.Internal.Directed.roundRat fmt mode negative num 0 =
        Model.invalidResult fmt := by
      cases mode <;>
        simp [Model.Internal.Directed.roundRat, Model.Internal.Directed.roundRatScaled,
          Model.roundRatNearestAwayScaled, Model.rationalIsGridTieScaled,
          Model.roundRatMagnitudeDirectedScaled]
    rw [hspec]
    unfold divCore roundQuotient
    simp only [pack_eq]
    simp [invalidWord_eq]
  · have hguard : 1 - den = 0 := by omega
    rw [hguard, ite_eq_right hden]
    have hWden : den.log2 + 1 ≤
        (if num = 0 then 0 else num.log2 + 1) +
          (den.log2 + 1 - if num = 0 then 0 else num.log2 + 1) := by omega
    have hnb := shiftLeft_normalized hden hWden
    by_cases hnum : num = 0
    · subst hnum
      rw [directedRat_zero fmt mode negative den hden]
      simp only [ite_true, Nat.zero_shiftLeft] at hnb ⊢
      rw [divCore_eq fmt mode negative _ (signNat negative) 0 _ _ _ _ rfl (Or.inl rfl) hnb]
      simp [zeroWord_eq]
    · rw [ite_eq_right hnum] at hnb ⊢
      have hWnum : num.log2 + 1 ≤ num.log2 + 1 + (den.log2 + 1 - (num.log2 + 1)) := by omega
      have hna := shiftLeft_normalized hnum hWnum
      have hshift0 : num <<< (num.log2 + 1 + (den.log2 + 1 - (num.log2 + 1)) - (num.log2 + 1)) ≠
          0 := by
        simp [Nat.shiftLeft_eq, hnum]
      rw [divCore_eq fmt mode negative _ (signNat negative) _ _ _ _ _ rfl (Or.inr hna) hnb,
        ite_eq_right hshift0]
      unfold Model.Internal.Directed.roundRat
      rw [← directedRat_shiftLeft fmt mode negative _ num den
          (num.log2 + 1 + (den.log2 + 1 - (num.log2 + 1)) - (num.log2 + 1))
          (num.log2 + 1 + (den.log2 + 1 - (num.log2 + 1)) - (den.log2 + 1)) 0 hnum hden hna hnb]
      congr 2
      omega

/--
`ofRatio` to nearest even computes the encoding of the reference rounding `Model.roundRat` of
`± num / den`, for every format descriptor and all naturals.
-/
theorem ofRatio_eq (fmt : FloatFormat) (negative : Bool) (num den : Nat) :
    ofRatio fmt .nearest (signNat negative) num den =
      (Model.roundRat fmt negative num den).toNatBits :=
  ofRatio_eq_directed fmt .nearest negative num den

/-! ## The rounding depends on the quotient only -/

/-- The binary exponent of a quotient does not see a common factor. -/
theorem floorLog2_mul_right (n d c : Nat) (hn : n ≠ 0) (hd : d ≠ 0) (hc : c ≠ 0) :
    RationalBinary.floorLog2 (n * c) (d * c) = RationalBinary.floorLog2 n d := by
  rw [Model.floorLog2_eq_int_log (n * c) (d * c) (Nat.mul_ne_zero hn hc) (Nat.mul_ne_zero hd hc),
    Model.floorLog2_eq_int_log n d hn hd]
  congr 1
  have hcReal : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  push_cast
  rw [mul_div_mul_right _ _ hcReal]

/-- The reference rational rounder depends on the quotient only: a common factor cancels. -/
theorem roundRatScaledGeneral_mul_right (fmt : FloatFormat) (negative : Bool) (n d c : Nat)
    (e : Int) (hc : 0 < c) :
    Model.roundRatScaledGeneral fmt negative (n * c) (d * c) e =
      Model.roundRatScaledGeneral fmt negative n d e := by
  have hc0 : c ≠ 0 := by omega
  by_cases hd : d = 0
  · subst hd
    simp [Model.roundRatScaledGeneral]
  by_cases hn : n = 0
  · subst hn
    simp [Model.roundRatScaledGeneral, hd, hc0]
  have hquotient : ∀ s : Int,
      roundQuotientEven (RationalBinary.scaleByPowerOfTwo (n * c) (d * c) s).1
          (RationalBinary.scaleByPowerOfTwo (n * c) (d * c) s).2 =
        roundQuotientEven (RationalBinary.scaleByPowerOfTwo n d s).1
          (RationalBinary.scaleByPowerOfTwo n d s).2 := by
    intro s
    simp only [scaleByPowerOfTwo_eq_shifts, Nat.shiftLeft_eq]
    rw [show n * c * 2 ^ s.toNat = n * 2 ^ s.toNat * c by ac_rfl,
      show d * c * 2 ^ (-s).toNat = d * 2 ^ (-s).toNat * c by ac_rfl,
      roundQuotientEven_mul_right _ _ _ hc]
  unfold Model.roundRatScaledGeneral
  simp only [beq_iff_eq, Nat.mul_eq_zero, hn, hd, hc0, or_self, ite_false,
    floorLog2_mul_right n d c hn hd hc0, hquotient]

/-- Two nonzero numbers can be shifted to a common bit length. -/
theorem exists_normalization (n d : Nat) (hn : n ≠ 0) (hd : d ≠ 0) :
    ∃ W la lb : Nat, (2 ^ W ≤ n <<< la ∧ n <<< la < 2 ^ (W + 1)) ∧
      (2 ^ W ≤ d <<< lb ∧ d <<< lb < 2 ^ (W + 1)) :=
  ⟨n.log2 + d.log2 + 1 - 1, _, _,
    shiftLeft_normalized hn (W := n.log2 + d.log2 + 1) (by omega),
    shiftLeft_normalized hd (W := n.log2 + d.log2 + 1) (by omega)⟩

/-- The reference rounding of a quotient does not see a common factor of its operands. -/
theorem roundRat_mul_right (fmt : FloatFormat) (negative : Bool) (n d c : Nat) (hc : 0 < c) :
    Model.roundRat fmt negative (n * c) (d * c) = Model.roundRat fmt negative n d := by
  have hc0 : c ≠ 0 := by omega
  by_cases hd : d = 0
  · subst hd
    simp
  by_cases hn : n = 0
  · subst hn
    simp [hd, hc0]
  obtain ⟨W, la, lb, hna, hnb⟩ := exists_normalization n d hn hd
  obtain ⟨W', la', lb', hna', hnb'⟩ :=
    exists_normalization (n * c) (d * c) (Nat.mul_ne_zero hn hc0) (Nat.mul_ne_zero hd hc0)
  unfold Model.roundRat
  rw [roundRatScaled_eq_general fmt negative W n d la lb 0 hn hd hna hnb,
    roundRatScaled_eq_general fmt negative W' (n * c) (d * c) la' lb' 0
      (Nat.mul_ne_zero hn hc0) (Nat.mul_ne_zero hd hc0) hna' hnb',
    roundRatScaledGeneral_mul_right fmt negative n d c 0 hc]

/-- A nonnegative quotient of naturals is its reduced fraction times a common factor. -/
theorem exists_common_factor (q : ℚ) (num den : Nat) (hden : den ≠ 0)
    (hq : q = (num : ℚ) / (den : ℚ)) :
    ∃ g : Nat, 0 < g ∧ num = q.num.natAbs * g ∧ den = q.den * g ∧ ¬ q.num < 0 := by
  have hdenQ : (den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hden
  have hqdenQ : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hnonneg : 0 ≤ q := by
    rw [hq]
    positivity
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hnonneg
  have hcrossQ : (num : ℚ) * q.den = q.num * den := by
    have h : (q.num : ℚ) / q.den = (num : ℚ) / den := by
      rw [Rat.num_div_den]
      exact hq
    exact ((div_eq_div_iff hqdenQ hdenQ).mp h).symm
  have hcross : num * q.den = q.num.natAbs * den := by
    have hInt : (num : ℤ) * q.den = q.num * den := by exact_mod_cast hcrossQ
    have : ((num * q.den : ℕ) : ℤ) = ((q.num.natAbs * den : ℕ) : ℤ) := by
      push_cast
      rw [abs_of_nonneg hnum]
      exact hInt
    exact_mod_cast this
  have hdvd : q.den ∣ den := by
    have hcoprime : Nat.Coprime q.den q.num.natAbs := q.reduced.symm
    refine hcoprime.dvd_of_dvd_mul_left ?_
    exact ⟨num, by rw [← hcross, Nat.mul_comm]⟩
  obtain ⟨g, hg⟩ := hdvd
  have hgpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | hpos
    · rw [h0, Nat.mul_zero] at hg
      exact absurd hg hden
    · exact hpos
  refine ⟨g, hgpos, ?_, hg, by omega⟩
  have hdenpos : 0 < q.den := q.den_pos
  rw [hg, ← Nat.mul_assoc, Nat.mul_comm (q.num.natAbs) q.den, Nat.mul_assoc,
    Nat.mul_comm num q.den] at hcross
  exact Nat.eq_of_mul_eq_mul_left hdenpos hcross

/--
`ofRatio` with a positive sign computes the encoding of `Model.ofRat` of the quotient, for every
format descriptor and every nonzero denominator.
-/
theorem ofRatio_eq_ofRat (fmt : FloatFormat) (q : ℚ) (num den : Nat) (hden : den ≠ 0)
    (hq : q = (num : ℚ) / (den : ℚ)) :
    ofRatio fmt .nearest 0 num den = (Model.ofRat fmt q).toNatBits := by
  obtain ⟨g, hg, hnum, hdenEq, hsign⟩ := exists_common_factor q num den hden hq
  have hstep : ofRatio fmt .nearest 0 num den = ofRatio fmt .nearest (signNat false) num den :=
    rfl
  rw [hstep, ofRatio_eq]
  change _ = (Model.roundRat fmt (decide (q.num < 0)) q.num.natAbs q.den).toNatBits
  have hdecide : decide (q.num < 0) = false := by simp [hsign]
  rw [hdecide]
  conv_lhs => rw [hnum, hdenEq]
  rw [roundRat_mul_right fmt false _ _ g hg]

/--
`ofScientific` computes the encoding of the scientific literal: `Model.ofRat` of its rational
value, for every format descriptor.
-/
theorem ofScientific_eq (fmt : FloatFormat) (mantissa : Nat) (exponentSign : Bool)
    (exponent : Nat) :
    ofScientific fmt mantissa exponentSign exponent =
      (Model.ofRat fmt
        (OfScientific.ofScientific mantissa exponentSign exponent : ℚ)).toNatBits := by
  have hvalue : (OfScientific.ofScientific mantissa exponentSign exponent : ℚ) =
      Rat.ofScientific mantissa exponentSign exponent := rfl
  rw [hvalue]
  unfold ofScientific
  cases exponentSign
  · refine ofRatio_eq_ofRat fmt _ _ 1 (by decide) ?_
    rw [Rat.ofScientific_false_def]
    simp
  · refine ofRatio_eq_ofRat fmt _ _ _ (Nat.pow_pos (by decide : 0 < 10)).ne' ?_
    rw [Rat.ofScientific_true_def, Rat.mkRat_eq_div]
    simp [Nat.pow_eq]

/--
`ofNatural` computes the encoding of the natural-number literal: `Model.ofRat` of the number, for
every format descriptor.
-/
theorem ofNatural_eq (fmt : FloatFormat) (value : Nat) :
    ofNatural fmt value = (Model.ofRat fmt (value : ℚ)).toNatBits := by
  unfold ofNatural
  refine ofRatio_eq_ofRat fmt _ _ 1 (by decide) ?_
  simp

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
