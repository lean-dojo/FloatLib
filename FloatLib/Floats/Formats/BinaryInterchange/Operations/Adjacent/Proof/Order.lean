/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Adjacent.Proof.Rank

/-!
# Extended-real order of binary adjacency ranks

A finite word is its signed grid index times the least subnormal spacing. Comparing these indices,
together with the signed infinity endpoints, proves that adjacency ranks and extended-real values
have the same order and equality on every non-NaN word.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Multiple of the least subnormal spacing denoted by a positive word with biased exponent `e` and
fraction `f`.
-/
private def gridIndex (fmt : FloatFormat) (e f : Nat) : Nat :=
  if e = 0 then f else (2 ^ fmt.fracWidth + f) * 2 ^ (e - 1)

/-- The grid index increases strictly with the field pair read as one number. -/
private theorem gridIndex_lt_gridIndex (fmt : FloatFormat) {e f e' f' : Nat}
    (hf : f < 2 ^ fmt.fracWidth) (hf' : f' < 2 ^ fmt.fracWidth)
    (h : e * 2 ^ fmt.fracWidth + f < e' * 2 ^ fmt.fracWidth + f') :
    gridIndex fmt e f < gridIndex fmt e' f' := by
  have hle : e ≤ e' := by
    by_contra hlt
    have : (e' + 1) * 2 ^ fmt.fracWidth ≤ e * 2 ^ fmt.fracWidth :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  rcases hle.lt_or_eq with hlt | heq
  · have hbelow : gridIndex fmt e f < 2 ^ fmt.fracWidth * 2 ^ e := by
      unfold gridIndex
      split_ifs with he
      · subst he
        simpa using hf
      · calc (2 ^ fmt.fracWidth + f) * 2 ^ (e - 1)
            < (2 * 2 ^ fmt.fracWidth) * 2 ^ (e - 1) :=
              Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
          _ = 2 ^ fmt.fracWidth * 2 ^ e := by
            rw [show e = (e - 1) + 1 by omega, pow_succ]
            simp only [Nat.add_sub_cancel]
            ring
    have habove : 2 ^ fmt.fracWidth * 2 ^ e ≤ gridIndex fmt e' f' := by
      have he' : e' ≠ 0 := by omega
      simp only [gridIndex, he', ite_false]
      calc 2 ^ fmt.fracWidth * 2 ^ e ≤ 2 ^ fmt.fracWidth * 2 ^ (e' - 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
        _ ≤ (2 ^ fmt.fracWidth + f') * 2 ^ (e' - 1) :=
            Nat.mul_le_mul_right _ (by omega)
    omega
  · subst heq
    unfold gridIndex
    split_ifs
    · omega
    · exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)

/-- Grid index of a word, read from its stored fields. -/
private def wordGridIndex {fmt : FloatFormat} (x : Model fmt) : Nat :=
  gridIndex fmt (expField x) (fracField x)

private theorem wordGridIndex_lt_wordGridIndex {fmt : FloatFormat} {x y : Model fmt}
    (h : magnitudeBits x < magnitudeBits y) : wordGridIndex x < wordGridIndex y :=
  gridIndex_lt_gridIndex fmt (fracField_lt_pow2 x) (fracField_lt_pow2 y) h

private theorem wordGridIndex_eq_zero_iff {fmt : FloatFormat} (x : Model fmt) :
    wordGridIndex x = 0 ↔ magnitudeBits x = 0 := by
  constructor
  · intro h
    by_contra hm
    have hzero : magnitudeBits (posZero fmt) = 0 := by simp [magnitudeBits]
    have hlt := wordGridIndex_lt_wordGridIndex (x := posZero fmt) (y := x) (by omega)
    omega
  · intro h
    obtain ⟨he, hf⟩ := fields_eq_zero_of_magnitude_eq_zero h
    simp [wordGridIndex, gridIndex, he, hf]

/-- Signed grid index: the grid index, negated when the sign bit is set. -/
private def signedGridIndex {fmt : FloatFormat} (x : Model fmt) : Int :=
  if signBit x then -(wordGridIndex x : Int) else wordGridIndex x

/-- Signed grid indices are ordered as their signed keys. -/
private theorem signedGridIndex_lt_signedGridIndex {fmt : FloatFormat} {x y : Model fmt}
    (h : signedMagnitude x < signedMagnitude y) : signedGridIndex x < signedGridIndex y := by
  have hzx := wordGridIndex_eq_zero_iff x
  have hzy := wordGridIndex_eq_zero_iff y
  unfold signedMagnitude at h
  unfold signedGridIndex
  cases hsx : signBit x <;> cases hsy : signBit y <;>
    simp only [hsx, hsy, ite_true, ite_false, Bool.false_eq_true] at h ⊢
  · have := wordGridIndex_lt_wordGridIndex (x := x) (y := y) (by omega)
    omega
  · omega
  · omega
  · have := wordGridIndex_lt_wordGridIndex (x := y) (y := x) (by omega)
    omega

/-- A finite word denotes its signed grid index times the least subnormal spacing. -/
private theorem toReal_eq_signedGridIndex {fmt : FloatFormat} {x : Model fmt}
    (hx : isFinite x = true) :
    toReal x = (signedGridIndex x : ℝ) * (2 : ℝ) ^ fmt.minSubnormalExponent := by
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hx
  have hsign := sign_eq_signBit_of_toDyadic?_some hd
  rw [toReal_eq, hd]
  simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand, hsign, signedGridIndex,
    wordGridIndex]
  rcases toDyadic?_some_cases hd with ⟨hs, -⟩ | ⟨he, _, hs, hexp⟩ | ⟨he, hs, hexp⟩
  · have hz := fields_eq_zero_of_magnitude_eq_zero <| magnitude_eq_zero_of_isZero
      (isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hd hs)
    cases signBit x <;> simp [hs, hz.1, hz.2, gridIndex]
  · cases signBit x <;> simp [hs, hexp, he, gridIndex]
  · rw [hs, hexp]
    simp only [gridIndex, he, ite_false, pow2_eq_two_pow]
    have hexpEq : (Int.ofNat (expField x) - Int.ofNat fmt.exponentBias -
        Int.ofNat fmt.fracWidth) = ((expField x - 1 : Nat) : Int) + fmt.minSubnormalExponent := by
      unfold FloatFormat.minSubnormalExponent FloatFormat.minNormalExponent
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hexpEq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
    cases signBit x <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> push_cast <;> ring

/-- Only an IEEE encoding has infinities, which have the all-ones exponent and zero fraction. -/
private theorem encoding_eq_ieee_and_magnitude_of_isInfinite {fmt : FloatFormat} {x : Model fmt}
    (hx : isInfinite x = true) :
    fmt.encoding = .ieee ∧ magnitudeBits x = fmt.expAllOnesNat * 2 ^ fmt.fracWidth := by
  cases hencoding : fmt.encoding with
  | ieee =>
      have hfields : expField x = fmt.expAllOnesNat ∧ fracField x = 0 := by
        simpa [isInfinite, hencoding, IEEE.isInfinite, Bool.and_eq_true] using hx
      exact ⟨rfl, by simp [magnitudeBits, hfields.1, hfields.2]⟩
  | finiteMaxNaN | finiteUnsignedZero | finite =>
      simp [isInfinite, hencoding] at hx

/-- A finite IEEE word has a magnitude below that of the infinities. -/
theorem magnitude_lt_of_isFinite {fmt : FloatFormat} {x : Model fmt}
    (hencoding : fmt.encoding = .ieee) (hx : isFinite x = true) :
    magnitudeBits x < fmt.expAllOnesNat * 2 ^ fmt.fracWidth := by
  have hne : expField x ≠ fmt.expAllOnesNat := by
    simpa [isFinite, hencoding, IEEE.isFinite] using hx
  have hlt := expField_lt_pow2 x
  exact (expField_lt_iff x _).1 (by unfold FloatFormat.expAllOnesNat at hne ⊢; omega)

/-- A number in an IEEE encoding has magnitude at most that of the infinities. -/
theorem magnitude_le_of_isNaN_eq_false {fmt : FloatFormat} {x : Model fmt}
    (hencoding : fmt.encoding = .ieee) (hnan : isNaN x = false) :
    magnitudeBits x ≤ fmt.expAllOnesNat * 2 ^ fmt.fracWidth := by
  cases hinf : isInfinite x
  · exact (magnitude_lt_of_isFinite hencoding
      (isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x hnan hinf)).le
  · exact (encoding_eq_ieee_and_magnitude_of_isInfinite hinf).2.le

/-- An infinity denotes the extended-real endpoint of its sign, as a finite word denotes a real. -/
private theorem toEReal_of_isInfinite {fmt : FloatFormat} {x : Model fmt} (hx :
    isInfinite x = true) :
    toEReal x = if signBit x then ⊥ else ⊤ := by
  rw [toEReal_eq_ite, isNaN_eq_false_of_isInfinite_eq_true x hx]
  simp [hx]

/-- Numbers are ordered in the extended reals as their signed keys. -/
private theorem toEReal_lt_toEReal_of_signedMagnitude_lt {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = false) (hy : isNaN y = false) (h : signedMagnitude x < signedMagnitude y) :
    toEReal x < toEReal y := by
  cases hxinf : isInfinite x <;> cases hyinf : isInfinite y
  · have hxf := isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x hx hxinf
    have hyf := isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false y hy hyinf
    rw [toEReal_eq_coe_toReal_of_isFinite x hxf, toEReal_eq_coe_toReal_of_isFinite y hyf,
      EReal.coe_lt_coe_iff, toReal_eq_signedGridIndex hxf, toReal_eq_signedGridIndex hyf]
    have hu : (0 : ℝ) < (2 : ℝ) ^ fmt.minSubnormalExponent := by positivity
    exact mul_lt_mul_of_pos_right (by exact_mod_cast signedGridIndex_lt_signedGridIndex h) hu
  · obtain ⟨henc, hmy⟩ := encoding_eq_ieee_and_magnitude_of_isInfinite hyinf
    have hxf := isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x hx hxinf
    have hmx := magnitude_lt_of_isFinite henc hxf
    rw [toEReal_eq_coe_toReal_of_isFinite x hxf, toEReal_of_isInfinite hyinf]
    cases hsy : signBit y
    · simp
    · unfold signedMagnitude at h
      cases hsx : signBit x <;>
        simp only [hsx, hsy, ite_true, ite_false, Bool.false_eq_true] at h <;> omega
  · obtain ⟨henc, hmx⟩ := encoding_eq_ieee_and_magnitude_of_isInfinite hxinf
    have hyf := isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false y hy hyinf
    have hmy := magnitude_lt_of_isFinite henc hyf
    rw [toEReal_eq_coe_toReal_of_isFinite y hyf, toEReal_of_isInfinite hxinf]
    cases hsx : signBit x
    · unfold signedMagnitude at h
      cases hsy : signBit y <;>
        simp only [hsx, hsy, ite_true, ite_false, Bool.false_eq_true] at h <;> omega
    · simp
  · obtain ⟨-, hmx⟩ := encoding_eq_ieee_and_magnitude_of_isInfinite hxinf
    obtain ⟨-, hmy⟩ := encoding_eq_ieee_and_magnitude_of_isInfinite hyinf
    rw [toEReal_of_isInfinite hxinf, toEReal_of_isInfinite hyinf]
    unfold signedMagnitude at h
    cases hsx : signBit x <;> cases hsy : signBit y <;>
      simp only [hsx, hsy, ite_true, ite_false, Bool.false_eq_true] at h ⊢ <;>
      first | omega | exact bot_lt_top

/-- Numbers with equal signed keys denote the same extended real. -/
private theorem toEReal_eq_toEReal_of_signedMagnitude_eq {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = false) (hy : isNaN y = false) (h : signedMagnitude x = signedMagnitude y) :
    toEReal x = toEReal y := by
  unfold signedMagnitude at h
  by_cases hs : signBit x = signBit y
  · have hm : magnitudeBits x = magnitudeBits y := by
      rw [hs] at h
      cases hsy : signBit y <;> simp only [hsy, ite_true, ite_false, Bool.false_eq_true] at h <;>
        omega
    rw [eq_of_signBit_eq_of_magnitude_eq hs hm]
  · have hm : magnitudeBits x = 0 ∧ magnitudeBits y = 0 := by
      cases hsx : signBit x <;> cases hsy : signBit y <;>
        simp only [hsx, hsy, ite_true, ite_false, Bool.false_eq_true, not_true_eq_false,
          not_false_eq_true] at h hs <;> omega
    have hxz := isZero_of_magnitude_eq_zero hx hm.1
    have hyz := isZero_of_magnitude_eq_zero hy hm.2
    rw [toEReal_eq_coe_toReal_of_isFinite x (isFinite_eq_true_of_isZero_eq_true x hxz),
      toEReal_eq_coe_toReal_of_isFinite y (isFinite_eq_true_of_isZero_eq_true y hyz),
      toReal_eq_zero_of_isZero x hxz, toReal_eq_zero_of_isZero y hyz]

/--
On non-NaN values the adjacency rank is a strict order embedding of the extended-real values:
a smaller rank is a smaller number, including at both infinities and across the two zeros.
-/
theorem adjacencyRank_lt_adjacencyRank_iff {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = false) (hy : isNaN y = false) :
    adjacencyRank x < adjacencyRank y ↔ toEReal x < toEReal y := by
  have hkey : adjacencyRank x < adjacencyRank y ↔ signedMagnitude x < signedMagnitude y := by
    have := adjacencyRank_eq_signedMagnitude x
    have := adjacencyRank_eq_signedMagnitude y
    omega
  rw [hkey]
  refine ⟨toEReal_lt_toEReal_of_signedMagnitude_lt hx hy, fun hlt => ?_⟩
  rcases lt_trichotomy (signedMagnitude x) (signedMagnitude y) with hk | hk | hk
  · exact hk
  · exact absurd (toEReal_eq_toEReal_of_signedMagnitude_eq hx hy hk) hlt.ne
  · exact absurd (toEReal_lt_toEReal_of_signedMagnitude_lt hy hx hk) (not_lt.mpr hlt.le)

/--
Two non-NaN values have the same adjacency rank if and only if they denote the same extended real.
The two signed-zero words therefore share a rank, and every other number has a rank of its own.
-/
theorem adjacencyRank_eq_adjacencyRank_iff {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = false) (hy : isNaN y = false) :
    adjacencyRank x = adjacencyRank y ↔ toEReal x = toEReal y := by
  constructor
  · intro h
    apply toEReal_eq_toEReal_of_signedMagnitude_eq hx hy
    have := adjacencyRank_eq_signedMagnitude x
    have := adjacencyRank_eq_signedMagnitude y
    omega
  · intro h
    rcases lt_trichotomy (adjacencyRank x) (adjacencyRank y) with hr | hr | hr
    · exact absurd h ((adjacencyRank_lt_adjacencyRank_iff hx hy).1 hr).ne
    · exact hr
    · exact absurd h.symm ((adjacencyRank_lt_adjacencyRank_iff hy hx).1 hr).ne

/-- On non-NaN values a weakly smaller adjacency rank is a weakly smaller extended real. -/
theorem adjacencyRank_le_adjacencyRank_iff {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = false) (hy : isNaN y = false) :
    adjacencyRank x ≤ adjacencyRank y ↔ toEReal x ≤ toEReal y := by
  rw [← not_lt, ← not_lt, adjacencyRank_lt_adjacencyRank_iff hy hx]

/-! ## Steps between numbers -/

end Model
end FloatLib.Floats.Formats.BinaryInterchange
