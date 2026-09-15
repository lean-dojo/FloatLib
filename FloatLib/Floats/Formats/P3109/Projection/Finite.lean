/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import Mathlib.Tactic.Ring
public import FloatLib.Floats.Formats.P3109.Projection.Runtime
public import FloatLib.Floats.Formats.P3109.Proof

/-!
# Finite-value correctness for P3109 projection

Positive-row encoding and decoding preserve the rational value of a positive dyadic on the
descriptor's precision grid, including the carry significand `2^P`. These formulas use natural
numbers without an upper exponent bound. `Projection.Range` adds the finite-range and bit-width
bounds needed for full datum encoding.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109
namespace Format

/--
Decoding the code that the encoder assembles from a row-scaled significand.

`shifted` is the significand scaled into the selected exponent row, so it is below `2^P`, and it
is below `2^(P-1)` only when that row is the subnormal one.
-/
theorem decodePositiveFinite_encodeRow_toRat
    (format : Format) (shifted : Nat) (encodedExponent : Int)
    (hlt : shifted < 2 * 2 ^ format.trailingBits)
    (hmin : format.minimumNormalExponent ≤ encodedExponent)
    (hsubnormal : shifted < 2 ^ format.trailingBits →
      encodedExponent = format.minimumNormalExponent) :
    (format.decodePositiveFinite
      (if shifted < 2 ^ format.trailingBits then
        shifted % 2 ^ format.trailingBits
      else
        shifted % 2 ^ format.trailingBits +
          Int.toNat (encodedExponent + Int.ofNat format.exponentBias) *
            2 ^ format.trailingBits)).toRat =
      (shifted : Rat) * 2 ^ (encodedExponent - Int.ofNat format.trailingBits) := by
  have hunit : 0 < 2 ^ format.trailingBits := Nat.two_pow_pos _
  split
  next hsub =>
    rw [Nat.mod_eq_of_lt hsub, format.decodePositiveFinite_toRat_of_lt _ hsub,
      hsubnormal hsub, format.minimumQuantumExponent_eq]
  next hnormal =>
    have hbiased : 0 < encodedExponent + Int.ofNat format.exponentBias := by
      unfold minimumNormalExponent at hmin
      omega
    have hbiased_cast := Int.toNat_of_nonneg hbiased.le
    have hbiased_ne : Int.toNat (encodedExponent + Int.ofNat format.exponentBias) ≠ 0 := by
      omega
    rw [format.decodePositiveFinite_toRat_add_mul _ _ (Nat.mod_lt _ hunit) hbiased_ne]
    have hdiv : shifted / 2 ^ format.trailingBits = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have hreconstruct :
        2 ^ format.trailingBits + shifted % 2 ^ format.trailingBits = shifted := by
      have := Nat.mod_add_div shifted (2 ^ format.trailingBits)
      rw [hdiv] at this
      omega
    rw [hreconstruct]
    congr 2
    have := format.trailingBits_int
    simp only [Int.ofNat_eq_natCast] at *
    omega

/--
Positive-row encoding preserves every positive dyadic accepted by the precision grid.

The significand bound is not strict: the carry value `2^P`, produced when precision rounding
increments an all-ones significand, is encoded in the next exponent row. The exponent lower bound
is the smallest P3109 quantum, so the theorem covers every normal and subnormal row of every
valid descriptor.
-/
theorem decodePositiveFinite_encodePositiveFinite_eq_of_le
    (format : Format) (value : Numerics.Dyadic)
    (hnegative : value.negative = false)
    (hzero : value.significand ≠ 0)
    (hprecision : value.significand ≤ 2 ^ format.precision)
    (hexponent : format.minimumQuantumExponent ≤ value.exponent) :
    (format.decodePositiveFinite
      (Internal.encodePositiveFinite format value)).toRat =
      value.toRat := by
  have hT := format.trailingBits_add_one
  have hTi := format.trailingBits_int
  have hminQ := format.minimumQuantumExponent_eq
  have hlog_lt : value.significand < 2 ^ (value.significand.log2 + 1) :=
    (Nat.log2_lt hzero).1 (Nat.lt_succ_self _)
  have hlog_le : 2 ^ value.significand.log2 ≤ value.significand :=
    (Nat.le_log2 hzero).1 le_rfl
  have hvalue : value.toRat = (value.significand : Rat) * 2 ^ value.exponent := by
    simp [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand, hnegative]
  unfold Internal.encodePositiveFinite
  simp only [hzero, beq_iff_eq, if_false]
  generalize hE : max (Int.ofNat value.significand.log2 + value.exponent)
    format.minimumNormalExponent = E
  have hminE : format.minimumNormalExponent ≤ E := hE ▸ le_max_right _ _
  have hLE : Int.ofNat value.significand.log2 + value.exponent ≤ E := hE ▸ le_max_left _ _
  have hE_of_ne : E ≠ format.minimumNormalExponent →
      E = Int.ofNat value.significand.log2 + value.exponent := by
    intro hne
    rw [← hE] at hne ⊢
    exact max_eq_left (le_of_not_ge fun h => hne (max_eq_right h))
  split
  next shift heq =>
    have hshift : value.significand.log2 + shift ≤ format.trailingBits := by
      simp only [Int.ofNat_eq_natCast] at heq hLE
      omega
    rw [format.decodePositiveFinite_encodeRow_toRat _ E]
    · have hexp : value.exponent = E - Int.ofNat format.trailingBits + (shift : Int) := by
        simp only [Int.ofNat_eq_natCast] at heq ⊢
        omega
      rw [hvalue, Nat.shiftLeft_eq', Nat.shiftLeft_eq, hexp,
        zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), zpow_natCast]
      push_cast
      ring
    · rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
      calc value.significand * 2 ^ shift
          < 2 ^ (value.significand.log2 + 1) * 2 ^ shift :=
            Nat.mul_lt_mul_of_pos_right hlog_lt (Nat.two_pow_pos _)
        _ = 2 ^ (value.significand.log2 + shift + 1) := by ring
        _ ≤ 2 ^ (format.trailingBits + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 * 2 ^ format.trailingBits := by ring
    · exact hminE
    · intro hsub
      by_contra hne
      have hEL := hE_of_ne hne
      have hshift_eq : value.significand.log2 + shift = format.trailingBits := by
        simp only [Int.ofNat_eq_natCast] at heq hEL
        omega
      rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, ← hshift_eq, Nat.pow_add] at hsub
      exact absurd hsub (not_lt.mpr (Nat.mul_le_mul_right _ hlog_le))
  next shift heq =>
    have hEL : E = Int.ofNat value.significand.log2 + value.exponent := by
      apply hE_of_ne
      intro hne
      rw [hne, Int.negSucc_eq] at heq
      simp only [Int.ofNat_eq_natCast] at heq hminQ hexponent
      omega
    have hlog_ge : format.precision ≤ value.significand.log2 := by
      rw [hEL, Int.negSucc_eq] at heq
      simp only [Int.ofNat_eq_natCast] at heq hTi
      omega
    have hsig : value.significand = 2 ^ format.precision :=
      le_antisymm hprecision ((Nat.le_log2 hzero).1 hlog_ge)
    have hlog : value.significand.log2 = format.precision := by
      rw [hsig, Nat.log2_two_pow]
    have hshift : shift = 0 := by
      rw [hEL, hlog, Int.negSucc_eq] at heq
      simp only [Int.ofNat_eq_natCast] at heq hTi
      omega
    have hshifted :
        Nat.shiftRight value.significand (shift + 1) = 2 ^ format.trailingBits := by
      rw [hshift, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, hsig, ← hT, Nat.pow_succ]
      simp
    rw [hshifted, format.decodePositiveFinite_encodeRow_toRat _ E]
    · rw [hvalue, hsig, show E - Int.ofNat format.trailingBits = value.exponent + 1 by
        rw [hEL, hlog]
        simp only [Int.ofNat_eq_natCast] at hTi ⊢
        omega]
      rw [zpow_add_one₀ (by norm_num), ← hT, pow_succ]
      push_cast
      ring
    · have := Nat.two_pow_pos format.trailingBits
      omega
    · exact hminE
    · intro h
      exact absurd h (lt_irrefl _)

end Format
end FloatLib.Floats.Formats.P3109
