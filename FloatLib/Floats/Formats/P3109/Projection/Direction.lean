/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
public import FloatLib.Floats.Formats.P3109.Projection.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Rounding-direction theorems for P3109 projection

`Format.roundFiniteToPrecision` expresses an exact finite dyadic in units of the descriptor
quantum `2^Q`, with `Q = max(floor(log2 |X|), 1 - B) - P + 1`, and then chooses between the two
integers bracketing the scaled magnitude. This module proves that the deterministic modes make
the choice the report prescribes:

* `towardZero` truncates: the result has the smaller magnitude and lies within one quantum;
* `towardPositive` and `towardNegative` bracket the input from the requested side;
* `nearestTiesToAway` and `nearestTiesToEven` stay within half a quantum, and on an exact tie
  select the larger magnitude, respectively the candidate whose P3109 code is even;
* `toOdd` stays within one quantum; for `P > 1`, it returns an odd significand whenever nonzero
  bits were discarded.

The bounds concern rational denotations before saturation and cover every descriptor width,
including `P = 1`. `Projection.Selection` and `Projection.Rational.Selection` prove the
stochastic selection formulas for every supplied random word.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109
namespace Format

/--
Quantum exponent selected by P3109 precision rounding for a nonzero finite dyadic.

This is the `Q` of Section 4.7.4: the selected precision grid has spacing `2^Q` before saturation.
-/
def quantumExponent (format : Format) (value : Numerics.Dyadic) : Int :=
  max (Int.ofNat value.significand.log2 + value.exponent) format.minimumNormalExponent -
    Int.ofNat format.precision + 1

/-- The quantum `2^Q` as a positive rational. -/
theorem quantum_pos (format : Format) (value : Numerics.Dyadic) :
    (0 : Rat) < (2 : Rat) ^ format.quantumExponent value :=
  zpow_pos (by norm_num) _

namespace Internal

/-- Rational sign factor of a dyadic. -/
def signRat (negative : Bool) : Rat :=
  if negative then -1 else 1

private theorem toRat_eq_signRat (value : Numerics.Dyadic) :
    value.toRat = signRat value.negative * (value.significand : Rat) * (2 : Rat) ^ value.exponent := by
  cases hnegative : value.negative <;>
    simp [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand, signRat, hnegative]

private theorem abs_signRat_mul (negative : Bool) (a u : Rat) (hu : 0 < u) :
    |signRat negative * a * u| = |a| * u := by
  cases negative <;> simp [signRat, abs_mul, abs_of_pos hu]

/--
Structural description of one precision-rounding step.

The input equals `sign * (lower + rem / 2^d) * 2^Q` with `rem < 2^d`, and the result significand
is `lower` or `lower + 1` exactly as `roundAway` decides.
-/
theorem roundFiniteToPrecision_spec
    (format : Format) (mode : RoundingMode) (value : Numerics.Dyadic)
    (hzero : value.significand ≠ 0) :
    ∃ lower rem d : Nat,
      rem < 2 ^ d ∧
      value.toRat =
        signRat value.negative * ((lower : Rat) + (rem : Rat) / 2 ^ d) *
          (2 : Rat) ^ format.quantumExponent value ∧
      (format.roundFiniteToPrecision mode value).significand =
        (if roundAway format mode value.negative (format.quantumExponent value)
            lower rem d then lower + 1 else lower) ∧
      (format.roundFiniteToPrecision mode value).toRat =
        signRat value.negative *
          ((format.roundFiniteToPrecision mode value).significand : Rat) *
          (2 : Rat) ^ format.quantumExponent value := by
  have hq :
      max (Int.ofNat value.significand.log2 + value.exponent)
          format.minimumNormalExponent - Int.ofNat format.precision + 1 =
        format.quantumExponent value := rfl
  unfold roundFiniteToPrecision
  simp only [beq_iff_eq, hzero, if_false]
  rw [hq]
  split
  next _ shift heq =>
    refine ⟨Nat.shiftLeft value.significand shift, 0, 0, by norm_num, ?_, ?_, ?_⟩
    · have hexp : value.exponent = format.quantumExponent value + shift := by
        simp only [Int.ofNat_eq_natCast] at heq
        omega
      rw [toRat_eq_signRat, hexp, zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), zpow_natCast,
        Nat.shiftLeft_eq', Nat.shiftLeft_eq]
      push_cast
      ring
    · simp [roundAway]
    · rw [toRat_eq_signRat]
  next _ shift heq =>
    refine ⟨Nat.shiftRight value.significand (shift + 1),
      shiftRightRemainder value.significand (shift + 1), shift + 1, ?_, ?_, ?_, ?_⟩
    · rw [shiftRightRemainder_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · have hexp : value.exponent = format.quantumExponent value - (shift + 1 : Nat) := by
        rw [Int.negSucc_eq] at heq
        push_cast
        omega
      rw [toRat_eq_signRat, hexp, zpow_sub₀ (by norm_num : (2 : Rat) ≠ 0), zpow_natCast,
        shiftRightRemainder_eq_mod, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
      have hdecompose := Nat.div_add_mod value.significand (2 ^ (shift + 1))
      have hcast : (value.significand : Rat) =
          2 ^ (shift + 1) * ((value.significand / 2 ^ (shift + 1) : Nat) : Rat) +
            ((value.significand % 2 ^ (shift + 1) : Nat) : Rat) := by
        exact_mod_cast hdecompose.symm
      have hpow : ((2 : Rat) ^ (shift + 1)) ≠ 0 := by positivity
      rw [hcast]
      field_simp
    · split <;> rename_i hrounded
      all_goals (split <;> simp_all)
    · split <;> rename_i hrounded
      · rw [toRat_eq_signRat]
        push_cast
        ring
      · split <;> rename_i hl
        · simp_all
        · rw [toRat_eq_signRat]

/-- The half point `2^(d-1)` of a `d`-bit remainder, as a rational. -/
private theorem half_cast (d : Nat) (hd : 0 < d) :
    ((Nat.shiftLeft 1 (d - 1) : Nat) : Rat) = 2 ^ d / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul, Nat.add_sub_cancel, pow_succ]
  push_cast
  ring

/-- The scaled fraction `rem / 2^d` compared with one half, in natural-number form. -/
private theorem half_le_iff (rem d : Nat) (hd : 0 < d) :
    Nat.shiftLeft 1 (d - 1) ≤ rem ↔ (1 / 2 : Rat) ≤ (rem : Rat) / 2 ^ d := by
  rw [← Nat.cast_le (α := Rat), half_cast d hd, le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

private theorem half_lt_iff (rem d : Nat) (hd : 0 < d) :
    Nat.shiftLeft 1 (d - 1) < rem ↔ (1 / 2 : Rat) < (rem : Rat) / 2 ^ d := by
  rw [← Nat.cast_lt (α := Rat), half_cast d hd, lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

private theorem eq_half_iff (rem d : Nat) (hd : 0 < d) :
    rem = Nat.shiftLeft 1 (d - 1) ↔ (rem : Rat) / 2 ^ d = 1 / 2 := by
  rw [← Nat.cast_inj (R := Rat), half_cast d hd, div_eq_iff (by positivity)]
  constructor <;> intro h <;> linarith

private theorem fraction_nonneg (rem d : Nat) : (0 : Rat) ≤ (rem : Rat) / 2 ^ d := by
  positivity

private theorem fraction_lt_one (rem d : Nat) (hrem : rem < 2 ^ d) :
    (rem : Rat) / 2 ^ d < 1 := by
  have hpow : (0 : Rat) < 2 ^ d := by positivity
  rw [div_lt_one hpow]
  exact_mod_cast hrem

private theorem fraction_pos (rem d : Nat) (hrem : rem ≠ 0) :
    (0 : Rat) < (rem : Rat) / 2 ^ d := by
  have hpow : (0 : Rat) < 2 ^ d := by positivity
  apply div_pos _ hpow
  exact_mod_cast Nat.pos_of_ne_zero hrem

private theorem pos_of_rem_ne_zero (rem d : Nat) (hrem : rem < 2 ^ d) (hne : rem ≠ 0) :
    0 < d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    omega
  · exact hd

private theorem abs_signRat_sub (negative : Bool) (a b u : Rat) (hu : 0 < u) :
    |signRat negative * a * u - signRat negative * b * u| = |a - b| * u := by
  rw [show signRat negative * a * u - signRat negative * b * u =
    signRat negative * (a - b) * u by ring]
  exact abs_signRat_mul negative (a - b) u hu

private theorem roundFiniteToPrecision_of_significand_eq_zero
    (format : Format) (mode : RoundingMode) (value : Numerics.Dyadic)
    (hzero : value.significand = 0) :
    format.roundFiniteToPrecision mode value = .zero := by
  simp [roundFiniteToPrecision, hzero]

private theorem abs_mul_le_half (a u : Rat) (hu : 0 < u) (h : |a| ≤ 1 / 2) :
    |a| * u ≤ u / 2 := by
  have := mul_le_mul_of_nonneg_right h hu.le
  linarith

private theorem abs_mul_lt_of_lt_one (a u : Rat) (hu : 0 < u) (h : |a| < 1) :
    |a| * u < u := by
  have := mul_lt_mul_of_pos_right h hu
  linarith

/--
Structural description of an exact tie under any rounding mode.

The discarded fraction is exactly one half, so the input is `sign * (lower + 1/2) * 2^Q`, and
the result significand is `lower` or `lower + 1` exactly as `roundAway` decides when the
remainder equals the half point `2^(d-1)`.
-/
private theorem roundFiniteToPrecision_tie_spec
    (format : Format) (mode : RoundingMode) (value : Numerics.Dyadic)
    (htie :
      |(format.roundFiniteToPrecision mode value).toRat - value.toRat| =
        (2 : Rat) ^ format.quantumExponent value / 2) :
    ∃ lower d : Nat, 0 < d ∧ Nat.shiftLeft 1 (d - 1) ≠ 0 ∧
      value.toRat =
        signRat value.negative * ((lower : Rat) + 1 / 2) *
          (2 : Rat) ^ format.quantumExponent value ∧
      (format.roundFiniteToPrecision mode value).significand =
        (if roundAway format mode value.negative (format.quantumExponent value)
            lower (Nat.shiftLeft 1 (d - 1)) d then lower + 1 else lower) ∧
      (format.roundFiniteToPrecision mode value).toRat =
        signRat value.negative *
          ((format.roundFiniteToPrecision mode value).significand : Rat) *
          (2 : Rat) ^ format.quantumExponent value := by
  have hu := format.quantum_pos value
  rcases Nat.eq_zero_or_pos value.significand with hzero | hpos
  · rw [roundFiniteToPrecision_of_significand_eq_zero format mode value hzero,
      (Numerics.Dyadic.toRat_eq_zero_iff value).2 hzero] at htie
    simp at htie
    linarith
  obtain ⟨lower, rem, d, hrem, hX, hsig, hY⟩ :=
    roundFiniteToPrecision_spec format mode value hpos.ne'
  have hf : (rem : Rat) / 2 ^ d = 1 / 2 := by
    rw [hY, hX, abs_signRat_sub _ _ _ _ hu] at htie
    have habs : |((if roundAway format mode value.negative (format.quantumExponent value)
        lower rem d then lower + 1 else lower : Nat) : Rat) -
          ((lower : Rat) + (rem : Rat) / 2 ^ d)| = 1 / 2 := by
      rw [hsig] at htie
      exact mul_right_cancel₀ hu.ne' (by linarith)
    have hf0 := fraction_nonneg rem d
    have hf1 := fraction_lt_one rem d hrem
    rcases (abs_eq (by norm_num : (0 : Rat) ≤ 1 / 2)).mp habs with h | h <;>
      split_ifs at h <;> push_cast at h <;> linarith
  have hremZero : rem ≠ 0 := by
    rintro rfl
    simp at hf
  have hd := pos_of_rem_ne_zero rem d hrem hremZero
  have heq : rem = Nat.shiftLeft 1 (d - 1) := (eq_half_iff rem d hd).2 hf
  exact ⟨lower, d, hd, heq ▸ hremZero, by rw [hX, hf], heq ▸ hsig, hY⟩

end Internal

open Internal in
/-- Precision rounding keeps the selected quantum exponent whenever the result is nonzero. -/
theorem roundFiniteToPrecision_exponent
    (format : Format) (mode : RoundingMode) (value : Numerics.Dyadic)
    (hresult : (format.roundFiniteToPrecision mode value).significand ≠ 0) :
    (format.roundFiniteToPrecision mode value).exponent = format.quantumExponent value := by
  rcases Nat.eq_zero_or_pos value.significand with hzero | hpos
  · rw [roundFiniteToPrecision_of_significand_eq_zero format mode value hzero] at hresult
    exact absurd rfl hresult
  · have hq :
        max (Int.ofNat value.significand.log2 + value.exponent)
            format.minimumNormalExponent - Int.ofNat format.precision + 1 =
          format.quantumExponent value := rfl
    unfold roundFiniteToPrecision at hresult ⊢
    simp only [beq_iff_eq, hpos.ne', if_false] at hresult ⊢
    rw [hq] at hresult ⊢
    generalize value.exponent - format.quantumExponent value = e at hresult ⊢
    cases e with
    | ofNat shift => rfl
    | negSucc shift =>
        dsimp only at hresult ⊢
        split <;> rename_i hr <;> simp only [hr, if_true] at hresult <;>
          split <;> rename_i hl <;> simp_all

open Internal in
/--
The rounded result is an integer multiple of the quantum `2^Q`.

Together with the direction theorems below this pins the result down to one of the two grid
points bracketing the input.
-/
theorem roundFiniteToPrecision_toRat_eq_int_mul
    (format : Format) (mode : RoundingMode) (value : Numerics.Dyadic) :
    ∃ n : Int, (format.roundFiniteToPrecision mode value).toRat =
      (n : Rat) * (2 : Rat) ^ format.quantumExponent value := by
  by_cases hresult : (format.roundFiniteToPrecision mode value).significand = 0
  · refine ⟨0, ?_⟩
    rw [(Numerics.Dyadic.toRat_eq_zero_iff _).2 hresult]
    simp
  · refine ⟨(format.roundFiniteToPrecision mode value).signedSignificand, ?_⟩
    rw [Numerics.Dyadic.toRat, roundFiniteToPrecision_exponent format mode value hresult,
      Rat.ofInt_eq_cast]

/-! ## Directed modes -/

open Internal in
/--
`towardZero` truncates: the result never exceeds the input in magnitude and is within one
quantum of it.
-/
theorem roundFiniteToPrecision_towardZero
    (format : Format) (value : Numerics.Dyadic) :
    |(format.roundFiniteToPrecision .towardZero value).toRat| ≤ |value.toRat| ∧
      |value.toRat| <
        |(format.roundFiniteToPrecision .towardZero value).toRat| +
          (2 : Rat) ^ format.quantumExponent value := by
  have hu := format.quantum_pos value
  rcases Nat.eq_zero_or_pos value.significand with hzero | hpos
  · rw [roundFiniteToPrecision_of_significand_eq_zero format _ value hzero,
      (Numerics.Dyadic.toRat_eq_zero_iff value).2 hzero]
    simp [hu]
  · obtain ⟨lower, rem, d, hrem, hX, hsig, hY⟩ :=
      roundFiniteToPrecision_spec format .towardZero value hpos.ne'
    simp only [roundAway, Bool.false_eq_true, if_false, ite_self] at hsig
    rw [hY, hX, hsig, abs_signRat_mul _ _ _ hu, abs_signRat_mul _ _ _ hu]
    have hf0 := fraction_nonneg rem d
    have hf1 := fraction_lt_one rem d hrem
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    constructor
    · nlinarith
    · nlinarith

open Internal in
/-- Every grid point no larger in magnitude than the input is no larger than the truncation. -/
theorem roundFiniteToPrecision_towardZero_maximal
    (format : Format) (value : Numerics.Dyadic) (n : Int)
    (hn : |(n : Rat)| * (2 : Rat) ^ format.quantumExponent value ≤ |value.toRat|) :
    |(n : Rat)| * (2 : Rat) ^ format.quantumExponent value ≤
      |(format.roundFiniteToPrecision .towardZero value).toRat| := by
  have hu := format.quantum_pos value
  obtain ⟨m, hm⟩ := format.roundFiniteToPrecision_toRat_eq_int_mul .towardZero value
  have hbracket := (format.roundFiniteToPrecision_towardZero value).2
  rw [hm, abs_mul, abs_of_pos hu] at hbracket ⊢
  have hlt : |(n : Rat)| < |(m : Rat)| + 1 := by
    have : |(n : Rat)| * 2 ^ format.quantumExponent value <
        (|(m : Rat)| + 1) * 2 ^ format.quantumExponent value := by
      linarith
    exact lt_of_mul_lt_mul_right this hu.le
  have hle : |(n : Rat)| ≤ |(m : Rat)| := by
    have hcast : ((|n| : Int) : Rat) < ((|m| : Int) : Rat) + 1 := by
      simpa [Int.cast_abs] using hlt
    have hint : |n| < |m| + 1 := by exact_mod_cast hcast
    have hcast' : ((|n| : Int) : Rat) ≤ ((|m| : Int) : Rat) := by
      exact_mod_cast Int.lt_add_one_iff.mp hint
    simpa [Int.cast_abs] using hcast'
  exact mul_le_mul_of_nonneg_right hle hu.le

open Internal in
/-- `towardPositive` never rounds down and stays within one quantum above the input. -/
theorem roundFiniteToPrecision_towardPositive
    (format : Format) (value : Numerics.Dyadic) :
    value.toRat ≤ (format.roundFiniteToPrecision .towardPositive value).toRat ∧
      (format.roundFiniteToPrecision .towardPositive value).toRat <
        value.toRat + (2 : Rat) ^ format.quantumExponent value := by
  have hu := format.quantum_pos value
  rcases Nat.eq_zero_or_pos value.significand with hzero | hpos
  · rw [roundFiniteToPrecision_of_significand_eq_zero format _ value hzero,
      (Numerics.Dyadic.toRat_eq_zero_iff value).2 hzero]
    simp [hu]
  · obtain ⟨lower, rem, d, hrem, hX, hsig, hY⟩ :=
      roundFiniteToPrecision_spec format .towardPositive value hpos.ne'
    have hf0 := fraction_nonneg rem d
    have hf1 := fraction_lt_one rem d hrem
    have hfu : (rem : Rat) / 2 ^ d * 2 ^ format.quantumExponent value <
        2 ^ format.quantumExponent value := by
      simpa using mul_lt_mul_of_pos_right hf1 hu
    have hfu0 : 0 ≤ (rem : Rat) / 2 ^ d * 2 ^ format.quantumExponent value :=
      mul_nonneg hf0 hu.le
    by_cases hremZero : rem = 0
    · subst hremZero
      simp only [roundAway, beq_self_eq_true, if_true, Bool.false_eq_true] at hsig
      rw [hY, hX, hsig]
      simp [hu]
    · have hf := fraction_pos rem d hremZero
      have hfu' : 0 < (rem : Rat) / 2 ^ d * 2 ^ format.quantumExponent value :=
        mul_pos hf hu
      cases hneg : value.negative
      · simp [roundAway, hremZero, hneg] at hsig
        rw [hY, hX, hsig, hneg]
        simp only [signRat, Bool.false_eq_true, if_false, one_mul]
        push_cast
        constructor <;> nlinarith
      · simp [roundAway, hremZero, hneg] at hsig
        rw [hY, hX, hsig, hneg]
        simp only [signRat, if_true]
        constructor <;> nlinarith

open Internal in
/-- `towardNegative` never rounds up and stays within one quantum below the input. -/
theorem roundFiniteToPrecision_towardNegative
    (format : Format) (value : Numerics.Dyadic) :
    (format.roundFiniteToPrecision .towardNegative value).toRat ≤ value.toRat ∧
      value.toRat <
        (format.roundFiniteToPrecision .towardNegative value).toRat +
          (2 : Rat) ^ format.quantumExponent value := by
  have hu := format.quantum_pos value
  rcases Nat.eq_zero_or_pos value.significand with hzero | hpos
  · rw [roundFiniteToPrecision_of_significand_eq_zero format _ value hzero,
      (Numerics.Dyadic.toRat_eq_zero_iff value).2 hzero]
    simp [hu]
  · obtain ⟨lower, rem, d, hrem, hX, hsig, hY⟩ :=
      roundFiniteToPrecision_spec format .towardNegative value hpos.ne'
    have hf0 := fraction_nonneg rem d
    have hf1 := fraction_lt_one rem d hrem
    have hfu : (rem : Rat) / 2 ^ d * 2 ^ format.quantumExponent value <
        2 ^ format.quantumExponent value := by
      simpa using mul_lt_mul_of_pos_right hf1 hu
    have hfu0 : 0 ≤ (rem : Rat) / 2 ^ d * 2 ^ format.quantumExponent value :=
      mul_nonneg hf0 hu.le
    by_cases hremZero : rem = 0
    · subst hremZero
      simp only [roundAway, beq_self_eq_true, if_true, Bool.false_eq_true] at hsig
      rw [hY, hX, hsig]
      simp [hu]
    · have hf := fraction_pos rem d hremZero
      have hfu' : 0 < (rem : Rat) / 2 ^ d * 2 ^ format.quantumExponent value :=
        mul_pos hf hu
      cases hneg : value.negative
      · simp [roundAway, hremZero, hneg] at hsig
        rw [hY, hX, hsig, hneg]
        simp only [signRat, Bool.false_eq_true, if_false, one_mul]
        constructor <;> nlinarith
      · simp [roundAway, hremZero, hneg] at hsig
        rw [hY, hX, hsig, hneg]
        simp only [signRat, if_true]
        push_cast
        constructor <;> nlinarith

/-- Every grid point at or above the input is at or above the `towardPositive` result. -/
theorem roundFiniteToPrecision_towardPositive_minimal
    (format : Format) (value : Numerics.Dyadic) (n : Int)
    (hn : value.toRat ≤ (n : Rat) * (2 : Rat) ^ format.quantumExponent value) :
    (format.roundFiniteToPrecision .towardPositive value).toRat ≤
      (n : Rat) * (2 : Rat) ^ format.quantumExponent value := by
  have hu := format.quantum_pos value
  obtain ⟨m, hm⟩ := format.roundFiniteToPrecision_toRat_eq_int_mul .towardPositive value
  have hbracket := (format.roundFiniteToPrecision_towardPositive value).2
  rw [hm] at hbracket ⊢
  have hlt : (m : Rat) < (n : Rat) + 1 := by
    have : (m : Rat) * 2 ^ format.quantumExponent value <
        ((n : Rat) + 1) * 2 ^ format.quantumExponent value := by
      linarith
    exact lt_of_mul_lt_mul_right this hu.le
  have hint : m < n + 1 := by exact_mod_cast hlt
  have hle : (m : Rat) ≤ (n : Rat) := by exact_mod_cast (Int.lt_add_one_iff.mp hint)
  exact mul_le_mul_of_nonneg_right hle hu.le

/-- Every grid point at or below the input is at or below the `towardNegative` result. -/
theorem roundFiniteToPrecision_towardNegative_maximal
    (format : Format) (value : Numerics.Dyadic) (n : Int)
    (hn : (n : Rat) * (2 : Rat) ^ format.quantumExponent value ≤ value.toRat) :
    (n : Rat) * (2 : Rat) ^ format.quantumExponent value ≤
      (format.roundFiniteToPrecision .towardNegative value).toRat := by
  have hu := format.quantum_pos value
  obtain ⟨m, hm⟩ := format.roundFiniteToPrecision_toRat_eq_int_mul .towardNegative value
  have hbracket := (format.roundFiniteToPrecision_towardNegative value).2
  rw [hm] at hbracket ⊢
  have hlt : (n : Rat) < (m : Rat) + 1 := by
    have : (n : Rat) * 2 ^ format.quantumExponent value <
        ((m : Rat) + 1) * 2 ^ format.quantumExponent value := by
      linarith
    exact lt_of_mul_lt_mul_right this hu.le
  have hint : n < m + 1 := by exact_mod_cast hlt
  have hle : (n : Rat) ≤ (m : Rat) := by exact_mod_cast (Int.lt_add_one_iff.mp hint)
  exact mul_le_mul_of_nonneg_right hle hu.le

/-! ## Nearest modes -/

open Internal in
/-- `nearestTiesToAway` rounds to within half a quantum of the input. -/
theorem roundFiniteToPrecision_nearestTiesToAway_abs_sub_le
    (format : Format) (value : Numerics.Dyadic) :
    |(format.roundFiniteToPrecision .nearestTiesToAway value).toRat - value.toRat| ≤
      (2 : Rat) ^ format.quantumExponent value / 2 := by
  have hu := format.quantum_pos value
  rcases Nat.eq_zero_or_pos value.significand with hzero | hpos
  · rw [roundFiniteToPrecision_of_significand_eq_zero format _ value hzero,
      (Numerics.Dyadic.toRat_eq_zero_iff value).2 hzero]
    simp
    positivity
  · obtain ⟨lower, rem, d, hrem, hX, hsig, hY⟩ :=
      roundFiniteToPrecision_spec format .nearestTiesToAway value hpos.ne'
    have hf0 := fraction_nonneg rem d
    have hf1 := fraction_lt_one rem d hrem
    by_cases hremZero : rem = 0
    · subst hremZero
      simp only [roundAway, beq_self_eq_true, if_true, Bool.false_eq_true] at hsig
      rw [hY, hX, hsig]
      simp
      positivity
    · have hd := pos_of_rem_ne_zero rem d hrem hremZero
      simp only [roundAway, hremZero, beq_iff_eq, if_false, decide_eq_true_eq] at hsig
      rw [hY, hX, hsig]
      by_cases hhalf : Nat.shiftLeft 1 (d - 1) ≤ rem
      · have hf := (half_le_iff rem d hd).1 hhalf
        rw [if_pos hhalf]
        push_cast
        rw [abs_signRat_sub _ _ _ _ hu]
        apply abs_mul_le_half _ _ hu
        rw [abs_le]
        constructor <;> linarith
      · have hf := (half_le_iff rem d hd).not.1 hhalf
        rw [if_neg hhalf, abs_signRat_sub _ _ _ _ hu]
        apply abs_mul_le_half _ _ hu
        rw [abs_le]
        constructor <;> linarith

open Internal in
/-- On an exact tie, `nearestTiesToAway` selects the candidate of larger magnitude. -/
theorem roundFiniteToPrecision_nearestTiesToAway_tie
    (format : Format) (value : Numerics.Dyadic)
    (htie :
      |(format.roundFiniteToPrecision .nearestTiesToAway value).toRat - value.toRat| =
        (2 : Rat) ^ format.quantumExponent value / 2) :
    |value.toRat| < |(format.roundFiniteToPrecision .nearestTiesToAway value).toRat| := by
  have hu := format.quantum_pos value
  obtain ⟨lower, d, hd, hhalf, hX, hsig, hY⟩ :=
    roundFiniteToPrecision_tie_spec format .nearestTiesToAway value htie
  simp only [roundAway, beq_iff_eq, hhalf, if_false, le_refl, decide_true, if_true] at hsig
  rw [hY, hX, hsig, abs_signRat_mul _ _ _ hu, abs_signRat_mul _ _ _ hu]
  push_cast
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  nlinarith

open Internal in
/-- `nearestTiesToEven` rounds to within half a quantum of the input. -/
theorem roundFiniteToPrecision_nearestTiesToEven_abs_sub_le
    (format : Format) (value : Numerics.Dyadic) :
    |(format.roundFiniteToPrecision .nearestTiesToEven value).toRat - value.toRat| ≤
      (2 : Rat) ^ format.quantumExponent value / 2 := by
  have hu := format.quantum_pos value
  rcases Nat.eq_zero_or_pos value.significand with hzero | hpos
  · rw [roundFiniteToPrecision_of_significand_eq_zero format _ value hzero,
      (Numerics.Dyadic.toRat_eq_zero_iff value).2 hzero]
    simp
    positivity
  · obtain ⟨lower, rem, d, hrem, hX, hsig, hY⟩ :=
      roundFiniteToPrecision_spec format .nearestTiesToEven value hpos.ne'
    have hf0 := fraction_nonneg rem d
    have hf1 := fraction_lt_one rem d hrem
    by_cases hremZero : rem = 0
    · subst hremZero
      simp only [roundAway, beq_self_eq_true, if_true, Bool.false_eq_true] at hsig
      rw [hY, hX, hsig]
      simp
      positivity
    · have hd := pos_of_rem_ne_zero rem d hrem hremZero
      simp only [roundAway, hremZero, beq_iff_eq, if_false] at hsig
      obtain ⟨half, hhalf⟩ : ∃ half, Nat.shiftLeft 1 (d - 1) = half := ⟨_, rfl⟩
      rw [hhalf] at hsig
      rw [hY, hX, abs_signRat_sub _ _ _ _ hu]
      apply abs_mul_le_half _ _ hu
      by_cases hlt : half < rem
      · have hf : (1 / 2 : Rat) < (rem : Rat) / 2 ^ d := by
          rw [← half_lt_iff rem d hd, hhalf]
          exact hlt
        simp only [hlt, decide_true, Bool.true_or, if_true] at hsig
        rw [hsig]
        push_cast
        rw [abs_le]
        constructor <;> linarith
      · by_cases heq : rem = half
        · have hf : (rem : Rat) / 2 ^ d = 1 / 2 := by
            rw [← eq_half_iff rem d hd, hhalf]
            exact heq
          have hc : (format.roundFiniteToPrecision .nearestTiesToEven value).significand =
              lower + 1 ∨
              (format.roundFiniteToPrecision .nearestTiesToEven value).significand = lower := by
            rw [hsig]
            split <;> simp
          rcases hc with hc | hc <;> rw [hc] <;> push_cast <;> rw [abs_le] <;>
            constructor <;> linarith
        · have hle : ¬ half ≤ rem := fun h =>
            (lt_or_eq_of_le h).elim hlt (fun h' => heq h'.symm)
          have hf : ¬ (1 / 2 : Rat) ≤ (rem : Rat) / 2 ^ d := by
            rw [← half_le_iff rem d hd, hhalf]
            exact hle
          have hbeq : (rem == half) = false := beq_eq_false_iff_ne.mpr heq
          simp only [hlt, hbeq, decide_false, Bool.false_or, Bool.false_and,
            Bool.false_eq_true, if_false] at hsig
          rw [hsig, abs_le]
          constructor <;> linarith

open Internal in
/--
On an exact tie, `nearestTiesToEven` selects the candidate whose P3109 code is even.

The input is exactly halfway between `lower * 2^Q` and `(lower + 1) * 2^Q` in magnitude, and the
result has magnitude `lower * 2^Q` precisely when the lower code is even under the report's
`CodeIsEven` rule (including its `P = 1` special case).
-/
theorem roundFiniteToPrecision_nearestTiesToEven_tie
    (format : Format) (value : Numerics.Dyadic)
    (htie :
      |(format.roundFiniteToPrecision .nearestTiesToEven value).toRat - value.toRat| =
        (2 : Rat) ^ format.quantumExponent value / 2) :
    ∃ lower : Nat,
      |value.toRat| = ((lower : Rat) + 1 / 2) * (2 : Rat) ^ format.quantumExponent value ∧
      (|(format.roundFiniteToPrecision .nearestTiesToEven value).toRat| =
          (lower : Rat) * (2 : Rat) ^ format.quantumExponent value ↔
        format.lowerCodeIsEven (format.quantumExponent value) lower = true) := by
  have hu := format.quantum_pos value
  obtain ⟨lower, d, hd, hhalf, hX, hsig, hY⟩ :=
    roundFiniteToPrecision_tie_spec format .nearestTiesToEven value htie
  simp only [roundAway, beq_iff_eq, hhalf, if_false, lt_self_iff_false, decide_false,
    Bool.false_or, beq_self_eq_true, Bool.true_and] at hsig
  refine ⟨lower, ?_, ?_⟩
  · rw [hX, abs_signRat_mul _ _ _ hu, abs_of_nonneg (by positivity)]
  · rw [hY, hsig, abs_signRat_mul _ _ _ hu]
    cases heven : format.lowerCodeIsEven (format.quantumExponent value) lower
    · simp only [Bool.not_false, if_true]
      push_cast
      rw [abs_of_nonneg (by positivity)]
      constructor
      · intro h
        exfalso
        linarith
      · intro h
        simp at h
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]
      rw [abs_of_nonneg (by positivity)]
      simp

open Internal in
/-- With more than one significand bit, a `nearestTiesToEven` tie yields an even significand. -/
theorem roundFiniteToPrecision_nearestTiesToEven_tie_even
    (format : Format) (value : Numerics.Dyadic) (hprecision : 1 < format.precision)
    (htie :
      |(format.roundFiniteToPrecision .nearestTiesToEven value).toRat - value.toRat| =
        (2 : Rat) ^ format.quantumExponent value / 2) :
    (format.roundFiniteToPrecision .nearestTiesToEven value).significand % 2 = 0 := by
  obtain ⟨lower, d, hd, hhalf, hX, hsig, hY⟩ :=
    roundFiniteToPrecision_tie_spec format .nearestTiesToEven value htie
  simp only [roundAway, beq_iff_eq, hhalf, if_false, lt_self_iff_false, decide_false,
    Bool.false_or, beq_self_eq_true, Bool.true_and, lowerCodeIsEven, hprecision, if_true] at hsig
  rw [hsig]
  rcases Nat.mod_two_eq_zero_or_one lower with hl | hl <;> simp [hl, Nat.add_mod]

/-! ## Round to odd -/

open Internal in
/-- `toOdd` stays within one quantum of the input. -/
theorem roundFiniteToPrecision_toOdd_abs_sub_lt
    (format : Format) (value : Numerics.Dyadic) :
    |(format.roundFiniteToPrecision .toOdd value).toRat - value.toRat| <
      (2 : Rat) ^ format.quantumExponent value := by
  have hu := format.quantum_pos value
  rcases Nat.eq_zero_or_pos value.significand with hzero | hpos
  · rw [roundFiniteToPrecision_of_significand_eq_zero format _ value hzero,
      (Numerics.Dyadic.toRat_eq_zero_iff value).2 hzero]
    simp [hu]
  · obtain ⟨lower, rem, d, hrem, hX, hsig, hY⟩ :=
      roundFiniteToPrecision_spec format .toOdd value hpos.ne'
    have hf0 := fraction_nonneg rem d
    have hf1 := fraction_lt_one rem d hrem
    rw [hY, hX, abs_signRat_sub _ _ _ _ hu]
    apply abs_mul_lt_of_lt_one _ _ hu
    by_cases hremZero : rem = 0
    · subst hremZero
      simp only [roundAway, beq_self_eq_true, if_true, Bool.false_eq_true] at hsig
      rw [hsig]
      simp
    · have hf := fraction_pos rem d hremZero
      have hc : (format.roundFiniteToPrecision .toOdd value).significand = lower + 1 ∨
          (format.roundFiniteToPrecision .toOdd value).significand = lower := by
        rw [hsig]
        split <;> simp
      rcases hc with hc | hc <;> rw [hc] <;> push_cast <;> rw [abs_lt] <;>
        constructor <;> linarith

open Internal in
/--
With more than one significand bit, `toOdd` returns an odd significand whenever rounding was
inexact.
-/
theorem roundFiniteToPrecision_toOdd_odd
    (format : Format) (value : Numerics.Dyadic) (hprecision : 1 < format.precision)
    (hinexact : (format.roundFiniteToPrecision .toOdd value).toRat ≠ value.toRat) :
    (format.roundFiniteToPrecision .toOdd value).significand % 2 = 1 := by
  rcases Nat.eq_zero_or_pos value.significand with hzero | hpos
  · rw [roundFiniteToPrecision_of_significand_eq_zero format _ value hzero,
      (Numerics.Dyadic.toRat_eq_zero_iff value).2 hzero] at hinexact
    simp at hinexact
  · obtain ⟨lower, rem, d, hrem, hX, hsig, hY⟩ :=
      roundFiniteToPrecision_spec format .toOdd value hpos.ne'
    by_cases hremZero : rem = 0
    · subst hremZero
      simp only [roundAway, beq_self_eq_true, if_true, Bool.false_eq_true] at hsig
      rw [hY, hX, hsig] at hinexact
      simp at hinexact
    · simp only [roundAway, hremZero, beq_iff_eq, if_false, lowerCodeIsEven, hprecision,
        if_true] at hsig
      rw [hsig]
      rcases Nat.mod_two_eq_zero_or_one lower with hl | hl <;> simp [hl, Nat.add_mod]

end Format
end FloatLib.Floats.Formats.P3109
