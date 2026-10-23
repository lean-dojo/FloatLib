/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Constants.Runtime
public import FloatLib.Numerics.Enclosure.Elementary.Proof
public import FloatLib.Numerics.Enclosure.Interval.BinaryGridProof
public import FloatLib.Numerics.Enclosure.Trigonometric.AtanProof
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Bounds for the cached constants

`piLevel_halfPi_spec`, `piLevel_twoOverPi_spec` and `ln2Fixed_spec` prove that the integers of
`Constants.Runtime` are lower bounds within two units of `π/2`, `2/π` and `log 2` times `2 ^ bits`,
for every `bits`. The proofs read the integers as the endpoints of the proved enclosures `piQuarter`
and `logSeries 2` (`piQuarterBounds_eq`, `ln2Bounds_eq`), bound the enclosure widths, and check
that the series degrees make those widths small at every precision.

Shifting such a bound to fewer bits keeps it within two units (`LowerApprox.shiftRight`), so every
read at any precision inherits the bound. The faithful read of `log 2` is within one unit and its
grid read encloses it. The cache returns the uncached values (`piLevelAt_eq`, `ln2FixedAt_eq`).
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.Constants

open Taylor

/-- `value` is a lower bound within two units of `c * 2 ^ bits`. -/
def LowerApprox (c : ℝ) (bits value : Nat) : Prop :=
  (value : ℝ) ≤ c * 2 ^ bits ∧ c * 2 ^ bits < value + 2

/-! ## The cache -/

/-- A cached `piLevel` is the uncached one. -/
theorem piLevelAt_eq (level : Nat) : piLevelAt level = piLevel (levelBits level) := by
  unfold piLevelAt
  split
  · simp [Internal.piCache, Internal.forceCache, Thunk.get]
  · rfl

/-- A cached `ln2Fixed` is the uncached one. -/
theorem ln2FixedAt_eq (level : Nat) : ln2FixedAt level = ln2Fixed (levelBits level) := by
  unfold ln2FixedAt
  split
  · simp [Internal.ln2Cache, Internal.forceCache, Thunk.get]
  · rfl

/-- The level of `bits` has at least `bits` fractional bits. -/
theorem le_levelBits_levelFor (bits : Nat) : bits ≤ levelBits (levelFor bits) := by
  unfold levelFor levelBits
  split
  · simpa using ‹bits ≤ 64›
  · rw [Nat.shiftLeft_eq]
    have hlog := Nat.lt_log2_self (n := (bits - 1) / 64)
    have hdiv := Nat.lt_mul_div_succ (bits - 1) (show 0 < 64 by decide)
    have hmul : 64 * ((bits - 1) / 64 + 1) ≤ 64 * 2 ^ (((bits - 1) / 64).log2 + 1) :=
      Nat.mul_le_mul_left 64 hlog
    omega

/-- More bits need the same or a higher level. -/
theorem levelFor_mono {bits bits' : Nat} (h : bits ≤ bits') : levelFor bits ≤ levelFor bits' := by
  unfold levelFor
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · have hdiv : (bits - 1) / 64 ≤ (bits' - 1) / 64 := Nat.div_le_div_right (by omega)
    have hlog : ((bits - 1) / 64).log2 ≤ ((bits' - 1) / 64).log2 :=
      (Nat.le_log2 (by omega)).mpr ((Nat.log2_self_le (by omega)).trans hdiv)
    omega

/-! ## Shifted and rounded reads -/

/-- Shifting a lower bound within two units to fewer bits keeps it within two units. -/
theorem LowerApprox.shiftRight {c : ℝ} {precision value : Nat}
    (h : LowerApprox c precision value) {bits : Nat} (hbits : bits ≤ precision) :
    LowerApprox c bits (value >>> (precision - bits)) := by
  obtain ⟨k, rfl⟩ : ∃ k, precision = bits + k := ⟨precision - bits, by omega⟩
  rw [Nat.add_sub_cancel_left, Nat.shiftRight_eq_div_pow]
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hscale : c * 2 ^ (bits + k) = c * 2 ^ bits * 2 ^ k := by ring
  have hfloor : ((value / 2 ^ k : ℕ) : ℝ) * 2 ^ k ≤ value := by
    exact_mod_cast Nat.div_mul_le_self value (2 ^ k)
  have hceil : value + 1 ≤ (value / 2 ^ k + 1) * 2 ^ k := by
    have := Nat.lt_mul_div_succ value (Nat.two_pow_pos k)
    rw [mul_comm] at this
    omega
  obtain ⟨hlo, hhi⟩ := h
  rw [hscale] at hlo hhi
  constructor
  · have : ((value / 2 ^ k : ℕ) : ℝ) * 2 ^ k ≤ c * 2 ^ bits * 2 ^ k := hfloor.trans hlo
    exact le_of_mul_le_mul_right this hpow
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simpa using hhi
    · have hceilReal : (value : ℝ) + 1 ≤ ((value / 2 ^ k : ℕ) + 1 : ℝ) * 2 ^ k := by
        exact_mod_cast hceil
      have htwo : (2 : ℝ) ≤ 2 ^ k := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
      have hlt : c * 2 ^ bits * 2 ^ k < (((value / 2 ^ k : ℕ) : ℝ) + 2) * 2 ^ k := by
        nlinarith
      exact lt_of_mul_lt_mul_right hlt hpow.le

/--
A lower bound within two units at 64 more bits, raised by one unit and rounded to `bits`, is
within one unit.
-/
theorem LowerApprox.abs_round_sub_lt {c : ℝ} {bits value : Nat}
    (h : LowerApprox c (bits + 64) value) :
    |(((value + 1 + 2 ^ 63) >>> 64 : ℕ) : ℝ) - c * 2 ^ bits| < 1 := by
  rw [Nat.shiftRight_eq_div_pow]
  set q := (value + 1 + 2 ^ 63) / 2 ^ 64
  have hfloor : (q : ℝ) * 2 ^ 64 ≤ value + 1 + 2 ^ 63 := by
    exact_mod_cast Nat.div_mul_le_self (value + 1 + 2 ^ 63) (2 ^ 64)
  have hceil : ((value + 1 + 2 ^ 63 : ℕ) : ℝ) < (q + 1) * 2 ^ 64 := by
    have := Nat.lt_mul_div_succ (value + 1 + 2 ^ 63) (Nat.two_pow_pos 64)
    rw [mul_comm] at this
    exact_mod_cast this
  obtain ⟨hlo, hhi⟩ := h
  have hscale : c * 2 ^ (bits + 64) = c * 2 ^ bits * 2 ^ 64 := by ring
  rw [hscale] at hlo hhi
  push_cast at hceil
  rw [abs_lt]
  constructor <;> nlinarith

/-! ## Machin's enclosure of π/4 -/

/-- `atanSmall (1/5)` at `degree` has radius `1 / (120 * 25 ^ degree)`. -/
private theorem atanRadius_one_div_five (degree : Nat) :
    atanRadius (1 / 5) (degree + 1) = 1 / (120 * 25 ^ degree) := by
  rw [atanRadius, abs_of_pos (by norm_num), show ((1 : ℚ) / 5) ^ 2 = 1 / 25 by norm_num,
    pow_succ, one_div_pow]
  field_simp
  norm_num

/-- `atanSmall (1/239)` at `degree` has radius `1 / (13651680 * 57121 ^ degree)`. -/
private theorem atanRadius_one_div_239 (degree : Nat) :
    atanRadius (1 / 239) (degree + 1) = 1 / (13651680 * 57121 ^ degree) := by
  rw [atanRadius, abs_of_pos (by norm_num), show ((1 : ℚ) / 239) ^ 2 = 1 / 57121 by norm_num,
    pow_succ, one_div_pow]
  field_simp
  norm_num

end FloatLib.Numerics.Enclosure.Constants

namespace FloatLib.Numerics.Enclosure

open Taylor

/-- Binary splitting writes an arctangent partial sum as `x` times one unreduced fraction. -/
theorem atanTaylor_eq_split (x : ℚ) (n : Nat) :
    atanTaylor x n =
      x * ((split (atanStep x) 0 n).constantTerm / (split (atanStep x) 0 n).denominator) := by
  rw [atanTaylor_eq_binarySplit]
  simp only [Taylor.atan, Rat.mkRat_eq_div]

/-- Machin's enclosure of π/4, with the radii of its two arctangent enclosures written out. -/
theorem piQuarter_eq (degree : Nat) :
    piQuarter degree =
      ⟨4 * (atanTaylor (1 / 5) (degree + 1) - 1 / (120 * 25 ^ degree)) -
          (atanTaylor (1 / 239) (degree + 1) + 1 / (13651680 * 57121 ^ degree)),
        4 * (atanTaylor (1 / 5) (degree + 1) + 1 / (120 * 25 ^ degree)) -
          (atanTaylor (1 / 239) (degree + 1) - 1 / (13651680 * 57121 ^ degree))⟩ := by
  simp only [piQuarter, atanSmall, RationalInterval.around, RationalInterval.scaleNonnegative,
    RationalInterval.sub, RationalInterval.add, RationalInterval.neg,
    Constants.atanRadius_one_div_five, Constants.atanRadius_one_div_239]
  congr 1 <;> ring

/-- Machin's enclosure of π/4 has width at most `1 / (12 * 25 ^ degree)`. -/
theorem piQuarter_width_le (degree : Nat) :
    (piQuarter degree).hi - (piQuarter degree).lo ≤ 1 / (12 * 25 ^ degree) := by
  rw [piQuarter_eq]
  dsimp only
  have hu : (0 : ℚ) < 25 ^ degree := by positivity
  have hpow : (25 : ℚ) ^ degree ≤ 57121 ^ degree := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  set w : ℚ := 1 / 25 ^ degree with hw
  have hwpos : 0 < w := by positivity
  have h120 : 1 / (120 * (25 : ℚ) ^ degree) = w / 120 := by rw [hw]; field_simp
  have h12 : 1 / (12 * (25 : ℚ) ^ degree) = w / 12 := by rw [hw]; field_simp
  have hlarge : 1 / (13651680 * (57121 : ℚ) ^ degree) ≤ w / 13651680 := by
    rw [hw, div_div, one_div_le_one_div (by positivity) (by positivity)]
    linarith
  rw [h120, h12]
  linarith

/-- Machin's enclosure contains π/4 and has width at most `1 / (12 * 25 ^ degree)`. -/
theorem piQuarter_bounds (degree : Nat) :
    ((piQuarter degree).lo : ℝ) ≤ Real.pi / 4 ∧ Real.pi / 4 ≤ (piQuarter degree).hi ∧
      ((piQuarter degree).hi : ℝ) - (piQuarter degree).lo ≤ 1 / (12 * 25 ^ degree) := by
  obtain ⟨hlo, hhi⟩ := contains_piQuarter degree
  refine ⟨hlo, hhi, ?_⟩
  have h : (((piQuarter degree).hi - (piQuarter degree).lo : ℚ) : ℝ) ≤
      ((1 / (12 * 25 ^ degree) : ℚ) : ℝ) := by exact_mod_cast piQuarter_width_le degree
  push_cast at h
  exact h

/-- The lower endpoint of Machin's enclosure exceeds two thirds. -/
theorem two_thirds_lt_piQuarter_lo (degree : Nat) : (2 / 3 : ℚ) < (piQuarter degree).lo := by
  obtain ⟨hlo, hhi, hwidth⟩ := piQuarter_bounds degree
  have hpi := Real.pi_gt_three
  have hsmall : (1 : ℝ) / (12 * 25 ^ degree) ≤ 1 / 12 :=
    one_div_le_one_div_of_le (by norm_num) (by
      have : (1 : ℝ) ≤ 25 ^ degree := one_le_pow₀ (by norm_num)
      linarith)
  have : ((2 / 3 : ℚ) : ℝ) < (piQuarter degree).lo := by push_cast; linarith
  exact_mod_cast this

/-- The lower endpoint of Machin's enclosure is positive. -/
theorem piQuarter_lo_pos (degree : Nat) : 0 < (piQuarter degree).lo :=
  lt_trans (by norm_num) (two_thirds_lt_piQuarter_lo degree)

end FloatLib.Numerics.Enclosure

namespace FloatLib.Numerics.Enclosure.Constants

open Taylor

/-- `piQuarterBounds degree` denotes the endpoints of `piQuarter degree`. -/
theorem piQuarterBounds_eq (degree : Nat) :
    ((piQuarterBounds degree).lower : ℚ) / (piQuarterBounds degree).denominator =
        (piQuarter degree).lo ∧
      ((piQuarterBounds degree).upper : ℚ) / (piQuarterBounds degree).denominator =
        (piQuarter degree).hi := by
  rw [piQuarter_eq, atanTaylor_eq_split, atanTaylor_eq_split]
  simp only [piQuarterBounds]
  generalize split (atanStep (1 / 5)) 0 (degree + 1) = five
  generalize split (atanStep (1 / 239)) 0 (degree + 1) = large
  have h5 : (five.denominator : ℚ) ≠ 0 := by exact_mod_cast five.denominator_pos.ne'
  have h239 : (large.denominator : ℚ) ≠ 0 := by exact_mod_cast large.denominator_pos.ne'
  have hu : (25 : ℚ) ^ degree ≠ 0 := by positivity
  have hv : (57121 : ℚ) ^ degree ≠ 0 := by positivity
  push_cast
  constructor <;> field_simp <;> ring

/-- `piDegree` makes the Machin enclosure narrow at its precision. -/
private theorem two_pow_succ_le_mul_pow_piDegree (bits : Nat) :
    2 ^ (bits + 1) ≤ 12 * 25 ^ piDegree bits := by
  unfold piDegree
  have hbits : bits + 1 ≤ 4 * (bits / 4) + 4 := by omega
  calc 2 ^ (bits + 1) ≤ 2 ^ (4 * (bits / 4) + 4) := Nat.pow_le_pow_right (by norm_num) hbits
    _ = 16 ^ (bits / 4) * 16 := by rw [pow_add, pow_mul]; norm_num
    _ ≤ 25 ^ (bits / 4) * 16 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) _)
    _ ≤ 25 ^ (bits / 4) * (12 * 25 ^ 4) := Nat.mul_le_mul_left _ (by norm_num)
    _ = 12 * 25 ^ (bits / 4 + 4) := by rw [pow_add]; ring

/-! ## π/2 and 2/π -/

/-- Natural division brackets the real quotient. -/
private theorem natCast_div_bounds (a b : Nat) (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b ∧ (a : ℝ) / b < (a / b : ℕ) + 1 := by
  have hbReal : (0 : ℝ) < b := by exact_mod_cast hb
  refine ⟨Nat.cast_div_le, ?_⟩
  rw [div_lt_iff₀ hbReal]
  have h : (a : ℝ) < b * ((a / b : ℕ) + 1) := by exact_mod_cast Nat.lt_mul_div_succ a hb
  linarith

/--
A floor quotient is a lower bound within two units of `c * 2 ^ bits` when the exact quotient is
`lo * 2 ^ bits` for an enclosure `[lo, hi]` of `c` of width at most `2 ^ -bits`.
-/
theorem LowerApprox.of_div {c lo hi : ℝ} {bits numerator denominator : Nat}
    (hdenominator : 0 < denominator)
    (hvalue : (numerator : ℝ) / denominator = lo * 2 ^ bits)
    (hlo : lo ≤ c) (hhi : c ≤ hi) (hwidth : (hi - lo) * 2 ^ bits ≤ 1) :
    LowerApprox c bits (numerator / denominator) := by
  obtain ⟨hfloor, hceil⟩ := natCast_div_bounds numerator denominator hdenominator
  rw [hvalue] at hfloor hceil
  have hpow : (0 : ℝ) ≤ 2 ^ bits := by positivity
  constructor
  · exact hfloor.trans (mul_le_mul_of_nonneg_right hlo hpow)
  · nlinarith [mul_le_mul_of_nonneg_right hhi hpow]

/-- A numerator whose quotient `value` is positive has `toNat` equal to `value * denominator`. -/
private theorem natCast_toNat_of_div {numerator : Int} {denominator : Nat} {value : ℚ}
    (hdenominator : 0 < denominator) (hvalue : (numerator : ℚ) / denominator = value)
    (hpos : 0 < value) : ((numerator.toNat : ℕ) : ℝ) = (value : ℝ) * denominator := by
  have hdenQ : (0 : ℚ) < denominator := by exact_mod_cast hdenominator
  have hnum : (numerator : ℚ) = value * denominator := by
    rw [← hvalue]
    field_simp
  have hnonneg : 0 ≤ numerator := by
    have : (0 : ℚ) ≤ numerator := by
      rw [hnum]
      positivity
    exact_mod_cast this
  have hz : ((numerator.toNat : ℕ) : ℤ) = numerator := Int.toNat_of_nonneg hnonneg
  have hcast : ((numerator.toNat : ℕ) : ℝ) = ((numerator : ℤ) : ℝ) := by exact_mod_cast hz
  rw [hcast]
  exact_mod_cast hnum

/-- `piLevel bits` holds `π / 2 * 2 ^ bits` to within two units below. -/
theorem piLevel_halfPi_spec (bits : Nat) :
    LowerApprox (Real.pi / 2) bits (piLevel bits).halfPi := by
  obtain ⟨hlo, hhi, hwidth⟩ := piQuarter_bounds (piDegree bits)
  obtain ⟨hlower, -⟩ := piQuarterBounds_eq (piDegree bits)
  have hden := (piQuarterBounds (piDegree bits)).denominator_pos
  have hcast := natCast_toNat_of_div hden hlower (piQuarter_lo_pos _)
  have hprec : (2 : ℝ) ^ (bits + 1) * (1 / (12 * 25 ^ piDegree bits)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    exact_mod_cast two_pow_succ_le_mul_pow_piDegree bits
  have hval : (piLevel bits).halfPi =
      ((piQuarterBounds (piDegree bits)).lower.toNat <<< (bits + 1)) /
        (piQuarterBounds (piDegree bits)).denominator := rfl
  rw [hval]
  apply LowerApprox.of_div hden (lo := 2 * ((piQuarter (piDegree bits)).lo : ℝ))
    (hi := 2 * ((piQuarter (piDegree bits)).hi : ℝ))
  · have hdenReal : (0 : ℝ) < (piQuarterBounds (piDegree bits)).denominator := by
      exact_mod_cast hden
    rw [Nat.shiftLeft_eq]
    push_cast
    rw [hcast]
    field_simp
    ring
  · linarith
  · linarith
  · calc (2 * ((piQuarter (piDegree bits)).hi : ℝ) - 2 * (piQuarter (piDegree bits)).lo) *
          2 ^ bits = 2 ^ (bits + 1) * ((piQuarter (piDegree bits)).hi -
            (piQuarter (piDegree bits)).lo) := by ring
      _ ≤ 2 ^ (bits + 1) * (1 / (12 * 25 ^ piDegree bits)) :=
        mul_le_mul_of_nonneg_left hwidth (by positivity)
      _ ≤ 1 := hprec

/-- `piLevel bits` holds `2 / π * 2 ^ bits` to within two units below. -/
theorem piLevel_twoOverPi_spec (bits : Nat) :
    LowerApprox (2 / Real.pi) bits (piLevel bits).twoOverPi := by
  obtain ⟨hlo, hhi, hwidth⟩ := piQuarter_bounds (piDegree bits)
  obtain ⟨-, hupper⟩ := piQuarterBounds_eq (piDegree bits)
  have hthird := two_thirds_lt_piQuarter_lo (piDegree bits)
  have hden := (piQuarterBounds (piDegree bits)).denominator_pos
  have hprec : (2 : ℝ) ^ (bits + 1) ≤ 12 * 25 ^ piDegree bits := by
    exact_mod_cast two_pow_succ_le_mul_pow_piDegree bits
  have hpi := Real.pi_gt_three
  set bounds := piQuarterBounds (piDegree bits)
  set lo := (piQuarter (piDegree bits)).lo
  set hi := (piQuarter (piDegree bits)).hi
  have hdenQ : (0 : ℚ) < bounds.denominator := by exact_mod_cast hden
  have hhiPos : (0 : ℚ) < hi := by
    have : ((2 / 3 : ℚ) : ℝ) < hi := by
      have : ((2 / 3 : ℚ) : ℝ) < lo := by exact_mod_cast hthird
      linarith [hlo, hhi]
    exact_mod_cast (lt_trans (by norm_num) this : ((0 : ℚ) : ℝ) < hi)
  have hupperPos : 0 < bounds.upper := by
    have : (0 : ℚ) < bounds.upper := (div_pos_iff_of_pos_right hdenQ).mp (hupper ▸ hhiPos)
    exact_mod_cast this
  have hcast : ((2 * bounds.upper.toNat : ℕ) : ℝ) = 2 * (hi : ℝ) * bounds.denominator := by
    have hq : (bounds.upper : ℚ) = hi * bounds.denominator := by
      rw [← hupper]; field_simp
    have : ((bounds.upper.toNat : ℕ) : ℤ) = bounds.upper := Int.toNat_of_nonneg hupperPos.le
    have hz : ((bounds.upper.toNat : ℕ) : ℝ) = ((bounds.upper : ℤ) : ℝ) := by exact_mod_cast this
    push_cast
    rw [hz]
    have : ((bounds.upper : ℤ) : ℝ) = (hi : ℝ) * bounds.denominator := by exact_mod_cast hq
    rw [this]
    ring
  have hupperNat : 0 < 2 * bounds.upper.toNat := by omega
  obtain ⟨hfloor, hceil⟩ := natCast_div_bounds (bounds.denominator <<< bits)
    (2 * bounds.upper.toNat) hupperNat
  have hdenReal : (0 : ℝ) < bounds.denominator := by exact_mod_cast hden
  have hhiReal : (3 / 4 : ℝ) < hi := by linarith
  have hscaled : ((bounds.denominator <<< bits : ℕ) : ℝ) / ((2 * bounds.upper.toNat : ℕ) : ℝ) =
      2 ^ bits / (2 * hi) := by
    rw [hcast, Nat.shiftLeft_eq]
    push_cast
    field_simp
  rw [hscaled] at hfloor hceil
  have hval : (piLevel bits).twoOverPi =
      (bounds.denominator <<< bits) / (2 * bounds.upper.toNat) := rfl
  rw [hval, LowerApprox]
  have hsmall : (2 : ℝ) ^ bits * (hi - lo) ≤ 1 / 2 := by
    have h1 : (2 : ℝ) ^ (bits + 1) * (hi - lo) ≤ 2 ^ (bits + 1) * (1 / (12 * 25 ^ piDegree bits)) :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    have h2 : (2 : ℝ) ^ (bits + 1) * (1 / (12 * 25 ^ piDegree bits)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      exact hprec
    rw [pow_succ] at h1 h2
    linarith
  have hquarter : (3 / 4 : ℝ) < Real.pi / 4 := by linarith
  have htwo : 2 / Real.pi * 2 ^ bits = 2 ^ bits / (2 * (Real.pi / 4)) := by
    field_simp
    ring
  rw [htwo]
  have hle : 2 ^ bits / (2 * hi) ≤ (2 : ℝ) ^ bits / (2 * (Real.pi / 4)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  constructor
  · exact hfloor.trans hle
  · have hdiff : (2 : ℝ) ^ bits / (2 * (Real.pi / 4)) - 2 ^ bits / (2 * hi) =
        2 ^ bits * (hi - Real.pi / 4) / (2 * (Real.pi / 4) * hi) := by
      field_simp
    have hnum : (2 : ℝ) ^ bits * (hi - Real.pi / 4) ≤ 1 / 2 := by
      have : (2 : ℝ) ^ bits * (hi - Real.pi / 4) ≤ 2 ^ bits * (hi - lo) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hdenom : (1 : ℝ) < 2 * (Real.pi / 4) * hi := by nlinarith
    have hfrac : (2 : ℝ) ^ bits * (hi - Real.pi / 4) / (2 * (Real.pi / 4) * hi) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    linarith

end FloatLib.Numerics.Enclosure.Constants

namespace FloatLib.Numerics.Enclosure

open Taylor

/-! ## log 2 -/

/-- Binary splitting writes a partial sum of `-log (1 - x)` as one unreduced fraction. -/
theorem logOneSubTaylor_eq_split (x : ℚ) (n : Nat) :
    logOneSubTaylor x n =
      (split (logStep x) 0 n).constantTerm / (split (logStep x) 0 n).denominator := by
  rw [logOneSubTaylor_eq_binarySplit]
  simp only [Taylor.logOneSub, Rat.mkRat_eq_div]

/-- Endpoints of `logSeries 2`, with the radii of both series in `1/3` written out. -/
theorem logSeries_two_eq (degree : Nat) :
    logSeries 2 degree =
      ⟨logOneSubTaylor (1 / 3) degree - logOneSubTaylor (-1 / 3) degree - 1 / 3 ^ degree,
        logOneSubTaylor (1 / 3) degree - logOneSubTaylor (-1 / 3) degree + 1 / 3 ^ degree⟩ := by
  have ht : ((2 : ℚ) - 1) / (2 + 1) = 1 / 3 := by norm_num
  have hneg : -((1 : ℚ) / 3) = -1 / 3 := by norm_num
  have habs : |(-1 / 3 : ℚ)| = 1 / 3 := by norm_num [abs_div]
  have habs' : |(1 / 3 : ℚ)| = 1 / 3 := by norm_num
  simp only [logSeries, ht, hneg, logOneSub, logOneSubRadius, RationalInterval.around,
    RationalInterval.sub, RationalInterval.add, RationalInterval.neg, habs, habs']
  have hradius : ((1 : ℚ) / 3) ^ (degree + 1) / (1 - 1 / 3) = 1 / 3 ^ degree / 2 := by
    rw [pow_succ, one_div_pow]
    field_simp
    norm_num
  rw [hradius]
  congr 1 <;> ring

end FloatLib.Numerics.Enclosure

namespace FloatLib.Numerics.Enclosure.Constants

open Taylor

/-- `ln2Bounds degree` denotes the endpoints of `logSeries 2 degree`. -/
theorem ln2Bounds_eq (degree : Nat) :
    ((ln2Bounds degree).lower : ℚ) / (ln2Bounds degree).denominator = (logSeries 2 degree).lo ∧
      ((ln2Bounds degree).upper : ℚ) / (ln2Bounds degree).denominator =
        (logSeries 2 degree).hi := by
  rw [logSeries_two_eq, logOneSubTaylor_eq_split, logOneSubTaylor_eq_split]
  simp only [ln2Bounds]
  generalize split (logStep (1 / 3)) 0 degree = plus
  generalize split (logStep (-1 / 3)) 0 degree = minus
  have hp : (plus.denominator : ℚ) ≠ 0 := by exact_mod_cast plus.denominator_pos.ne'
  have hm : (minus.denominator : ℚ) ≠ 0 := by exact_mod_cast minus.denominator_pos.ne'
  have hw : (3 : ℚ) ^ degree ≠ 0 := by positivity
  push_cast
  constructor <;> field_simp

/-- `ln2Degree` makes the series enclosure of `log 2` narrow at its precision. -/
private theorem two_pow_succ_le_three_pow_ln2Degree (bits : Nat) :
    2 ^ (bits + 1) ≤ 3 ^ ln2Degree bits := by
  unfold ln2Degree
  have hbits : bits + 1 ≤ 3 * (bits / 3) + 3 := by omega
  have hdegree : 2 * (bits / 3) + 8 ≤ 2 * bits / 3 + 8 := by omega
  calc 2 ^ (bits + 1) ≤ 2 ^ (3 * (bits / 3) + 3) := Nat.pow_le_pow_right (by norm_num) hbits
    _ = 8 ^ (bits / 3) * 8 := by rw [pow_add, pow_mul]; norm_num
    _ ≤ 9 ^ (bits / 3) * 8 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) _)
    _ ≤ 9 ^ (bits / 3) * 3 ^ 8 := Nat.mul_le_mul_left _ (by norm_num)
    _ = 3 ^ (2 * (bits / 3) + 8) := by rw [pow_add, pow_mul]; norm_num
    _ ≤ 3 ^ (2 * bits / 3 + 8) := Nat.pow_le_pow_right (by norm_num) hdegree

/-- `ln2Fixed bits` is within two units below `log 2 * 2 ^ bits`. -/
theorem ln2Fixed_spec (bits : Nat) : LowerApprox (Real.log 2) bits (ln2Fixed bits) := by
  obtain ⟨hlo, hhi⟩ := contains_logSeries 2 (ln2Degree bits) (by norm_num)
  simp only [Rat.cast_ofNat] at hlo hhi
  obtain ⟨hlower, -⟩ := ln2Bounds_eq (ln2Degree bits)
  have hden := (ln2Bounds (ln2Degree bits)).denominator_pos
  have hprec : (2 : ℝ) ^ (bits + 1) ≤ 3 ^ ln2Degree bits := by
    exact_mod_cast two_pow_succ_le_three_pow_ln2Degree bits
  have height : (3 : ℝ) ^ 8 ≤ 3 ^ ln2Degree bits :=
    pow_le_pow_right₀ (by norm_num) (by unfold ln2Degree; omega)
  have hwidth : ((logSeries 2 (ln2Degree bits)).hi : ℝ) - (logSeries 2 (ln2Degree bits)).lo =
      2 / 3 ^ ln2Degree bits := by
    rw [logSeries_two_eq]
    push_cast
    ring
  have hlog := Real.log_two_gt_d9
  have hpow : (0 : ℝ) < 3 ^ ln2Degree bits := by positivity
  have hpos : (0 : ℝ) < (logSeries 2 (ln2Degree bits)).lo := by
    have : (2 : ℝ) / 3 ^ ln2Degree bits ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hpow (by norm_num)]
      nlinarith
    linarith
  have hcast := natCast_toNat_of_div hden hlower (by exact_mod_cast hpos)
  apply LowerApprox.of_div hden (lo := ((logSeries 2 (ln2Degree bits)).lo : ℝ))
    (hi := ((logSeries 2 (ln2Degree bits)).hi : ℝ)) _ hlo hhi
  · rw [hwidth, div_mul_eq_mul_div, div_le_one hpow]
    rw [pow_succ] at hprec
    linarith
  · have hdenReal : (0 : ℝ) < (ln2Bounds (ln2Degree bits)).denominator := by exact_mod_cast hden
    rw [Nat.shiftLeft_eq]
    push_cast
    rw [hcast]
    field_simp

/-! ## Reads at any precision -/

/-- `halfPiLower bits` is within two units below `π / 2 * 2 ^ bits`. -/
theorem halfPiLower_spec (bits : Nat) : LowerApprox (Real.pi / 2) bits (halfPiLower bits) := by
  unfold halfPiLower
  dsimp only
  rw [piLevelAt_eq]
  exact (piLevel_halfPi_spec _).shiftRight (le_levelBits_levelFor bits)

/-- `twoOverPiLower bits` is within two units below `2 / π * 2 ^ bits`. -/
theorem twoOverPiLower_spec (bits : Nat) :
    LowerApprox (2 / Real.pi) bits (twoOverPiLower bits) := by
  unfold twoOverPiLower
  dsimp only
  rw [piLevelAt_eq]
  exact (piLevel_twoOverPi_spec _).shiftRight (le_levelBits_levelFor bits)

/-- `ln2Lower bits` is within two units below `log 2 * 2 ^ bits`. -/
theorem ln2Lower_spec (bits : Nat) : LowerApprox (Real.log 2) bits (ln2Lower bits) := by
  unfold ln2Lower
  dsimp only
  rw [ln2FixedAt_eq]
  exact (ln2Fixed_spec _).shiftRight (le_levelBits_levelFor bits)

/-- `ln2Faithful bits` is within one unit of `log 2 * 2 ^ bits`. -/
theorem abs_ln2Faithful_sub_lt_one (bits : Nat) :
    |(ln2Faithful bits : ℝ) - Real.log 2 * 2 ^ bits| < 1 :=
  (ln2Lower_spec (bits + 64)).abs_round_sub_lt

/-- The grid read of `log 2` encloses `log 2`. -/
theorem containsReal_ln2Grid (precision : Nat) :
    (ln2Grid precision).ContainsReal (Interval.BinaryGrid.decode precision) (Real.log 2) := by
  rw [Interval.BinaryGrid.containsReal_iff]
  obtain ⟨hlo, hhi⟩ := ln2Lower_spec (precision + 64)
  set lower := ln2Lower (precision + 64)
  have hscale : ((Interval.BinaryGrid.scale precision : ℤ) : ℝ) = 2 ^ precision := by
    rw [Interval.BinaryGrid.scale_eq_pow]
    push_cast
    ring
  have hpow : (0 : ℝ) < 2 ^ precision := by positivity
  have hpow64 : (0 : ℝ) < 2 ^ 64 := by positivity
  have hsplit : Real.log 2 * 2 ^ (precision + 64) = Real.log 2 * 2 ^ precision * 2 ^ 64 := by
    ring
  rw [hsplit] at hlo hhi
  simp only [ln2Grid, Interval.BinaryGrid.value, hscale, Int.ofNat_eq_natCast, Int.cast_natCast,
    Nat.shiftRight_eq_div_pow]
  constructor
  · rw [div_le_iff₀ hpow]
    have hfloor : ((lower / 2 ^ 64 : ℕ) : ℝ) * 2 ^ 64 ≤ lower := by
      exact_mod_cast Nat.div_mul_le_self lower (2 ^ 64)
    have : ((lower / 2 ^ 64 : ℕ) : ℝ) * 2 ^ 64 ≤ Real.log 2 * 2 ^ precision * 2 ^ 64 :=
      hfloor.trans hlo
    exact le_of_mul_le_mul_right this hpow64
  · rw [le_div_iff₀ hpow]
    have hceil : lower + 2 ≤ (lower + 2 + (2 ^ 64 - 1)) / 2 ^ 64 * 2 ^ 64 := by
      have := Nat.div_add_mod (lower + 2 + (2 ^ 64 - 1)) (2 ^ 64)
      have := Nat.mod_lt (lower + 2 + (2 ^ 64 - 1)) (Nat.two_pow_pos 64)
      have : 1 ≤ 2 ^ 64 := Nat.one_le_two_pow
      rw [mul_comm] at *
      omega
    have hceilReal : ((lower : ℝ) + 2) ≤
        (((lower + 2 + (2 ^ 64 - 1)) / 2 ^ 64 : ℕ) : ℝ) * 2 ^ 64 := by exact_mod_cast hceil
    have : Real.log 2 * 2 ^ precision * 2 ^ 64 ≤
        (((lower + 2 + (2 ^ 64 - 1)) / 2 ^ 64 : ℕ) : ℝ) * 2 ^ 64 := by linarith
    exact le_of_mul_le_mul_right this hpow64

end FloatLib.Numerics.Enclosure.Constants
