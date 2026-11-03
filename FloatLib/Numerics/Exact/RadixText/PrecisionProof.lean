/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Exact.RadixText.Precision
import Mathlib.Tactic.Positivity.Finset

/-! # Laws of significant-digit rounding in any radix

The caller supplies integer rounding. These laws establish the grid, coefficient
bounds and value-preserving carry independently of decimal or binary descriptors.
-/

@[expose] public section

namespace FloatLib.Numerics.RadixText

/-- Carry changes the written scale without changing the numerical value. -/
theorem carry_value (radix : Nat) (hradix : 0 < radix) (digits : ℕ+)
    (coefficient : Nat) (quantum : Int) :
    ((carry radix digits coefficient quantum).1 : ℚ) *
      (radix : ℚ) ^ (carry radix digits coefficient quantum).2 =
        (coefficient : ℚ) * (radix : ℚ) ^ quantum := by
  have hr : (radix : ℚ) ≠ 0 := by exact_mod_cast hradix.ne'
  by_cases h : coefficient = radix ^ (digits : Nat)
  · have hp : (digits : Nat) - 1 + 1 = digits := Nat.sub_add_cancel digits.pos
    simp only [carry, ite_eq_left h]
    rw [h]
    simp only [Nat.cast_pow, zpow_add_one₀ hr]
    have hpow : (radix : ℚ) ^ ((digits : Nat) - 1) * radix =
        (radix : ℚ) ^ (digits : Nat) := by rw [← pow_succ, hp]
    rw [← hpow]
    ring
  · simp [carry, h]

/-- The written result denotes precisely the caller's integer rounding on the selected grid. -/
theorem significant_value (radix : Nat) (hradix : 0 < radix)
    (roundMagnitude : Bool → ℚ → Nat) (negative : Bool)
    (coefficient : Nat) (quantum : Int) (digits : ℕ+) :
    ((significant radix roundMagnitude negative coefficient quantum digits).1 : ℚ) *
      (radix : ℚ) ^ (significant radix roundMagnitude negative coefficient quantum digits).2 =
        (roundCoefficient radix roundMagnitude negative coefficient quantum
          (significantQuantum radix coefficient quantum digits) : ℚ) *
          (radix : ℚ) ^ significantQuantum radix coefficient quantum digits := by
  exact carry_value radix hradix digits _ _

/--
A nonzero coefficient scaled to its requested grid is `coefficient / radix ^ log` times
`radix ^ (digits - 1)`, with `log = Nat.log radix coefficient`: its leading digit sits at position
`digits - 1`.
-/
private theorem scaled_eq (radix : Nat) (hr : (0 : ℚ) < radix)
    (coefficient : Nat) (quantum : Int) (digits : ℕ+) (hc : coefficient ≠ 0) :
    (coefficient : ℚ) * (radix : ℚ) ^ quantum /
        (radix : ℚ) ^ significantQuantum radix coefficient quantum digits =
      (coefficient : ℚ) / (radix : ℚ) ^ Nat.log radix coefficient *
        (radix : ℚ) ^ ((digits : Nat) - 1) := by
  have he : significantQuantum radix coefficient quantum digits =
      quantum + (Nat.log radix coefficient : Int) - (((digits : Nat) - 1 : Nat) : Int) := by
    have := digits.pos
    simp only [significantQuantum, ite_eq_right hc]
    omega
  rw [he, zpow_sub₀ hr.ne', zpow_add₀ hr.ne', zpow_natCast, zpow_natCast]
  field_simp

/-- The coefficient before rounding is strictly smaller than the radix to the requested precision. -/
theorem scaled_lt (radix : Nat) (hradix : 1 < radix)
    (coefficient : Nat) (quantum : Int) (digits : ℕ+) :
    (coefficient : ℚ) * (radix : ℚ) ^ quantum /
      (radix : ℚ) ^ significantQuantum radix coefficient quantum digits <
        (radix : ℚ) ^ (digits : Nat) := by
  have hr : (0 : ℚ) < radix := by exact_mod_cast (Nat.zero_lt_of_lt hradix)
  by_cases hc : coefficient = 0
  · simp [hc, pow_pos hr]
  · have hlt : (coefficient : ℚ) / (radix : ℚ) ^ Nat.log radix coefficient < radix := by
      rw [div_lt_iff₀ (pow_pos hr _), ← pow_succ']
      exact_mod_cast Nat.lt_pow_succ_log_self hradix coefficient
    rw [scaled_eq radix hr coefficient quantum digits hc]
    calc _ < (radix : ℚ) * (radix : ℚ) ^ ((digits : Nat) - 1) :=
          mul_lt_mul_of_pos_right hlt (pow_pos hr _)
      _ = (radix : ℚ) ^ (digits : Nat) := by rw [← pow_succ', Nat.sub_add_cancel digits.pos]

/--
A nonzero coefficient scaled to its requested grid is at least `radix ^ (digits - 1)`, so its
leading digit sits at the requested precision.
-/
theorem scaled_lower (radix : Nat) (hradix : 1 < radix)
    (coefficient : Nat) (quantum : Int) (digits : ℕ+) (hc : coefficient ≠ 0) :
    (radix : ℚ) ^ ((digits : Nat) - 1) ≤
      (coefficient : ℚ) * (radix : ℚ) ^ quantum /
        (radix : ℚ) ^ significantQuantum radix coefficient quantum digits := by
  have hr : (0 : ℚ) < radix := by exact_mod_cast (Nat.zero_lt_of_lt hradix)
  have hle : (1 : ℚ) ≤ (coefficient : ℚ) / (radix : ℚ) ^ Nat.log radix coefficient := by
    rw [one_le_div (pow_pos hr _)]
    exact_mod_cast Nat.pow_log_le_self radix hc
  rw [scaled_eq radix hr coefficient quantum digits hc]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hle (pow_nonneg hr.le ((digits : Nat) - 1))

/-- For a nonzero input, a rounder between floor and ceiling emits the requested digit count. -/
theorem significant_coefficient_bounds (radix : Nat) (hradix : 1 < radix)
    (roundMagnitude : Bool → ℚ → Nat)
    (hlower : ∀ sign x, ⌊x⌋₊ ≤ roundMagnitude sign x)
    (hupper : ∀ sign x (n : Nat), 0 ≤ x → x ≤ (n : ℚ) → roundMagnitude sign x ≤ n)
    (negative : Bool) (coefficient : Nat) (quantum : Int) (digits : ℕ+)
    (hc : coefficient ≠ 0) :
    radix ^ ((digits : Nat) - 1) ≤
      (significant radix roundMagnitude negative coefficient quantum digits).1 ∧
    (significant radix roundMagnitude negative coefficient quantum digits).1 <
      radix ^ (digits : Nat) := by
  let x := (coefficient : ℚ) * (radix : ℚ) ^ quantum /
    (radix : ℚ) ^ significantQuantum radix coefficient quantum digits
  have hr : (0 : ℚ) < radix := by exact_mod_cast (Nat.zero_lt_of_lt hradix)
  have hx : 0 ≤ x := div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (zpow_pos hr _).le) (zpow_pos hr _).le
  have hu : roundMagnitude negative x ≤ radix ^ (digits : Nat) :=
    hupper negative x _ hx (by exact_mod_cast (scaled_lt radix hradix coefficient quantum digits).le)
  have hl : radix ^ ((digits : Nat) - 1) ≤ roundMagnitude negative x :=
    (Nat.le_floor (by exact_mod_cast scaled_lower radix hradix coefficient quantum digits hc)).trans
      (hlower negative x)
  unfold significant carry
  dsimp only
  split
  · exact ⟨le_rfl, Nat.pow_lt_pow_right hradix (by have hp := digits.pos; omega)⟩
  · rename_i hcarry
    exact ⟨hl, lt_of_le_of_ne hu hcarry⟩

/--
Enough requested digits preserve value whenever integer inputs are fixed by the rounder.

The digit bound already makes the radix positive.
-/
theorem significant_exact (radix : Nat)
    (roundMagnitude : Bool → ℚ → Nat)
    (hexact : ∀ sign (n : Nat), roundMagnitude sign (n : ℚ) = n)
    (negative : Bool) (coefficient : Nat) (quantum : Int) (digits : ℕ+)
    (hc : coefficient < radix ^ (digits : Nat)) :
    ((significant radix roundMagnitude negative coefficient quantum digits).1 : ℚ) *
      (radix : ℚ) ^ (significant radix roundMagnitude negative coefficient quantum digits).2 =
        (coefficient : ℚ) * (radix : ℚ) ^ quantum := by
  have hradix : 0 < radix := by
    rcases Nat.eq_zero_or_pos radix with hzero | hpositive
    · rw [hzero, Nat.zero_pow digits.pos] at hc
      omega
    · exact hpositive
  have hr : (radix : ℚ) ≠ 0 := by exact_mod_cast hradix.ne'
  rw [significant_value radix hradix]
  unfold roundCoefficient
  by_cases hz : coefficient = 0
  · have hzero : roundMagnitude negative 0 = 0 := hexact negative 0
    simp [hz, hzero]
  · have hlog := Nat.log_lt_of_lt_pow hz hc
    have hq : significantQuantum radix coefficient quantum digits ≤ quantum := by
      simp only [significantQuantum, ite_eq_right hz]
      omega
    let q := significantQuantum radix coefficient quantum digits
    have hscale : (coefficient : ℚ) * (radix : ℚ) ^ quantum / (radix : ℚ) ^ q =
        ((coefficient * radix ^ (quantum - q).toNat : Nat) : ℚ) := by
      rw [Nat.cast_mul, Nat.cast_pow, ← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hq),
        zpow_sub₀ hr, mul_div_assoc]
    rw [hscale, hexact, ← hscale, div_mul_cancel₀ _ (zpow_ne_zero _ hr)]

/-- An integer rounding error bound scales by the requested external grid unit. -/
theorem significant_error (radix : Nat) (hradix : 0 < radix)
    (roundMagnitude : Bool → ℚ → Nat) (error : ℚ)
    (herror : ∀ sign x, 0 ≤ x → |(roundMagnitude sign x : ℚ) - x| ≤ error)
    (negative : Bool) (coefficient : Nat) (quantum : Int) (digits : ℕ+) :
    |((significant radix roundMagnitude negative coefficient quantum digits).1 : ℚ) *
        (radix : ℚ) ^ (significant radix roundMagnitude negative coefficient quantum digits).2 -
      (coefficient : ℚ) * (radix : ℚ) ^ quantum| ≤
        error * (radix : ℚ) ^ significantQuantum radix coefficient quantum digits := by
  have hr : (0 : ℚ) < radix := by exact_mod_cast hradix
  let unit := (radix : ℚ) ^ significantQuantum radix coefficient quantum digits
  let value := (coefficient : ℚ) * (radix : ℚ) ^ quantum
  have hu : 0 < unit := zpow_pos hr _
  have hv : 0 ≤ value := mul_nonneg (Nat.cast_nonneg _) (zpow_pos hr _).le
  have he := mul_le_mul_of_nonneg_right (herror negative (value / unit)
    (div_nonneg hv hu.le)) hu.le
  have heq :
      |(roundMagnitude negative (value / unit) : ℚ) * unit - value| =
        |(roundMagnitude negative (value / unit) : ℚ) - value / unit| * unit := by
    calc
      _ = |((roundMagnitude negative (value / unit) : ℚ) - value / unit) * unit| := by
        rw [sub_mul, div_mul_cancel₀ _ hu.ne']
      _ = _ := by rw [abs_mul, abs_of_pos hu]
  rw [← heq] at he
  simpa only [significant_value radix hradix, roundCoefficient] using he

end FloatLib.Numerics.RadixText
