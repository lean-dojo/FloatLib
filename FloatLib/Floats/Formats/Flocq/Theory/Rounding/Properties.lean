/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Core

/-!
# Generic rounding properties

Generic-format rounding scales to an integer, applies a valid integer rounding rule, and scales
back by a positive radix power. From that construction comes the basic order sandwich: rounding
down gives a value at or below every valid rounding, and rounding up one at or above it.

No concrete precision family is assumed. These results are the reusable real-valued layer we use
when proving executable binary and rational rounding algorithms.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/-- Rounding toward negative infinity never exceeds the exact value. -/
theorem round_floor_le (x : ℝ) :
    round (β := β) (fexp := fexp) floorRound x ≤ x := by
  calc
    round (β := β) (fexp := fexp) floorRound x =
        (⌊scaledMantissa β fexp x⌋ : ℝ) *
          bpow β (cexp β fexp x) := rfl
    _ ≤ scaledMantissa β fexp x * bpow β (cexp β fexp x) :=
      mul_le_mul_of_nonneg_right (Int.floor_le _) (bpow.nonneg β _)
    _ = x := scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x

/-- Rounding toward positive infinity never falls below the exact value. -/
theorem le_round_ceil (x : ℝ) :
    x ≤ round (β := β) (fexp := fexp) ceilRound x := by
  calc
    x = scaledMantissa β fexp x * bpow β (cexp β fexp x) :=
      (scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x).symm
    _ ≤ (⌈scaledMantissa β fexp x⌉ : ℝ) *
          bpow β (cexp β fexp x) :=
      mul_le_mul_of_nonneg_right (Int.le_ceil _) (bpow.nonneg β _)
    _ = round (β := β) (fexp := fexp) ceilRound x := rfl

/-- Every valid integer rounding rule returns a value at least as large as the floor. -/
theorem floor_le_valid_round (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    floorRound x ≤ rnd x :=
  ValidRnd.le_of_intCast_le rnd (Int.floor_le x)

/-- Every valid integer rounding rule returns a value at most as large as the ceiling. -/
theorem valid_round_le_ceil (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    rnd x ≤ ceilRound x :=
  ValidRnd.le_of_le_intCast rnd (Int.le_ceil x)

/-- Every valid integer rounding chooses either floor or ceiling. -/
theorem valid_round_eq_floor_or_ceil (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    rnd x = floorRound x ∨ rnd x = ceilRound x := by
  have hfloor := floor_le_valid_round (rnd := rnd) x
  have hceil := valid_round_le_ceil (rnd := rnd) x
  by_cases hle : rnd x ≤ floorRound x
  · exact Or.inl (le_antisymm hle hfloor)
  · right
    have hsucc : floorRound x + 1 ≤ rnd x :=
      Int.add_one_le_iff.mpr (lt_of_not_ge hle)
    have hceilSucc : ceilRound x ≤ floorRound x + 1 := by
      exact Int.ceil_le_floor_add_one x
    exact le_antisymm hceil (hceilSucc.trans hsucc)

/-- Every valid format rounding lies above directed-down rounding. -/
theorem round_floor_le_round (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    round (β := β) (fexp := fexp) floorRound x ≤
      round (β := β) (fexp := fexp) rnd x :=
  round_le_round_of_le (floor_le_valid_round rnd _)

/-- Every valid format rounding lies below directed-up rounding. -/
theorem round_le_ceil (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    round (β := β) (fexp := fexp) rnd x ≤
      round (β := β) (fexp := fexp) ceilRound x :=
  round_le_round_of_le (valid_round_le_ceil rnd _)

/-- Every valid generic rounding chooses either directed-down or directed-up rounding. -/
theorem round_eq_floor_or_ceil (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    round (β := β) (fexp := fexp) rnd x =
        round (β := β) (fexp := fexp) floorRound x ∨
      round (β := β) (fexp := fexp) rnd x =
        round (β := β) (fexp := fexp) ceilRound x :=
  (valid_round_eq_floor_or_ceil rnd (scaledMantissa β fexp x)).imp round_congr round_congr

end FloatLib.Floats.Formats.Flocq
