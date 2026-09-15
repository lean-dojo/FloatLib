/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Core

/-!
# Generic rounding properties

Rounding in the generic format scales to an integer, applies a valid integer rounding rule, and
scales back by a positive radix power. This construction gives the basic order sandwich:
directed down is below every valid rounding, and directed up is above it.

These results do not assume a concrete precision family. They form the reusable real-valued layer
used when proving executable binary and rational rounding algorithms.
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
    floorRound x ≤ rnd x := by
  unfold floorRound
  rw [← ValidRnd.id (rnd := rnd) ⌊x⌋]
  exact ValidRnd.monotone (rnd := rnd) (⌊x⌋ : ℝ) x (Int.floor_le x)

/-- Every valid integer rounding rule returns a value at most as large as the ceiling. -/
theorem valid_round_le_ceil (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    rnd x ≤ ceilRound x := by
  unfold ceilRound
  rw [← ValidRnd.id (rnd := rnd) ⌈x⌉]
  exact ValidRnd.monotone (rnd := rnd) x (⌈x⌉ : ℝ) (Int.le_ceil x)

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
      round (β := β) (fexp := fexp) rnd x := by
  have hi := floor_le_valid_round (rnd := rnd) (scaledMantissa β fexp x)
  have hiR : (floorRound (scaledMantissa β fexp x) : ℝ) ≤
      (rnd (scaledMantissa β fexp x) : ℝ) := by exact_mod_cast hi
  unfold round toReal
  exact mul_le_mul_of_nonneg_right
    hiR (bpow.nonneg β _)

/-- Every valid format rounding lies below directed-up rounding. -/
theorem round_le_ceil (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    round (β := β) (fexp := fexp) rnd x ≤
      round (β := β) (fexp := fexp) ceilRound x := by
  have hi := valid_round_le_ceil (rnd := rnd) (scaledMantissa β fexp x)
  have hiR : (rnd (scaledMantissa β fexp x) : ℝ) ≤
      (ceilRound (scaledMantissa β fexp x) : ℝ) := by exact_mod_cast hi
  unfold round toReal
  exact mul_le_mul_of_nonneg_right
    hiR (bpow.nonneg β _)

/-- Every valid generic rounding chooses either directed-down or directed-up rounding. -/
theorem round_eq_floor_or_ceil (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    round (β := β) (fexp := fexp) rnd x =
        round (β := β) (fexp := fexp) floorRound x ∨
      round (β := β) (fexp := fexp) rnd x =
        round (β := β) (fexp := fexp) ceilRound x := by
  rcases valid_round_eq_floor_or_ceil rnd (scaledMantissa β fexp x) with h | h
  · left
    unfold round
    rw [h]
  · right
    unfold round
    rw [h]

end FloatLib.Floats.Formats.Flocq
