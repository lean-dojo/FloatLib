/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Calculation.Round

/-!
# Rounding to nearest with ties toward zero

IEEE 754-2019 §9.5 introduces one more rounding direction, used only by the augmented
arithmetic operations: the floating-point number nearest to the infinitely precise result, and
of two equally near ones the one of smaller magnitude. Riedy and Demmel, "Augmented Arithmetic
Operations Proposed for IEEE-754 2018" (ARITH 2018, Section III) call it roundTiesToZero, and
Boldo, Lauter and Muller, "Emulating Round-to-Nearest Ties-to-Zero 'Augmented' Floating-Point
Operations Using Round-to-Nearest Ties-to-Even Arithmetic" (IEEE Transactions on Computers 70(7),
2021, Section I) quote the standard's definition as `RN₀`.

On the integer grid this is `nearestChoice nearestTowardZeroChoice`: a midpoint `f + 1/2` above a
nonnegative integer `f` is positive and stays at `f`, and a midpoint above a negative integer is
negative and goes up to `f + 1`. It is a valid nearest rounding rule (`nearestChoiceValid`), so
the error of a rounded sum is representable (`add_round_error_generic`). This module proves that
it commutes with negation and that a nonnegative midpoint rounds to its floor.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

/--
Tie choice of rounding to nearest with ties toward zero, IEEE 754-2019 §9.5
roundTiesTowardZero: the midpoint above `f` goes up exactly when `f` is negative.
-/
def nearestTowardZeroChoice (f : ℤ) : Bool :=
  decide (f < 0)

/-- Nearest rounding with ties toward zero commutes with negation. -/
theorem negRound_nearestChoice_tieTowardZero :
    negRound (nearestChoice nearestTowardZeroChoice) = nearestChoice nearestTowardZeroChoice := by
  rw [negRound_nearestChoice]
  congr 1
  funext f
  simp only [nearestTowardZeroChoice]
  by_cases hf : f < 0 <;> simp [hf] <;> omega

/-- Nearest rounding with ties toward zero of a negated real is the negated rounding. -/
theorem nearestChoice_tieTowardZero_neg (x : ℝ) :
    nearestChoice nearestTowardZeroChoice (-x) = -nearestChoice nearestTowardZeroChoice x := by
  have h := congrFun negRound_nearestChoice_tieTowardZero (-x)
  simp only [negRound, neg_neg] at h
  omega

/-- A nonnegative midpoint rounds to its floor under ties toward zero. -/
theorem nearestChoice_tieTowardZero_of_fract_eq_half {x : ℝ} (hx : 0 ≤ x)
    (hfract : Int.fract x = 1 / 2) :
    nearestChoice nearestTowardZeroChoice x = ⌊x⌋ := by
  have hfloor : ¬ ⌊x⌋ < 0 := not_lt.mpr (Int.floor_nonneg.mpr hx)
  simp [nearestChoice, hfract, nearestTowardZeroChoice, hfloor]

/-- Away from a midpoint, rounding with ties toward zero is nearest-even rounding. -/
theorem nearestChoice_tieTowardZero_eq_nearestEven {x : ℝ} (hfract : Int.fract x ≠ 1 / 2) :
    nearestChoice nearestTowardZeroChoice x = nearestEven x := by
  rw [nearestChoice_eq_of_fract_ne_half nearestTowardZeroChoice nearestEvenChoice hfract,
    nearestChoice_even_eq]

end FloatLib.Floats.Formats.Flocq
