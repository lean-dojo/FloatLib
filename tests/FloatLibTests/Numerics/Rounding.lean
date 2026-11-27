/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.RoundingProof

meta import FloatLib.Numerics.Enclosure.Interval.Rounding

/-!
# Tests of the binary-grid roundings of rational intervals

Lean's kernel decides the endpoints of `dyadicHull`, `relativeHull` and `quotientHull` on
literals, and `#guard` checks the same values in compiled code. The expected endpoints were
computed with the definitions these functions replace, and both agree on every input here. The
inputs cover endpoints of both signs, a zero interval, points already on the grid, a negative
relative exponent, and bit lengths past 256 bits. The last examples apply the containment
theorems, where the kernel computes a rounded interval and a theorem carries a real member into
it, and the endpoint equations, for every precision.
-/

namespace FloatLibTests.Numerics.Rounding

open FloatLib.Numerics FloatLib.Numerics.Interval

/-! ### The fixed grid -/

example : dyadicHull 4 ⟨1 / 3, 2 / 3⟩ = ⟨5 / 16, 11 / 16⟩ := by decide +kernel
example : dyadicHull 4 ⟨-1 / 3, 3 / 8⟩ = ⟨-3 / 8, 3 / 8⟩ := by decide +kernel
example : dyadicHull 0 ⟨-5 / 2, 7 / 3⟩ = ⟨-3, 3⟩ := by decide +kernel
example : dyadicHull 8 ⟨1 / 10 ^ 30, 1 / 10 ^ 30⟩ = ⟨0, 1 / 256⟩ := by decide +kernel
example : (OutwardRounding.grid 4).enclose? (1 / 3) = some ⟨5 / 16, 3 / 8⟩ := by decide +kernel

/-! ### Relative precision -/

example : roundDownRel 1 (3 / 2) = 3 / 2 ∧ roundUpRel 1 (3 / 2) = 3 / 2 := by decide +kernel
example : (3 / 16 : ℚ) < 4 / 21 ∧ roundDownRel 1 (3 / 16) = 3 / 16 ∧
    roundDownRel 1 (4 / 21) = 1 / 8 := by decide +kernel
example : relativeExponent 8 (1 / 3) = 9 ∧ relativeExponent 8 (1000 / 7) = 1 ∧
    relativeExponent 8 0 = 8 ∧ relativeExponent 8 (2 ^ 300 / 3) = -291 := by
  decide +kernel
example : relativeHull 8 ⟨1 / 3, 1000 / 7⟩ = ⟨85 / 256, 143⟩ := by decide +kernel
example : relativeHull 8 ⟨-10 ^ 50, 10 ^ 50⟩ = ⟨-274 * 2 ^ 158, 274 * 2 ^ 158⟩ := by
  decide +kernel
example : relativeHull 8 ⟨0, 0⟩ = ⟨0, 0⟩ := by decide +kernel
example : relativeHull 128 ⟨1 / 3, 2 / 3⟩ =
    ⟨113427455640312821154458202477256070485 / 2 ^ 128,
      226854911280625642308916404954512140971 / 2 ^ 128⟩ := by
  decide +kernel
example : encloseInterval? (OutwardRounding.relative 8) ⟨1 / 3, 1000 / 7⟩ =
    some ⟨85 / 256, 143⟩ := by
  decide +kernel

/-! ### The grid for quotients -/

example : gridBits 8 (1 / 10 ^ 30) = 107 ∧ gridBits 8 (-7 / 2) = 8 ∧ gridBits 8 0 = 9 ∧
    gridBits 8 (1 / (3 * 2 ^ 300)) = 309 := by
  decide +kernel
example : quotientHull 8 ⟨1 / 10 ^ 30, 1 / 10 ^ 30⟩ = ⟨81 / 2 ^ 106, 163 / 2 ^ 107⟩ := by
  decide +kernel
example : quotientHull 8 ⟨-7 / 2, 22 / 7⟩ = ⟨-7 / 2, 805 / 256⟩ := by decide +kernel
example : (OutwardRounding.quotient 8).enclose? (1 / 10 ^ 30) =
    some ⟨81 / 2 ^ 106, 163 / 2 ^ 107⟩ := by
  decide +kernel

/-! ### Compiled code -/

#guard dyadicHull 4 ⟨1 / 3, 2 / 3⟩ == ⟨5 / 16, 11 / 16⟩
#guard relativeHull 8 ⟨-10 ^ 50, 10 ^ 50⟩ == ⟨-274 * 2 ^ 158, 274 * 2 ^ 158⟩
#guard quotientHull 8 ⟨1 / 10 ^ 30, 1 / 10 ^ 30⟩ == ⟨81 / 2 ^ 106, 163 / 2 ^ 107⟩
#guard gridBits 8 (1 / (3 * 2 ^ 300)) == 309 && relativeExponent 8 (2 ^ 300 / 3) == -291

/-! ### Containment -/

/-- A real number between `1 / 3` and `2 / 3` lies between `5 / 16` and `11 / 16`. -/
example (x : ℝ) (hx : 1 / 3 ≤ x ∧ x ≤ 2 / 3) : 5 / 16 ≤ x ∧ x ≤ 11 / 16 := by
  have h := containsReal_dyadicHull 4 (I := ⟨1 / 3, 2 / 3⟩) (x := x) (by
    rw [containsReal_some_iff]
    push_cast
    exact hx)
  rw [show dyadicHull 4 ⟨1 / 3, 2 / 3⟩ = ⟨5 / 16, 11 / 16⟩ by decide +kernel,
    containsReal_some_iff] at h
  push_cast at h
  exact h

example (bits : ℕ) {I : Interval ℚ} {x : ℝ} (hx : I.ContainsReal some x) :
    (relativeHull bits I).ContainsReal some x ∧ (quotientHull bits I).ContainsReal some x :=
  ⟨containsReal_relativeHull bits hx, containsReal_quotientHull bits hx⟩

/-! ### The endpoint equations -/

/-- The floor and the ceiling of `-16 / 3`, read off the grid enclosure by the kernel. -/
example : ⌊(-1 / 3 : ℚ) * 2 ^ 4⌋ = -6 ∧ ⌈(-1 / 3 : ℚ) * 2 ^ 4⌉ = -5 := by
  rw [← BinaryGrid.enclose_lo_eq_floor, ← BinaryGrid.enclose_hi_eq_ceil]
  decide +kernel

/-- On the grid with no fractional bits, a coefficient is its integer. -/
example (z : ℤ) : BinaryGrid.toRat 0 z = z := by
  rw [BinaryGrid.toRat_eq_div]
  simp

/-- On the grid of integers the dyadic hull is the floor and the ceiling. -/
example (I : Interval ℚ) : (dyadicHull 0 I).lo = ⌊I.lo⌋ ∧ (dyadicHull 0 I).hi = ⌈I.hi⌉ := by
  rw [dyadicHull_lo, dyadicHull_hi]
  simp

/-- Zero has the exponent `bits`, rounds to itself, and gets one more fractional bit on the grid
for quotients. -/
example (bits : ℕ) : relativeExponent bits 0 = bits ∧ roundDownRel bits 0 = 0 ∧
    roundUpRel bits 0 = 0 ∧ gridBits bits 0 = bits + 1 := by
  rw [roundDownRel_def, roundUpRel_def, relativeExponent_def, gridBits_def]
  simp

/-- The relative roundings bracket every rational. -/
example (bits : ℕ) (q : ℚ) : roundDownRel bits q ≤ roundUpRel bits q :=
  (roundDownRel_le bits q).trans (le_roundUpRel bits q)

/-- Where the grid for quotients has `bits` fractional bits, it is the fixed grid. -/
example (bits : ℕ) (I : Interval ℚ) (hlo : gridBits bits I.lo = bits)
    (hhi : gridBits bits I.hi = bits) :
    (quotientHull bits I).lo = (dyadicHull bits I).lo ∧
      (quotientHull bits I).hi = (dyadicHull bits I).hi := by
  rw [quotientHull_lo, quotientHull_hi, dyadicHull_lo, dyadicHull_hi, hlo, hhi]
  exact ⟨rfl, rfl⟩

end FloatLibTests.Numerics.Rounding
