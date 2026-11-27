/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Numerics.Enclosure.Interval.TotalProof

/-!
# Enclosures of the total square root, arcsine, arccosine and logarithm

Values on literals, decided in Lean's kernel, at 12 square-root steps, 32 arcsine terms and
logarithm degree 20: exact roots of rational squares, `[0, 0]` below zero, arguments clamped to
`[-1, 1]`, the logarithm of a negative interval, and the intervals it refuses. Then the
containment theorems applied to real arguments.
-/

namespace FloatLibTests.Numerics.Total

open FloatLib.Numerics FloatLib.Numerics.Interval

/-! ## Square root -/

-- Rational squares come out exact, also when the denominator isn't a power of two.
example : Total.sqrtPoint 4 12 = point 2 := by decide +kernel

example : Total.sqrtPoint (9 / 4) 12 = point (3 / 2) := by decide +kernel

example : Total.sqrtPoint ((5 / 7) ^ 2) 12 = point (5 / 7) := Total.sqrtPoint_sq (by norm_num) 12

-- Otherwise the grid is `1 / (q.den * 2 ^ steps)`.
example : Total.sqrtPoint 2 12 = ⟨181 / 128, 5793 / 4096⟩ := by decide +kernel

example : Total.sqrtPoint (2 / 9) 12 = ⟨17377 / 36864, 8689 / 18432⟩ := by decide +kernel

example (q : ℚ) (h : q.den = 9) :
    (Total.sqrtPoint q 12).hi - (Total.sqrtPoint q 12).lo ≤ 1 / 36864 :=
  (Total.sqrtPoint_width_le q 12).trans (by rw [h]; norm_num)

-- Mathlib's square root is zero below zero.
example : Total.sqrtPoint (-1) 12 = point 0 := by decide +kernel

example : Total.sqrt ⟨-1, 4⟩ 12 = ⟨0, 2⟩ := by decide +kernel

/-! ## Arcsine and arccosine -/

example (fallback : Interval ℚ) (q : ℚ) (terms : Nat) :
    Total.inverseTrigPoint (fun _ _ _ => none) fallback q terms = fallback := rfl

-- Outside `[-1, 1]` the argument is clamped.
example : Total.asinPoint 2 32 = Total.asinPoint 1 32 := by decide +kernel

example : Total.asinPoint (-7 / 2) 32 = Total.asinPoint (-1) 32 := by decide +kernel

example : Total.acosPoint 5 32 = point 0 := by decide +kernel

example : Total.acos ⟨1, 3⟩ 32 = point 0 := by decide +kernel

-- `asinBounds?` keeps zero exact, and the grid keeps it too.
example : Total.asinPoint 0 32 = point 0 := by decide +kernel

-- `π / 2` on the grid of `2 ^ (-128)`.
example : Total.asinPoint 1 32 =
    ⟨267257146016241686964920093290467695825 / 170141183460469231731687303715884105728,
      534514292032483373929840186580935391651 / 340282366920938463463374607431768211456⟩ := by
  decide +kernel

-- The square-root precision is `32 + 2 * log2 q.den`, and the grid is at least 128 bits.
example : Total.inverseTrigPrecision (1 / 3) = 34 := by decide +kernel

example (q : ℚ) (h : q.den = 3) : Total.inverseTrigPrecision q = 34 := by
  rw [Total.inverseTrigPrecision_def, h]
  decide +kernel

example : Total.inverseTrigRoundingPrecision (1 / 3) = 128 := by decide +kernel

example : Total.inverseTrigRoundingPrecision (1 / 2 ^ 60) = 184 := by decide +kernel

/-! ## Logarithm -/

-- A negative interval gets the bounds of its negation, since `log (-x) = log x`.
example : Total.log? ⟨-3, -1⟩ 20 = logBounds? ⟨1, 3⟩ 20 := by decide +kernel

example : Total.log? ⟨1, 3⟩ 20 = logBounds? ⟨1, 3⟩ 20 := by decide +kernel

example : Total.log? ⟨-3, -1⟩ 20 =
    some ⟨0, 236230641475322983536375114113 / 215026396347908592224121093750⟩ := by
  decide +kernel

-- Mathlib's `log 0 = 0`.
example : Total.log? (point 0) 20 = some (point 0) := by decide +kernel

-- An interval that contains zero and another point gets no enclosure.
example : Total.log? ⟨-1, 1⟩ 20 = none := by decide +kernel

example : Total.log? ⟨0, 1⟩ 20 = none := by decide +kernel

example : Total.log? ⟨-1, 0⟩ 20 = none := by decide +kernel

/-! ## Containment at real arguments -/

example : (Total.sqrt ⟨-1, 4⟩ 12).ContainsReal some (Real.sqrt 3) :=
  Total.containsReal_sqrt _ _ (by norm_num [containsReal_some_iff])

example {x : ℝ} (hx : x ∈ Set.Icc (-3 : ℝ) 3) :
    (Total.asin ⟨-3, 3⟩ 32).ContainsReal some (Real.arcsin x) :=
  Total.containsReal_asin _ _ (by simpa [containsReal_some_iff] using hx)

example {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
    (Total.acos ⟨1 / 2, 2⟩ 32).ContainsReal some (Real.arccos x) :=
  Total.containsReal_acos _ _ (by simpa [containsReal_some_iff] using hx)

example {x : ℝ} (hx : x ∈ Set.Icc (-3 : ℝ) (-1)) :
    (⟨0, 236230641475322983536375114113 / 215026396347908592224121093750⟩ :
      Interval ℚ).ContainsReal some (Real.log x) :=
  Total.containsReal_log? (I := ⟨-3, -1⟩) (terms := 20) (by decide +kernel)
    (by simpa [containsReal_some_iff] using hx)

end FloatLibTests.Numerics.Total
