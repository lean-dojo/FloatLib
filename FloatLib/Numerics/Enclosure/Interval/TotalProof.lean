/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.InverseTrigProof
public import FloatLib.Numerics.Enclosure.Interval.RoundingProof
public import FloatLib.Numerics.Enclosure.Interval.Total

import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Real containment for the total enclosures

Every enclosure of `Total` contains Mathlib's total function at every real member of its input
interval, irrational members included.

The square root at a point comes from `containsReal_sqrtPointBounds` and
`√(q * q.den ^ 2) = √q * q.den`. It's exact at rational squares (`sqrtPoint_sq`), and the
division by `q.den` turns the width `2 ^ (-steps)` of `sqrtPointBounds` into
`1 / (q.den * 2 ^ steps)` (`sqrtPoint_width_le`). Arcsine and arccosine read the clamped argument
through `Real.arcsin_projIcc`, round with `containsReal_dyadicHull`, and bound their fallbacks by
Mathlib's `Real.pi_lt_d20`. The logarithm of a negative interval is that of its negation, by
`Real.log_neg_eq_log`. On an interval, `containsReal_monotoneBounds` and
`containsReal_antitoneBounds` do the rest.
-/

public section

namespace FloatLib.Numerics.Interval.Total

/-! ### Square root -/

/-- `sqrtPoint q steps` contains `Real.sqrt q` for every rational `q`. -/
theorem containsReal_sqrtPoint (q : ℚ) (steps : Nat) :
    (sqrtPoint q steps).ContainsReal some (Real.sqrt q) := by
  rw [sqrtPoint_def, containsReal_some_iff]
  split_ifs with hq
  · have h := (containsReal_some_iff _ _).1
      (containsReal_sqrtPointBounds (q * (q.den : ℚ) ^ 2) steps (mul_nonneg hq (sq_nonneg _)))
    have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    rw [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
      Real.sqrt_mul (by exact_mod_cast hq), Real.sqrt_sq hd.le] at h
    push_cast
    exact ⟨(div_le_iff₀ hd).2 h.1, (le_div_iff₀ hd).2 h.2⟩
  · rw [Real.sqrt_eq_zero_of_nonpos (by exact_mod_cast (not_le.1 hq).le)]
    simp [point]

/-- The enclosure of `Real.sqrt q` is at most `1 / (q.den * 2 ^ steps)` wide. -/
theorem sqrtPoint_width_le (q : ℚ) (steps : Nat) :
    (sqrtPoint q steps).hi - (sqrtPoint q steps).lo ≤ 1 / ((q.den : ℚ) * 2 ^ steps) := by
  rw [sqrtPoint_def]
  split_ifs
  · rw [← sub_div, mul_comm (q.den : ℚ), ← div_div]
    exact div_le_div_of_nonneg_right (sqrtPointBounds_width_le _ steps) (Nat.cast_nonneg _)
  · simp only [point, sub_self]
    positivity

/-- The integer square-root bounds of the square of a natural number are that number. -/
private theorem sqrtPointBounds_natCast_sq (n precision : Nat) :
    sqrtPointBounds ((n : ℚ) ^ 2) precision = point (n : ℚ) := by
  have hscaled : (n : ℚ) ^ 2 * ((2 : ℚ) ^ precision) ^ 2 = ((n * 2 ^ precision) ^ 2 : ℕ) := by
    push_cast
    ring
  have hroot : ((n * 2 ^ precision : ℕ) : ℚ) / 2 ^ precision = n := by
    push_cast
    field_simp
  rw [sqrtPointBounds_def]
  simp only [hscaled, Nat.floor_natCast, Nat.sqrt_eq', hroot, ↓reduceIte, point]

/-- A rational square gives its exact root: `sqrtPoint (r ^ 2) steps = [r, r]` for `0 ≤ r`. -/
theorem sqrtPoint_sq {r : ℚ} (hr : 0 ≤ r) (steps : Nat) :
    sqrtPoint (r ^ 2) steps = point r := by
  have hnum : ((r.num.natAbs : ℕ) : ℚ) = r.num := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast Rat.num_nonneg.2 hr)]
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  have hscaled : r ^ 2 * (((r ^ 2).den : ℕ) : ℚ) ^ 2 = ((r.num.natAbs * r.den : ℕ) : ℚ) ^ 2 := by
    rw [Rat.den_pow, Nat.cast_mul, hnum, Nat.cast_pow, ← Rat.mul_den_eq_num]
    ring
  have hroot : ((r.num.natAbs * r.den : ℕ) : ℚ) / (((r ^ 2).den : ℕ) : ℚ) = r := by
    rw [Rat.den_pow, Nat.cast_mul, hnum, Nat.cast_pow, ← Rat.mul_den_eq_num]
    field_simp
  rw [sqrtPoint_def, ite_eq_left (sq_nonneg r)]
  simp only [hscaled, sqrtPointBounds_natCast_sq, point, hroot]

/-- `Total.sqrt I steps` contains `Real.sqrt x` for every real member `x` of `I`. -/
theorem containsReal_sqrt (I : Interval ℚ) (steps : Nat) {x : ℝ} (hx : I.ContainsReal some x) :
    (sqrt I steps).ContainsReal some (Real.sqrt x) :=
  containsReal_monotoneBounds _ Real.sqrt I (fun _ _ _ _ h => Real.sqrt_le_sqrt h)
    (fun q _ => containsReal_sqrtPoint q steps) hx

/-! ### Arcsine and arccosine -/

/-- Mathlib's arcsine takes the same value at the clamped argument. -/
theorem arcsin_clampUnit (q : ℚ) : Real.arcsin (clampUnit q) = Real.arcsin q := by
  rw [clampUnit_def]
  push_cast
  simpa [Set.coe_projIcc] using Real.arcsin_projIcc (q : ℝ)

/-- Mathlib's arccosine takes the same value at the clamped argument. -/
theorem arccos_clampUnit (q : ℚ) : Real.arccos (clampUnit q) = Real.arccos q := by
  simp only [Real.arccos_eq_pi_div_two_sub_arcsin, arcsin_clampUnit]

/--
`inverseTrigPoint bounds fallback q terms` contains `f q` when `bounds` encloses `f` at the
degree `terms` and the precision `inverseTrigPrecision q`, `f` takes the same value at
`clampUnit q`, and `fallback` contains `f q`.
-/
theorem containsReal_inverseTrigPoint {f : ℝ → ℝ}
    {bounds : Interval ℚ → Nat → Nat → Option (Interval ℚ)} {fallback : Interval ℚ} {q : ℚ}
    {terms : Nat}
    (hbounds : ∀ {I K : Interval ℚ}, bounds I terms (inverseTrigPrecision q) = some K →
      ∀ {x : ℝ}, I.ContainsReal some x → K.ContainsReal some (f x))
    (hclamp : f (clampUnit q) = f q) (hfallback : fallback.ContainsReal some (f q)) :
    (inverseTrigPoint bounds fallback q terms).ContainsReal some (f q) := by
  unfold inverseTrigPoint
  split
  · next J hJ =>
    have hJ' := hbounds hJ (containsReal_point (clampUnit q))
    rw [hclamp] at hJ'
    exact containsReal_dyadicHull _ hJ'
  · exact hfallback

/-- `asinPoint q terms` contains `Real.arcsin q` for every rational `q`. -/
theorem containsReal_asinPoint (q : ℚ) (terms : Nat) :
    (asinPoint q terms).ContainsReal some (Real.arcsin q) := by
  refine containsReal_inverseTrigPoint containsReal_asinBounds? (arcsin_clampUnit q) ?_
  rw [containsReal_some_iff]
  push_cast
  constructor <;> linarith [Real.pi_lt_d20, Real.neg_pi_div_two_le_arcsin (q : ℝ),
    Real.arcsin_le_pi_div_two (q : ℝ)]

/-- `acosPoint q terms` contains `Real.arccos q` for every rational `q`. -/
theorem containsReal_acosPoint (q : ℚ) (terms : Nat) :
    (acosPoint q terms).ContainsReal some (Real.arccos q) := by
  refine containsReal_inverseTrigPoint containsReal_acosBounds? (arccos_clampUnit q) ?_
  rw [containsReal_some_iff]
  push_cast
  exact ⟨Real.arccos_nonneg _, (Real.arccos_le_pi _).trans Real.pi_lt_d20.le⟩

/-- `Total.asin I terms` contains `Real.arcsin x` for every real member `x` of `I`. -/
theorem containsReal_asin (I : Interval ℚ) (terms : Nat) {x : ℝ} (hx : I.ContainsReal some x) :
    (asin I terms).ContainsReal some (Real.arcsin x) :=
  containsReal_monotoneBounds _ Real.arcsin I (fun _ _ _ _ h => Real.arcsin_le_arcsin h)
    (fun q _ => containsReal_asinPoint q terms) hx

/-- `Total.acos I terms` contains `Real.arccos x` for every real member `x` of `I`. -/
theorem containsReal_acos (I : Interval ℚ) (terms : Nat) {x : ℝ} (hx : I.ContainsReal some x) :
    (acos I terms).ContainsReal some (Real.arccos x) :=
  containsReal_antitoneBounds _ Real.arccos I (fun _ _ _ _ h => Real.arccos_le_arccos h)
    (fun q _ => containsReal_acosPoint q terms) hx

/-! ### Logarithm -/

/--
A successful `Total.log? I terms` contains `Real.log x` for every real member `x` of `I`,
`Real.log 0 = 0` included.
-/
theorem containsReal_log? {I K : Interval ℚ} {terms : Nat} (h : log? I terms = some K) {x : ℝ}
    (hx : I.ContainsReal some x) : K.ContainsReal some (Real.log x) := by
  obtain ⟨hlo, hhi⟩ := (containsReal_some_iff I x).1 hx
  rw [log?_def] at h
  split_ifs at h with _ _ hzero
  · exact containsReal_logBounds? h hx
  · rw [← Real.log_neg_eq_log]
    refine containsReal_logBounds? h ((containsReal_some_iff _ _).2 ?_)
    push_cast
    exact ⟨neg_le_neg hhi, neg_le_neg hlo⟩
  · cases h
    have hx0 : x = 0 := le_antisymm (by simpa [hzero.2] using hhi) (by simpa [hzero.1] using hlo)
    simp [hx0, point]

end FloatLib.Numerics.Interval.Total
