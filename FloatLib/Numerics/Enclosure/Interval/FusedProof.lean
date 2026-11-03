/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Fused
public import FloatLib.Numerics.Enclosure.Interval.BinaryGridProof

/-!
# Containment for interval multiply-add

Four-corner product bounds followed by the addend bounds enclose every real combination
of the inputs. Rounding takes place after this exact calculation.
-/

public section

namespace FloatLib.Numerics.Interval

variable {α β : Type*} [Field β] [LinearOrder β] [IsStrictOrderedRing β]

/-- Exact multiply-add bounds contain every combination of members of the three intervals. -/
theorem fma_bounds (I J K : Interval β) {x y z : β}
    (hx : I.lo ≤ x ∧ x ≤ I.hi) (hy : J.lo ≤ y ∧ y ≤ J.hi)
    (hz : K.lo ≤ z ∧ z ≤ K.hi) :
    (fmaBounds I J K).lo ≤ x * y + z ∧ x * y + z ≤ (fmaBounds I J K).hi := by
  have hxy := mul_bounds_Icc I.lo I.hi J.lo J.hi x y hx hy
  exact ⟨add_le_add hxy.1 hz.1, add_le_add hxy.2 hz.2⟩

omit [IsStrictOrderedRing β] in
/-- Multiply-add succeeds exactly when all three inputs decode and the exact bounds round outward. -/
theorem fma?_eq_some_iff (R : OutwardRounding α β) {I J K L : Interval α} :
    fma? R I J K = some L ↔
      ∃ a b c, I.decode? R.decode = some a ∧ J.decode? R.decode = some b ∧
        K.decode? R.decode = some c ∧ encloseInterval? R (fmaBounds a b c) = some L := by
  unfold fma?
  cases I.decode? R.decode <;> cases J.decode? R.decode <;> cases K.decode? R.decode <;> simp

/-- Any outward rounder preserves the exact multiply-add bounds over its ordered field. -/
theorem contains_fma? (R : OutwardRounding α β) {I J K L : Interval α}
    (h : fma? R I J K = some L) {x y z : β}
    (hx : I.Contains R.decode x) (hy : J.Contains R.decode y)
    (hz : K.Contains R.decode z) :
    L.Contains R.decode (x * y + z) := by
  obtain ⟨a, b, c, ha, hb, hc, hL⟩ := (fma?_eq_some_iff R).1 h
  exact contains_encloseInterval? R hL
    (fma_bounds a b c ((contains_iff_of_decode? ha x).mp hx)
      ((contains_iff_of_decode? hb y).mp hy) ((contains_iff_of_decode? hc z).mp hz))

/-- Successful multiply-add encloses arbitrary real members of rationally decoded intervals. -/
theorem containsReal_fma? (R : OutwardRounding α ℚ) {I J K L : Interval α}
    (h : fma? R I J K = some L) {x y z : ℝ}
    (hx : I.ContainsReal R.decode x) (hy : J.ContainsReal R.decode y)
    (hz : K.ContainsReal R.decode z) :
    L.ContainsReal R.decode (x * y + z) := by
  obtain ⟨a, b, c, ha, hb, hc, hL⟩ := (fma?_eq_some_iff R).1 h
  apply containsReal_encloseInterval? R hL
  have hbounds := fma_bounds (a.map (fun q : ℚ => (q : ℝ)))
    (b.map (fun q : ℚ => (q : ℝ))) (c.map (fun q : ℚ => (q : ℝ)))
    ((containsReal_iff_of_decode? ha x).mp hx)
    ((containsReal_iff_of_decode? hb y).mp hy)
    ((containsReal_iff_of_decode? hc z).mp hz)
  simpa [fmaBounds, map, minOfFour, maxOfFour] using hbounds

namespace BinaryGrid

/--
The outward-rounded integer multiply-add interval encloses `x * y + z` for arbitrary real members
of the three decoded input intervals. The corner products and the aligned addend are exact on the
grid with twice the fractional bits; only the two final endpoints are rounded outward.
-/
theorem containsReal_fma (precision : Nat) {I J K : Interval Int} {x y z : ℝ}
    (hx : I.ContainsReal (decode precision) x) (hy : J.ContainsReal (decode precision) y)
    (hz : K.ContainsReal (decode precision) z) :
    (fma precision I J K).ContainsReal (decode precision) (x * y + z) := by
  rw [containsReal_iff] at hx hy hz
  refine containsReal_coarsen (I := ⟨_, _⟩) (shift := precision) ?_
  rw [containsReal_iff]
  simpa only [fmaBounds, map, minOfFour, maxOfFour, value_add, value_min, value_max, value_mul,
    value_shiftLeft] using
    fma_bounds (I.map (value precision)) (J.map (value precision)) (K.map (value precision))
      hx hy hz

end BinaryGrid
end FloatLib.Numerics.Interval
