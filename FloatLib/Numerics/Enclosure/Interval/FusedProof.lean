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

/-- Any outward rounder preserves the exact multiply-add bounds over its ordered field. -/
theorem contains_fma? (R : OutwardRounding α β) {I J K L : Interval α}
    (h : fma? R I J K = some L) {x y z : β}
    (hx : I.Contains R.decode x) (hy : J.Contains R.decode y)
    (hz : K.Contains R.decode z) :
    L.Contains R.decode (x * y + z) := by
  cases ha : I.decode? R.decode with
  | none => simp [fma?, ha] at h
  | some a =>
    cases hb : J.decode? R.decode with
    | none => simp [fma?, ha, hb] at h
    | some b =>
      cases hc : K.decode? R.decode with
      | none => simp [fma?, ha, hb, hc] at h
      | some c =>
        exact contains_encloseInterval? R (by simpa [fma?, ha, hb, hc] using h)
          (fma_bounds a b c ((contains_iff_of_decode? ha x).mp hx)
            ((contains_iff_of_decode? hb y).mp hy) ((contains_iff_of_decode? hc z).mp hz))

/-- Successful multiply-add encloses arbitrary real members of rationally decoded intervals. -/
theorem containsReal_fma? (R : OutwardRounding α ℚ) {I J K L : Interval α}
    (h : fma? R I J K = some L) {x y z : ℝ}
    (hx : I.ContainsReal R.decode x) (hy : J.ContainsReal R.decode y)
    (hz : K.ContainsReal R.decode z) :
    L.ContainsReal R.decode (x * y + z) := by
  cases ha : I.decode? R.decode with
  | none => simp [fma?, ha] at h
  | some a =>
    cases hb : J.decode? R.decode with
    | none => simp [fma?, ha, hb] at h
    | some b =>
      cases hc : K.decode? R.decode with
      | none => simp [fma?, ha, hb, hc] at h
      | some c =>
        apply containsReal_encloseInterval? R (by simpa [fma?, ha, hb, hc] using h)
        have hbounds := fma_bounds (a.map (fun q : ℚ => (q : ℝ)))
          (b.map (fun q : ℚ => (q : ℝ))) (c.map (fun q : ℚ => (q : ℝ)))
          ((containsReal_iff_of_decode? ha x).mp hx)
          ((containsReal_iff_of_decode? hb y).mp hy)
          ((containsReal_iff_of_decode? hc z).mp hz)
        simpa [fmaBounds, map, minOfFour, maxOfFour] using hbounds

namespace BinaryGrid

private theorem scaled_product_add (precision : Nat) (a b c : Int) :
    value precision (a * b + (c <<< precision)) / (scale precision : ℝ) =
      value precision a * value precision b + value precision c := by
  have hs : (scale precision : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (scale_pos precision)
  simp only [value, Int.shiftLeft_eq, ← scale_eq_pow, Int.cast_add, Int.cast_mul]
  field_simp

/-- Integer multiply-add contains the exact real expression before its final outward rounding. -/
theorem containsReal_fma (precision : Nat) {I J K : Interval Int} {x y z : ℝ}
    (hx : I.ContainsReal (decode precision) x) (hy : J.ContainsReal (decode precision) y)
    (hz : K.ContainsReal (decode precision) z) :
    (fma precision I J K).ContainsReal (decode precision) (x * y + z) := by
  rw [containsReal_iff] at hx hy hz ⊢
  have hs : (0 : ℝ) < scale precision := by exact_mod_cast scale_pos precision
  have hlo (a : Int) : value precision (roundDown precision a) ≤
      value precision a / (scale precision : ℝ) :=
    div_le_div_of_nonneg_right (roundDown_le precision a) hs.le
  have hhi (a : Int) : value precision a / (scale precision : ℝ) ≤
      value precision (roundUp precision a) :=
    div_le_div_of_nonneg_right (le_roundUp precision a) hs.le
  have hbounds := fma_bounds (I.map (value precision)) (J.map (value precision))
    (K.map (value precision)) hx hy hz
  refine ⟨(hlo _).trans ?_, (hhi _).trans' ?_⟩
  · simpa only [fmaBounds, map, minOfFour, ← min_add_add_right, value_min,
      ← min_div_div_right hs.le, scaled_product_add] using hbounds.1
  · simpa only [fmaBounds, map, maxOfFour, ← max_add_add_right, value_max,
      ← max_div_div_right hs.le, scaled_product_add] using hbounds.2

end BinaryGrid
end FloatLib.Numerics.Interval
