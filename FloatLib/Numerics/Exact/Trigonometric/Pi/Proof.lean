/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Trigonometric.Pi.Runtime
import FloatLib.Numerics.Order.Comparison

/-!
# Real semantics of pi-scaled comparisons

The exact-value branches and every adaptive branch return the ordering of the corresponding
real function and rational boundary. Inverse sine and cosine use their principal branches on
`[-1, 1]`. Tangent agrees with the totalized real function, including zero at half-integer poles;
format wrappers must reject poles when required by their exceptional-value contract.
-/

public section

namespace FloatLib.Numerics.TrigonometricComparison

private theorem cmp_ratCast (a b : ℚ) : cmp a b = cmp (a : ℝ) (b : ℝ) :=
  ((Rat.cast_strictMono (K := ℝ)).cmp_map_eq a b).symm

/-- Prepared pi-scaled sine comparisons agree with the exact real ordering at every cache size. -/
theorem prepareSinPi_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ) :
    (prepareSinPi argument levels).compare boundary =
      cmp (Real.sin ((argument : ℝ) * Real.pi)) (boundary : ℝ) := by
  rw [← Enclosure.sin_piReduced argument]
  unfold prepareSinPi
  dsimp only
  split
  · rename_i value hvalue
    rw [Enclosure.Comparison.Prepared.compare,
      sinPiExact_eq_real (Enclosure.piReduced argument) value hvalue]
    exact cmp_ratCast value boundary
  · exact Enclosure.Comparison.Prepared.compare_enclosed_cacheIntervals _ _ _ _ _
      fun n => Enclosure.contains_sinPi (Enclosure.piReduced argument) (2 ^ n)

/-- Prepared pi-scaled cosine comparisons include all classified rational special values. -/
theorem prepareCosPi_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ) :
    (prepareCosPi argument levels).compare boundary =
      cmp (Real.cos ((argument : ℝ) * Real.pi)) (boundary : ℝ) := by
  rw [← Enclosure.cos_piReduced argument]
  unfold prepareCosPi
  dsimp only
  split
  · rename_i value hvalue
    rw [Enclosure.Comparison.Prepared.compare,
      cosPiExact_eq_real (Enclosure.piReduced argument) value hvalue]
    exact cmp_ratCast value boundary
  · exact Enclosure.Comparison.Prepared.compare_enclosed_cacheIntervals _ _ _ _ _
      fun n => Enclosure.contains_cosPi (Enclosure.piReduced argument) (2 ^ n)

/-- The tangent helper agrees with the totalized real tangent, including its pole convention. -/
theorem prepareTanPi_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ) :
    (prepareTanPi argument levels).compare boundary =
      cmp (Real.tan ((argument : ℝ) * Real.pi)) (boundary : ℝ) := by
  unfold prepareTanPi
  split
  · rename_i hpole
    rw [Enclosure.Comparison.Prepared.compare, Real.tan_eq_sin_div_cos,
      cosPi_eq_zero_of_fract_half argument hpole, div_zero]
    simpa using cmp_ratCast 0 boundary
  · rename_i hpole
    split
    · rename_i value hvalue
      rw [Enclosure.Comparison.Prepared.compare, tanPiExact_eq_real argument value hvalue]
      exact cmp_ratCast value boundary
    · rename_i hvalue
      rw [Enclosure.Comparison.Prepared.compare]
      have hr := Enclosure.Comparison.compare_eq_real
        (fun n => ((Enclosure.Comparison.cacheIntervals
          (fun i => Enclosure.sinPi argument (2 ^ i)) levels).get n).sub
            (((Enclosure.Comparison.cacheIntervals
              (fun i => Enclosure.cosPi argument (2 ^ i)) levels).get n).scale boundary)) 0
        (by simpa only [Enclosure.Comparison.cacheIntervals_apply, Enclosure.sinPiSubCos] using
          Enclosure.exists_sinPiSubCos_separating argument boundary hvalue)
        (Real.sin ((argument : ℝ) * Real.pi) -
          (boundary : ℝ) * Real.cos ((argument : ℝ) * Real.pi))
        (fun n => by simpa only [Enclosure.Comparison.cacheIntervals_apply,
          Enclosure.sinPiSubCos] using Enclosure.contains_sinPiSubCos argument boundary (2 ^ n))
      rw [prepareCosPi_eq_real, hr, Rat.cast_zero]
      simp only [cmp_eq_gt_iff, Real.tan_eq_sin_div_cos]
      split
      · exact cmp_div_of_pos _ _ _ ‹_›
      · have hc : Real.cos ((argument : ℝ) * Real.pi) < 0 :=
          lt_of_le_of_ne (le_of_not_gt ‹_›) ((cosPi_eq_zero_iff argument).not.mpr hpole)
        exact cmp_div_of_neg _ _ _ hc

private theorem cmp_div_pi (a b : ℝ) : cmp (a / Real.pi) b = cmp a (b * Real.pi) := by
  simp only [cmp, cmpUsing, div_lt_iff₀ Real.pi_pos, lt_div_iff₀ Real.pi_pos]

private theorem half_ratCast : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num

/-- Inverse sine divided by pi lies in `[-1/2, 1/2]`. -/
private theorem arcsin_div_pi_mem (x : ℝ) :
    Real.arcsin x / Real.pi ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
  constructor
  · rw [le_div_iff₀ Real.pi_pos]
    linarith [Real.neg_pi_div_two_le_arcsin x]
  · rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.arcsin_le_pi_div_two x]

/-- Inverse cosine divided by pi lies in `[0, 1]`. -/
private theorem arccos_div_pi_mem (x : ℝ) : Real.arccos x / Real.pi ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (Real.arccos_nonneg x) Real.pi_pos.le,
    (div_le_one Real.pi_pos).2 (Real.arccos_le_pi x)⟩

/-- Inverse tangent divided by pi lies in `(-1/2, 1/2)`. -/
private theorem arctan_div_pi_mem (x : ℝ) :
    Real.arctan x / Real.pi ∈ Set.Ioo (-1 / 2 : ℝ) (1 / 2) := by
  constructor
  · rw [lt_div_iff₀ Real.pi_pos]
    linarith [Real.neg_pi_div_two_lt_arctan x]
  · rw [div_lt_iff₀ Real.pi_pos]
    linarith [Real.arctan_lt_pi_div_two x]

/-- Scaling by pi maps `[-1/2, 1/2]` into the principal branch `[-π/2, π/2]` of sine. -/
private theorem mul_pi_mem_Icc {b : ℝ} (hb : b ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :
    b * Real.pi ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
  ⟨by nlinarith [Real.pi_pos, hb.1], by nlinarith [Real.pi_pos, hb.2]⟩

/-- Scaling by pi maps `(-1/2, 1/2)` into the principal branch `(-π/2, π/2)` of tangent. -/
private theorem mul_pi_mem_Ioo {b : ℝ} (hb : b ∈ Set.Ioo (-1 / 2 : ℝ) (1 / 2)) :
    b * Real.pi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
  ⟨by nlinarith [Real.pi_pos, hb.1], by nlinarith [Real.pi_pos, hb.2]⟩

/-- Inverse sine divided by pi has the exact principal-branch ordering throughout `[-1, 1]`. -/
theorem prepareArcsinPi_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ)
    (hlower : -1 ≤ argument) (hupper : argument ≤ 1) :
    (prepareArcsinPi argument levels).compare boundary =
      cmp (Real.arcsin (argument : ℝ) / Real.pi) (boundary : ℝ) := by
  cases hvalue : arcsinPiExact argument with
  | some value =>
    rw [prepareArcsinPi, hvalue, Enclosure.Comparison.Prepared.compare,
      arcsinPiExact_eq_real argument value hvalue]
    exact cmp_ratCast value boundary
  | none =>
    rw [prepareArcsinPi, hvalue, Enclosure.Comparison.Prepared.compare]
    have hrange := arcsin_div_pi_mem (argument : ℝ)
    split
    · rename_i hb
      have hb' : (boundary : ℝ) < -1 / 2 := by exact_mod_cast hb
      exact (hb'.trans_le hrange.1).cmp_eq_gt.symm
    · rename_i hbzero
      split
      · rename_i hb
        have hb' : (1 / 2 : ℝ) < boundary := by
          simpa only [half_ratCast] using (Rat.cast_lt (K := ℝ)).2 hb
        exact (hrange.2.trans_lt hb').cmp_eq_lt.symm
      · rename_i hbhalf
        have ha : (argument : ℝ) ∈ Set.Icc (-1 : ℝ) 1 :=
          ⟨by exact_mod_cast hlower, by exact_mod_cast hupper⟩
        have hb := mul_pi_mem_Icc (b := (boundary : ℝ)) ⟨by exact_mod_cast le_of_not_gt hbzero,
          by simpa only [half_ratCast] using (Rat.cast_le (K := ℝ)).2 (le_of_not_gt hbhalf)⟩
        rw [cmp_div_pi, prepareSinPi_eq_real, cmp_swap]
        simp only [cmp, cmpUsing, Real.arcsin_lt_iff_lt_sin ha hb,
          Real.lt_arcsin_iff_sin_lt hb ha]

/-- Inverse cosine divided by pi uses the decreasing principal branch, including both endpoints. -/
theorem prepareArccosPi_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ)
    (hlower : -1 ≤ argument) (hupper : argument ≤ 1) :
    (prepareArccosPi argument levels).compare boundary =
      cmp (Real.arccos (argument : ℝ) / Real.pi) (boundary : ℝ) := by
  cases hvalue : arccosPiExact argument with
  | some value =>
    rw [prepareArccosPi, hvalue, Enclosure.Comparison.Prepared.compare,
      arccosPiExact_eq_real argument value hvalue]
    exact cmp_ratCast value boundary
  | none =>
    rw [prepareArccosPi, hvalue, Enclosure.Comparison.Prepared.compare]
    have hrange := arccos_div_pi_mem (argument : ℝ)
    split
    · rename_i hb
      have hb' : (boundary : ℝ) < 0 := by exact_mod_cast hb
      exact (hb'.trans_le hrange.1).cmp_eq_gt.symm
    · rename_i hbzero
      split
      · rename_i hb
        have hb' : (1 : ℝ) < boundary := by exact_mod_cast hb
        exact (hrange.2.trans_lt hb').cmp_eq_lt.symm
      · rename_i hbone
        have hlo : (-1 : ℝ) ≤ argument := by exact_mod_cast hlower
        have hhi : (argument : ℝ) ≤ 1 := by exact_mod_cast hupper
        have hb : (boundary : ℝ) * Real.pi ∈ Set.Icc 0 Real.pi := by
          have hlo : (0 : ℝ) ≤ boundary := by exact_mod_cast le_of_not_gt hbzero
          have hhi : (boundary : ℝ) ≤ 1 := by exact_mod_cast le_of_not_gt hbone
          constructor
          · exact mul_nonneg hlo Real.pi_pos.le
          · simpa using mul_le_mul_of_nonneg_right hhi Real.pi_pos.le
        have ha : Real.arccos (argument : ℝ) ∈ Set.Icc 0 Real.pi :=
          ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
        rw [cmp_div_pi, prepareCosPi_eq_real, ← Real.strictAntiOn_cos.cmp_map_eq hb ha,
          Real.cos_arccos hlo hhi]

/-- Inverse tangent divided by pi uses the increasing open principal branch. -/
theorem prepareArctanPi_eq_real (argument : ℚ) (levels : Nat) (boundary : ℚ) :
    (prepareArctanPi argument levels).compare boundary =
      cmp (Real.arctan (argument : ℝ) / Real.pi) (boundary : ℝ) := by
  cases hvalue : arctanPiExact argument with
  | some value =>
    rw [prepareArctanPi, hvalue, Enclosure.Comparison.Prepared.compare,
      arctanPiExact_eq_real argument value hvalue]
    exact cmp_ratCast value boundary
  | none =>
    rw [prepareArctanPi, hvalue, Enclosure.Comparison.Prepared.compare]
    have hrange := arctan_div_pi_mem (argument : ℝ)
    split
    · rename_i hb
      have hb' : (boundary : ℝ) ≤ -1 / 2 := by exact_mod_cast hb
      exact (hb'.trans_lt hrange.1).cmp_eq_gt.symm
    · rename_i hbzero
      split
      · rename_i hb
        have hb' : (1 / 2 : ℝ) ≤ boundary := by
          simpa only [half_ratCast] using (Rat.cast_le (K := ℝ)).2 hb
        exact (hrange.2.trans_le hb').cmp_eq_lt.symm
      · rename_i hbhalf
        have hb := mul_pi_mem_Ioo (b := (boundary : ℝ)) ⟨by exact_mod_cast lt_of_not_ge hbzero,
          by simpa only [half_ratCast] using (Rat.cast_lt (K := ℝ)).2 (lt_of_not_ge hbhalf)⟩
        rw [cmp_div_pi, prepareTanPi_eq_real, cmp_swap,
          ← Real.strictMonoOn_tan.cmp_map_eq (Real.arctan_mem_Ioo (argument : ℝ)) hb,
          Real.tan_arctan]

/-- Exact real semantics of pi-scaled sine comparison. -/
theorem compareSinPi_eq_real (argument boundary : ℚ) :
    compareSinPi argument boundary = cmp (Real.sin ((argument : ℝ) * Real.pi)) (boundary : ℝ) :=
  prepareSinPi_eq_real argument 0 boundary

/-- Exact real semantics of pi-scaled cosine comparison. -/
theorem compareCosPi_eq_real (argument boundary : ℚ) :
    compareCosPi argument boundary = cmp (Real.cos ((argument : ℝ) * Real.pi)) (boundary : ℝ) :=
  prepareCosPi_eq_real argument 0 boundary

/-- Exact real semantics of the totalized pi-scaled tangent comparison. -/
theorem compareTanPi_eq_real (argument boundary : ℚ) :
    compareTanPi argument boundary = cmp (Real.tan ((argument : ℝ) * Real.pi)) (boundary : ℝ) :=
  prepareTanPi_eq_real argument 0 boundary

/-- Exact inverse sine semantics on its closed real domain. -/
theorem compareArcsinPi_eq_real (argument boundary : ℚ) (hlower : -1 ≤ argument)
    (hupper : argument ≤ 1) :
    compareArcsinPi argument boundary = cmp (Real.arcsin (argument : ℝ) / Real.pi) (boundary : ℝ) :=
  prepareArcsinPi_eq_real argument 0 boundary hlower hupper

/-- Exact inverse cosine semantics on its closed real domain. -/
theorem compareArccosPi_eq_real (argument boundary : ℚ) (hlower : -1 ≤ argument)
    (hupper : argument ≤ 1) :
    compareArccosPi argument boundary = cmp (Real.arccos (argument : ℝ) / Real.pi) (boundary : ℝ) :=
  prepareArccosPi_eq_real argument 0 boundary hlower hupper

/-- Exact inverse tangent semantics at every rational input. -/
theorem compareArctanPi_eq_real (argument boundary : ℚ) :
    compareArctanPi argument boundary = cmp (Real.arctan (argument : ℝ) / Real.pi) (boundary : ℝ) :=
  prepareArctanPi_eq_real argument 0 boundary

end FloatLib.Numerics.TrigonometricComparison
