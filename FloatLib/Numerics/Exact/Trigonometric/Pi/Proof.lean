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
  · dsimp only [Enclosure.Comparison.Prepared.compare]
    apply Enclosure.Comparison.compare_eq_real
    intro n
    simpa only [Enclosure.Comparison.cacheIntervals_apply] using
      Enclosure.contains_sinPi (Enclosure.piReduced argument) (2 ^ n)

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
  · dsimp only [Enclosure.Comparison.Prepared.compare]
    apply Enclosure.Comparison.compare_eq_real
    intro n
    simpa only [Enclosure.Comparison.cacheIntervals_apply] using
      Enclosure.contains_cosPi (Enclosure.piReduced argument) (2 ^ n)

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
          Enclosure.exists_sinPiSubCos_separating argument boundary hpole hvalue)
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
    rw [prepareArcsinPi, hvalue, Enclosure.Comparison.Prepared.compare, cmp_div_pi]
    have ha : (argument : ℝ) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by exact_mod_cast hlower, by exact_mod_cast hupper⟩
    split
    · rename_i hb
      have hb' : (boundary : ℝ) < -1 / 2 := by exact_mod_cast hb
      have hgt : (boundary : ℝ) * Real.pi < Real.arcsin (argument : ℝ) := by
        have hmul := mul_lt_mul_of_pos_right hb' Real.pi_pos
        linarith [Real.neg_pi_div_two_le_arcsin (argument : ℝ)]
      exact hgt.cmp_eq_gt.symm
    · rename_i hbzero
      split
      · rename_i hb
        have hb' : (1 / 2 : ℝ) < boundary := by
          simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
            (show ((1 / 2 : ℚ) : ℝ) < (boundary : ℝ) from Rat.cast_lt.mpr hb)
        have hlt : Real.arcsin (argument : ℝ) < (boundary : ℝ) * Real.pi := by
          have hmul := mul_lt_mul_of_pos_right hb' Real.pi_pos
          linarith [Real.arcsin_le_pi_div_two (argument : ℝ)]
        exact hlt.cmp_eq_lt.symm
      · rename_i hbhalf
        have hb : (boundary : ℝ) * Real.pi ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          have hlo : (-1 / 2 : ℝ) ≤ boundary := by exact_mod_cast le_of_not_gt hbzero
          have hhi : (boundary : ℝ) ≤ 1 / 2 := by
            simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
              (show (boundary : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) from
                Rat.cast_le.mpr (le_of_not_gt hbhalf))
          constructor
          · linarith [mul_le_mul_of_nonneg_right hlo Real.pi_pos.le]
          · linarith [mul_le_mul_of_nonneg_right hhi Real.pi_pos.le]
        rw [prepareSinPi_eq_real, cmp_swap]
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
    rw [prepareArccosPi, hvalue, Enclosure.Comparison.Prepared.compare, cmp_div_pi]
    have hlo : (-1 : ℝ) ≤ argument := by exact_mod_cast hlower
    have hhi : (argument : ℝ) ≤ 1 := by exact_mod_cast hupper
    split
    · rename_i hb
      have hb' : (boundary : ℝ) < 0 := by exact_mod_cast hb
      have hgt : (boundary : ℝ) * Real.pi < Real.arccos (argument : ℝ) := by
        have hmul := mul_neg_of_neg_of_pos hb' Real.pi_pos
        linarith [Real.arccos_nonneg (argument : ℝ)]
      exact hgt.cmp_eq_gt.symm
    · rename_i hbzero
      split
      · rename_i hb
        have hb' : (1 : ℝ) < boundary := by exact_mod_cast hb
        have hlt : Real.arccos (argument : ℝ) < (boundary : ℝ) * Real.pi := by
          have hmul := mul_lt_mul_of_pos_right hb' Real.pi_pos
          linarith [Real.arccos_le_pi (argument : ℝ)]
        exact hlt.cmp_eq_lt.symm
      · rename_i hbone
        have hb : (boundary : ℝ) * Real.pi ∈ Set.Icc 0 Real.pi := by
          have hlo : (0 : ℝ) ≤ boundary := by exact_mod_cast le_of_not_gt hbzero
          have hhi : (boundary : ℝ) ≤ 1 := by exact_mod_cast le_of_not_gt hbone
          constructor
          · exact mul_nonneg hlo Real.pi_pos.le
          · simpa using mul_le_mul_of_nonneg_right hhi Real.pi_pos.le
        have ha : Real.arccos (argument : ℝ) ∈ Set.Icc 0 Real.pi :=
          ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
        have hlt : Real.cos ((boundary : ℝ) * Real.pi) < argument ↔
            Real.arccos (argument : ℝ) < (boundary : ℝ) * Real.pi := by
          simpa only [Real.cos_arccos hlo hhi] using Real.strictAntiOn_cos.lt_iff_gt hb ha
        have hgt : (argument : ℝ) < Real.cos ((boundary : ℝ) * Real.pi) ↔
            (boundary : ℝ) * Real.pi < Real.arccos (argument : ℝ) := by
          simpa only [Real.cos_arccos hlo hhi] using Real.strictAntiOn_cos.lt_iff_gt ha hb
        rw [prepareCosPi_eq_real]
        simp only [cmp, cmpUsing, hlt, hgt]

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
    rw [prepareArctanPi, hvalue, Enclosure.Comparison.Prepared.compare, cmp_div_pi]
    split
    · rename_i hb
      have hb' : (boundary : ℝ) ≤ -1 / 2 := by exact_mod_cast hb
      have hgt : (boundary : ℝ) * Real.pi < Real.arctan (argument : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right hb' Real.pi_pos.le
        linarith [Real.neg_pi_div_two_lt_arctan (argument : ℝ)]
      exact hgt.cmp_eq_gt.symm
    · rename_i hbzero
      split
      · rename_i hb
        have hb' : (1 / 2 : ℝ) ≤ boundary := by
          simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
            (show ((1 / 2 : ℚ) : ℝ) ≤ (boundary : ℝ) from Rat.cast_le.mpr hb)
        have hlt : Real.arctan (argument : ℝ) < (boundary : ℝ) * Real.pi := by
          have hmul := mul_le_mul_of_nonneg_right hb' Real.pi_pos.le
          linarith [Real.arctan_lt_pi_div_two (argument : ℝ)]
        exact hlt.cmp_eq_lt.symm
      · rename_i hbhalf
        have hb : (boundary : ℝ) * Real.pi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
          have hlo : (-1 / 2 : ℝ) < boundary := by exact_mod_cast lt_of_not_ge hbzero
          have hhi : (boundary : ℝ) < 1 / 2 := by
            simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
              (show (boundary : ℝ) < ((1 / 2 : ℚ) : ℝ) from
                Rat.cast_lt.mpr (lt_of_not_ge hbhalf))
          constructor
          · linarith [mul_lt_mul_of_pos_right hlo Real.pi_pos]
          · linarith [mul_lt_mul_of_pos_right hhi Real.pi_pos]
        have ha := Real.arctan_mem_Ioo (argument : ℝ)
        have hlt : (argument : ℝ) < Real.tan ((boundary : ℝ) * Real.pi) ↔
            Real.arctan (argument : ℝ) < (boundary : ℝ) * Real.pi := by
          simpa only [Real.tan_arctan] using Real.strictMonoOn_tan.lt_iff_lt ha hb
        have hgt : Real.tan ((boundary : ℝ) * Real.pi) < (argument : ℝ) ↔
            (boundary : ℝ) * Real.pi < Real.arctan (argument : ℝ) := by
          simpa only [Real.tan_arctan] using Real.strictMonoOn_tan.lt_iff_lt hb ha
        rw [prepareTanPi_eq_real, cmp_swap]
        simp only [cmp, cmpUsing, hlt, hgt]

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
