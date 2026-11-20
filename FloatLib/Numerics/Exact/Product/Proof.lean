/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Product.Runtime
public import FloatLib.Numerics.Enclosure.Comparison.Proof
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Correctness and termination of the product comparison

`ProductComparison.compare` orders `F * C` against a rational boundary. An answer from any
enclosure of `C` is the real order (`compare_eq_real`). When the enclosures converge to a nonzero
`C` and the product differs from the boundary, some enclosure settles the order
(`exists_decide?_isSome`), which is the termination argument the executable search erases.
-/

public section

namespace FloatLib.Numerics.ProductComparison

open Filter
open scoped Topology

variable {compareFactor : ℚ → Ordering} {F C : ℝ}

/-- An order settled by an enclosure of `C` is the real order of `F * C` and the boundary. -/
theorem decide?_eq_some_cmp (hF : 0 < F)
    (hcompare : ∀ q : ℚ, compareFactor q = cmp F (q : ℝ))
    {interval : RationalInterval} (hC : interval.Contains C) {boundary : ℚ} {order : Ordering}
    (h : decide? compareFactor interval boundary = some order) :
    order = cmp (F * C) (boundary : ℝ) := by
  obtain ⟨hlo, hhi⟩ := hC
  unfold decide? at h
  split at h
  · rename_i hpos
    have hloR : (0 : ℝ) < interval.lo := by exact_mod_cast hpos
    have hhiR : (0 : ℝ) < interval.hi := hloR.trans_le (hlo.trans hhi)
    split at h
    · rename_i hb
      cases Option.some.inj h
      have : (boundary : ℝ) ≤ 0 := by exact_mod_cast hb
      exact ((cmp_eq_gt_iff _ _).mpr (this.trans_lt (mul_pos hF (hloR.trans_le hlo)))).symm
    · split at h
      · rename_i hlt
        cases Option.some.inj h
        rw [hcompare, cmp_eq_lt_iff] at hlt
        push_cast at hlt
        rw [lt_div_iff₀ hhiR] at hlt
        exact ((cmp_eq_lt_iff _ _).mpr
          ((mul_le_mul_of_nonneg_left hhi hF.le).trans_lt hlt)).symm
      · split at h
        · rename_i hgt
          cases Option.some.inj h
          rw [hcompare, cmp_eq_gt_iff] at hgt
          push_cast at hgt
          rw [div_lt_iff₀ hloR] at hgt
          exact ((cmp_eq_gt_iff _ _).mpr
            (hgt.trans_le (mul_le_mul_of_nonneg_left hlo hF.le))).symm
        · simp at h
  · split at h
    · rename_i hneg
      have hhiR : (interval.hi : ℝ) < 0 := by exact_mod_cast hneg
      have hloR : (interval.lo : ℝ) < 0 := (hlo.trans hhi).trans_lt hhiR
      split at h
      · rename_i hb
        cases Option.some.inj h
        have : (0 : ℝ) ≤ boundary := by exact_mod_cast hb
        exact ((cmp_eq_lt_iff _ _).mpr
          ((mul_neg_of_pos_of_neg hF (hhi.trans_lt hhiR)).trans_le this)).symm
      · split at h
        · rename_i hlt
          cases Option.some.inj h
          rw [hcompare, cmp_eq_lt_iff] at hlt
          push_cast at hlt
          rw [lt_div_iff_of_neg hloR] at hlt
          exact ((cmp_eq_gt_iff _ _).mpr
            (hlt.trans_le (mul_le_mul_of_nonneg_left hlo hF.le))).symm
        · split at h
          · rename_i hgt
            cases Option.some.inj h
            rw [hcompare, cmp_eq_gt_iff] at hgt
            push_cast at hgt
            rw [div_lt_iff_of_neg hhiR] at hgt
            exact ((cmp_eq_lt_iff _ _).mpr
              ((mul_le_mul_of_nonneg_left hhi hF.le).trans_lt hgt)).symm
          · simp at h
    · simp at h

/-- The product comparison agrees with the real order of `F * C` and the boundary. -/
theorem compare_eq_real (hF : 0 < F) (hcompare : ∀ q : ℚ, compareFactor q = cmp F (q : ℝ))
    (intervals : Nat → RationalInterval) (contains : ∀ n, (intervals n).Contains C)
    (boundary : ℚ)
    (terminates : ∃ n, (decide? compareFactor (intervals n) boundary).isSome) :
    compare compareFactor intervals boundary terminates = cmp (F * C) (boundary : ℝ) :=
  decide?_eq_some_cmp hF hcompare (contains _) (Option.some_get _).symm

/--
Enclosures that converge to a nonzero `C` eventually settle the order of `F * C` and any boundary
different from the product.
-/
theorem exists_decide?_isSome
    (hcompare : ∀ q : ℚ, compareFactor q = cmp F (q : ℝ)) (hC : C ≠ 0)
    {intervals : Nat → RationalInterval} {boundary : ℚ} (hne : F * C ≠ (boundary : ℝ))
    (hlo : Tendsto (fun n => ((intervals n).lo : ℝ)) atTop (𝓝 C))
    (hhi : Tendsto (fun n => ((intervals n).hi : ℝ)) atTop (𝓝 C)) :
    ∃ n, (decide? compareFactor (intervals n) boundary).isSome := by
  have hFlo : Tendsto (fun n => F * ((intervals n).lo : ℝ)) atTop (𝓝 (F * C)) :=
    hlo.const_mul F
  have hFhi : Tendsto (fun n => F * ((intervals n).hi : ℝ)) atTop (𝓝 (F * C)) :=
    hhi.const_mul F
  rcases lt_or_gt_of_ne hC with hneg | hpos
  · -- A negative factor: the enclosures are eventually negative.
    have hevHi := hhi.eventually (eventually_lt_nhds hneg)
    have hevLo := hlo.eventually (eventually_lt_nhds hneg)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨n, hn, hnl, hprod⟩ :=
        (hevHi.and (hevLo.and (hFhi.eventually (eventually_lt_nhds hlt)))).exists
      have hhiQ : (intervals n).hi < 0 := by exact_mod_cast hn
      have hnotpos : ¬0 < (intervals n).lo := by
        have : ((intervals n).lo : ℝ) < 0 := hnl
        exact fun h =>
          absurd (by exact_mod_cast h : (0 : ℝ) < (intervals n).lo) (not_lt.mpr this.le)
      refine ⟨n, ?_⟩
      simp only [decide?, hnotpos, hhiQ, ↓reduceIte]
      split
      · rfl
      · split
        · rfl
        · rename_i hfirst
          have hgtF : compareFactor (boundary / (intervals n).hi) = .gt := by
            rw [hcompare, cmp_eq_gt_iff]
            push_cast
            rw [div_lt_iff_of_neg hn]
            exact hprod
          simp [hgtF]
    · obtain ⟨n, hn, hnl, hprod⟩ :=
        (hevHi.and (hevLo.and (hFlo.eventually (eventually_gt_nhds hgt)))).exists
      have hhiQ : (intervals n).hi < 0 := by exact_mod_cast hn
      have hnotpos : ¬0 < (intervals n).lo := by
        have : ((intervals n).lo : ℝ) < 0 := hnl
        exact fun h =>
          absurd (by exact_mod_cast h : (0 : ℝ) < (intervals n).lo) (not_lt.mpr this.le)
      refine ⟨n, ?_⟩
      simp only [decide?, hnotpos, hhiQ, ↓reduceIte]
      split
      · rfl
      · have hltF : compareFactor (boundary / (intervals n).lo) = .lt := by
          rw [hcompare, cmp_eq_lt_iff]
          push_cast
          rw [lt_div_iff_of_neg hnl]
          exact hprod
        simp [hltF]
  · -- A positive factor: the enclosures are eventually positive.
    have hevLo := hlo.eventually (eventually_gt_nhds hpos)
    have hevHi := hhi.eventually (eventually_gt_nhds hpos)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨n, hn, hnh, hprod⟩ :=
        (hevLo.and (hevHi.and (hFhi.eventually (eventually_lt_nhds hlt)))).exists
      have hloQ : 0 < (intervals n).lo := by exact_mod_cast hn
      refine ⟨n, ?_⟩
      simp only [decide?, hloQ, ↓reduceIte]
      split
      · rfl
      · have hltF : compareFactor (boundary / (intervals n).hi) = .lt := by
          rw [hcompare, cmp_eq_lt_iff]
          push_cast
          rw [lt_div_iff₀ hnh]
          exact hprod
        simp [hltF]
    · obtain ⟨n, hn, _, hprod⟩ :=
        (hevLo.and (hevHi.and (hFlo.eventually (eventually_gt_nhds hgt)))).exists
      have hloQ : 0 < (intervals n).lo := by exact_mod_cast hn
      refine ⟨n, ?_⟩
      simp only [decide?, hloQ, ↓reduceIte]
      split
      · rfl
      · split
        · rfl
        · have hgtF : compareFactor (boundary / (intervals n).lo) = .gt := by
            rw [hcompare, cmp_eq_gt_iff]
            push_cast
            rw [div_lt_iff₀ hn]
            exact hprod
          simp [hgtF]

end FloatLib.Numerics.ProductComparison
