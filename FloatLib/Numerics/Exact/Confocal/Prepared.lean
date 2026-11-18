/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Confocal.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Proof
public import FloatLib.Numerics.Enclosure.Comparison.Cache

/-!
# Total comparators for the inverse functions of the confocal coordinates

For rational `p` and `q`, with `major p q` and `minor p q` the half sum and the half difference of
the distances of `(p, q)` to the foci `(0, -1)` and `(0, 1)`:

* `compareArcosh` orders `arcosh (major p q)` against any rational (`compareArcosh_eq_real`);
* `compareArcsin` orders `arcsin (minor p q)` against any rational (`compareArcsin_eq_real`);
* `compareArccos` orders `arccos (minor p q)` against any rational (`compareArccos_eq_real`).

Each comparison with a boundary `t` decides the sign of `major p q - cosh t`, `minor p q - sin t`
or `minor p q - cos t` from convergent enclosures. The sign is never zero at `t ≠ 0`, because the
coordinates are algebraic. The boundary zero and the boundaries outside the range of the inverse
function are decided first, so no comparison evaluates a hyperbolic cosine beyond
`guard p q`.
-/

@[expose] public section

namespace FloatLib.Numerics.ConfocalComparison

open RationalInterval ProductComparison Enclosure.Comparison

/--
Compare `arcosh (major p q)` with a rational boundary. The first `levels` enclosures of the half
sum of the distances are shared across boundaries.
-/
def compareArcosh (p q : ℚ) (levels : Nat) : ℚ → Ordering :=
  let ladder := cacheIntervals (majorLadder p q) levels
  let bound : ℚ := guard p q
  fun boundary =>
    if hpositive : boundary ≤ 0 then
      if boundary = 0 ∧ p = 0 ∧ |q| ≤ 1 then .eq else .gt
    else if bound ≤ boundary then .lt
    else
      compare (fun n => (ladder.get n).sub (coshLadder boundary n)) 0 (by
        simpa only [ladder, cacheIntervals_apply] using
          ((converges_majorLadder p q).sub (converges_coshLadder boundary)).exists_separates
            (by simpa using major_sub_cosh_ne_zero p q (ne_of_gt (not_le.mp hpositive))))

/--
Compare `arcsin (minor p q)` with a rational boundary. The comparison with zero is the sign of
`q`.
-/
def compareArcsin (p q : ℚ) (levels : Nat) : ℚ → Ordering :=
  let ladder := cacheIntervals (minorLadder p q) levels
  let quarter := TrigonometricComparison.prepareArctan 1 levels
  fun boundary =>
    if hzero : boundary = 0 then cmp q 0
    else if quarter.compare (boundary / 2) = .lt then .lt
    else if quarter.compare (-boundary / 2) = .lt then .gt
    else
      compare (fun n => (ladder.get n).sub (Trig.sin.intervals boundary n)) 0 (by
        simpa only [ladder, cacheIntervals_apply] using
          ((converges_minorLadder p q).sub
            (Trig.converges_intervals .sin boundary)).exists_separates
            (by simpa [Trig.eval] using minor_sub_sin_ne_zero p q hzero))

/--
Compare `arccos (minor p q)` with a rational boundary. The inverse cosine is zero exactly on the
ray above the upper focus.
-/
def compareArccos (p q : ℚ) (levels : Nat) : ℚ → Ordering :=
  let ladder := cacheIntervals (minorLadder p q) levels
  let quarter := TrigonometricComparison.prepareArctan 1 levels
  fun boundary =>
    if hpositive : boundary ≤ 0 then
      if boundary = 0 ∧ p = 0 ∧ 1 ≤ q then .eq else .gt
    else if quarter.compare (boundary / 4) = .lt then .lt
    else
      (compare (fun n => (ladder.get n).sub (Trig.cos.intervals boundary n)) 0 (by
        simpa only [ladder, cacheIntervals_apply] using
          ((converges_minorLadder p q).sub
            (Trig.converges_intervals .cos boundary)).exists_separates
            (by simpa [Trig.eval] using
              minor_sub_cos_ne_zero p q (ne_of_gt (not_le.mp hpositive))))).swap

/-- `compareArcosh` orders `arcosh (major p q)` against every rational boundary. -/
theorem compareArcosh_eq_real (p q : ℚ) (levels : Nat) (boundary : ℚ) :
    compareArcosh p q levels boundary = cmp (Real.arcosh (major p q)) (boundary : ℝ) := by
  have hmajor := one_le_major (p : ℝ) q
  unfold compareArcosh
  split
  · rename_i hnonpos
    have hb : (boundary : ℝ) ≤ 0 := by exact_mod_cast hnonpos
    split
    · rename_i h
      obtain ⟨rfl, hp, hq⟩ := h
      rw [major_eq_one (by exact_mod_cast hp) (by exact_mod_cast hq), Real.arcosh_zero]
      simp [cmp, cmpUsing]
    · rename_i h
      by_cases hzero : boundary = 0
      · have hne : ¬((p : ℝ) = 0 ∧ |(q : ℝ)| ≤ 1) := fun ⟨hp, hq⟩ =>
          h ⟨hzero, by exact_mod_cast hp, by exact_mod_cast hq⟩
        exact ((cmp_eq_gt_iff _ _).mpr (hb.trans_lt (Real.arcosh_pos (one_lt_major hne)))).symm
      · have hneg : (boundary : ℝ) < 0 := lt_of_le_of_ne hb (by exact_mod_cast hzero)
        exact ((cmp_eq_gt_iff _ _).mpr (hneg.trans_le (Real.arcosh_nonneg hmajor))).symm
  · rename_i hpositive
    have ht : (0 : ℝ) < boundary := by exact_mod_cast not_le.mp hpositive
    split
    · rename_i hguard
      have hg : ((guard p q : ℕ) : ℝ) ≤ boundary := by exact_mod_cast hguard
      exact ((cmp_eq_lt_iff _ _).mpr ((arcosh_major_lt_guard p q).trans_le hg)).symm
    · rw [Converges.compare_eq (by
        simpa only [cacheIntervals_apply] using
          (converges_majorLadder p q).sub (converges_coshLadder boundary))]
      have hlt : major p q < Real.cosh boundary ↔ Real.arcosh (major p q) < boundary := by
        conv_lhs => rw [← Real.cosh_arcosh hmajor]
        rw [Real.cosh_lt_cosh, abs_of_nonneg (Real.arcosh_nonneg hmajor), abs_of_pos ht]
      have hgt : Real.cosh boundary < major p q ↔ (boundary : ℝ) < Real.arcosh (major p q) := by
        conv_lhs => rw [← Real.cosh_arcosh hmajor]
        rw [Real.cosh_lt_cosh, abs_of_nonneg (Real.arcosh_nonneg hmajor), abs_of_pos ht]
      simp only [Rat.cast_zero, cmp, cmpUsing, sub_neg, sub_pos, hlt, hgt]

/-- `compareArcsin` orders `arcsin (minor p q)` against every rational boundary. -/
theorem compareArcsin_eq_real (p q : ℚ) (levels : Nat) (boundary : ℚ) :
    compareArcsin p q levels boundary = cmp (Real.arcsin (minor p q)) (boundary : ℝ) := by
  have hminor : minor (p : ℝ) q ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨neg_one_le_minor _ _, minor_le_one _ _⟩
  unfold compareArcsin
  split
  · rename_i hzero
    subst hzero
    have hlt : Real.arcsin (minor (p : ℝ) q) < 0 ↔ q < 0 := by
      rw [Real.arcsin_lt_zero, minor_neg_iff]
      norm_cast
    have hgt : 0 < Real.arcsin (minor (p : ℝ) q) ↔ 0 < q := by
      rw [Real.arcsin_pos, minor_pos_iff]
      norm_cast
    simp only [Rat.cast_zero, cmp, cmpUsing, hlt, hgt]
  · simp only [TrigonometricComparison.prepareArctan_eq_real, Rat.cast_one, Real.arctan_one,
      Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, cmp_eq_lt_iff]
    split
    · rename_i hb
      exact ((Real.arcsin_le_pi_div_two _).trans_lt (by linarith)).cmp_eq_lt.symm
    · rename_i hbupper
      split
      · rename_i hb
        exact ((show (boundary : ℝ) < -(Real.pi / 2) by linarith).trans_le
          (Real.neg_pi_div_two_le_arcsin _)).cmp_eq_gt.symm
      · rename_i hblower
        have hb : (boundary : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
          ⟨by linarith [le_of_not_gt hblower], by linarith [le_of_not_gt hbupper]⟩
        rw [Converges.compare_eq (by
          simpa only [cacheIntervals_apply] using
            (converges_minorLadder p q).sub (Trig.converges_intervals .sin boundary))]
        simp only [Trig.eval, Rat.cast_zero, cmp, cmpUsing, sub_neg, sub_pos,
          Real.arcsin_lt_iff_lt_sin hminor hb, Real.lt_arcsin_iff_sin_lt hb hminor]

/-- `compareArccos` orders `arccos (minor p q)` against every rational boundary. -/
theorem compareArccos_eq_real (p q : ℚ) (levels : Nat) (boundary : ℚ) :
    compareArccos p q levels boundary = cmp (Real.arccos (minor p q)) (boundary : ℝ) := by
  have hlower := neg_one_le_minor (p : ℝ) q
  have hupper := minor_le_one (p : ℝ) q
  unfold compareArccos
  split
  · rename_i hnonpos
    have hb : (boundary : ℝ) ≤ 0 := by exact_mod_cast hnonpos
    split
    · rename_i h
      obtain ⟨rfl, hp, hq⟩ := h
      rw [Real.arccos_eq_zero.mpr
        (one_le_minor_iff.mpr ⟨by exact_mod_cast hp, by exact_mod_cast hq⟩)]
      simp [cmp, cmpUsing]
    · rename_i h
      by_cases hzero : boundary = 0
      · have hne : ¬((p : ℝ) = 0 ∧ 1 ≤ (q : ℝ)) := fun ⟨hp, hq⟩ =>
          h ⟨hzero, by exact_mod_cast hp, by exact_mod_cast hq⟩
        have hpos : 0 < Real.arccos (minor (p : ℝ) q) :=
          Real.arccos_pos.mpr (lt_of_not_ge fun hge => hne (one_le_minor_iff.mp hge))
        exact ((cmp_eq_gt_iff _ _).mpr (hb.trans_lt hpos)).symm
      · have hneg : (boundary : ℝ) < 0 := lt_of_le_of_ne hb (by exact_mod_cast hzero)
        exact ((cmp_eq_gt_iff _ _).mpr (hneg.trans_le (Real.arccos_nonneg _))).symm
  · rename_i hpositive
    have ht : (0 : ℝ) < boundary := by exact_mod_cast not_le.mp hpositive
    simp only [TrigonometricComparison.prepareArctan_eq_real, Rat.cast_one, Real.arctan_one,
      Rat.cast_div, Rat.cast_ofNat, cmp_eq_lt_iff]
    split
    · rename_i hb
      exact ((Real.arccos_le_pi _).trans_lt (by linarith)).cmp_eq_lt.symm
    · rename_i hbpi
      have hb : (boundary : ℝ) ∈ Set.Icc 0 Real.pi := ⟨ht.le, by linarith [le_of_not_gt hbpi]⟩
      have ha : Real.arccos (minor (p : ℝ) q) ∈ Set.Icc 0 Real.pi :=
        ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
      have hlt : Real.cos (boundary : ℝ) < minor p q ↔
          Real.arccos (minor (p : ℝ) q) < boundary := by
        simpa only [Real.cos_arccos hlower hupper] using
          Real.strictAntiOn_cos.lt_iff_gt hb ha
      have hgt : minor (p : ℝ) q < Real.cos (boundary : ℝ) ↔
          (boundary : ℝ) < Real.arccos (minor (p : ℝ) q) := by
        simpa only [Real.cos_arccos hlower hupper] using
          Real.strictAntiOn_cos.lt_iff_gt ha hb
      rw [Converges.compare_eq (by
        simpa only [cacheIntervals_apply] using
          (converges_minorLadder p q).sub (Trig.converges_intervals .cos boundary)), cmp_swap]
      simp only [Trig.eval, Rat.cast_zero, cmp, cmpUsing, sub_neg, sub_pos, hlt, hgt]

end FloatLib.Numerics.ConfocalComparison
