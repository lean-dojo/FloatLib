/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Catalog

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring

/-!
# Worked instances of block scaling

These are kernel-checked instances of the general theorems of `Formats.Block`, on explicit
data. They cover one example each, not all data: the general statements are in `Block.Format`,
`Block.Bounds`, `Block.Transpose` and `Block.Catalog`.

## One outlier

`nvfp4_outlier` and `mxfp4_outlier`: in a matrix whose entries are `3/4` except one entry `42`,
the elements NVFP4 and MXFP4 flush to zero are exactly the other elements of the outlier's block,
for every block shape. So the count is the block size minus one:

* `nvfp4_tile_row_blocks`: a `16 × 16` tile in `1 × 16` blocks loses 15 values and keeps 241;
* `nvfp4_tile_square`: the same tile as one `16 × 16` block loses 255 and keeps the outlier;
* `nvfp4_wide_row_blocks`, `mxfp4_wide_row_blocks`, `nvfp4_wide_square`: on a `16 × 32` matrix,
  `1 × 16` NVFP4 blocks lose 15 values, `1 × 32` MXFP4 blocks lose 31 and `16 × 16` tiles
  lose 255.

These are the counts of the second tile figure of Thinking Machines' "End-to-End 4-Bit Training"
(13 November 2026): 241 of 256 values survive `1 × 16` scaling and only the outlier survives
`16 × 16` scaling. The figure's data is not published; the data here is ours.

## One large row, and transposition

`rowTile` is a `16 × 16` tile with a first row of `42`, nineteen entries `3` and `3/4` elsewhere.

* `rowTile_row_blocks`: with `1 × 16` blocks every value survives;
* `rowTile_col_blocks`: with `16 × 1` blocks the large row and the nineteen entries survive and
  the other 221 values are flushed to zero, the count of the post's first tile figure;
* `transpose_mismatch`: quantizing the transpose of `rowTile` with `1 × 16` blocks is not the
  transpose of quantizing `rowTile` with `1 × 16` blocks. This is the counterexample to
  transposition for `1 × 16` blocks; for square tiles `nvfp4_reconstruct_transpose` proves equality.

## Four Over Six

`fourOverSix_not_optimal`: for the block `(48, 42, 42)` both candidate scales `48 / 6 = 8` and
`48 / 4 = 12` leave squared error `72`, and the scale `11`, which E4M3 stores exactly, leaves
`24`. The selection minimizes over its two candidates (`ofCandidates_error_le`) and not over all
scales.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.BlockExamples

open FloatLib FloatLib.Floats FloatLib.Floats.Formats FloatLib.Floats.Formats.Block
open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Floats.Formats.BinaryInterchange.Model

/-! ## Stored values used by the examples -/

/-- Binary32 stores `2 ^ (-6)` exactly. -/
theorem binary32_fixes_outer : (Rounding.grid .binary32).Fixes (42 / (6 * 448)) := by
  have h := Rounding.grid_fixes_natCast_mul_zpow .binary32 1 (-6) (r := 8388608) (t := -29)
    (by decide) (by decide) (by norm_num)
  norm_num at h ⊢
  exact h

/-- E4M3 stores 448 exactly. -/
theorem e4m3_fixes_448 : (Rounding.saturating .e4m3).Fixes 448 := by
  have h := Rounding.saturating_fixes_natCast_mul_zpow .e4m3 7 6 (r := 14) (t := 5)
    (by decide) (by decide) (by norm_num) (by rw [toReal_posMaxFinite_e4m3]; norm_num)
  norm_num at h
  exact h

/-- E4M3 stores 32 exactly. -/
theorem e4m3_fixes_32 : (Rounding.saturating .e4m3).Fixes 32 := by
  have h := Rounding.saturating_fixes_natCast_mul_zpow .e4m3 1 5 (r := 8) (t := 2)
    (by decide) (by decide) (by norm_num) (by rw [toReal_posMaxFinite_e4m3]; norm_num)
  norm_num at h
  exact h

/-- E4M3 stores 8 exactly. -/
theorem e4m3_fixes_8 : (Rounding.saturating .e4m3).Fixes 8 := by
  have h := Rounding.saturating_fixes_natCast_mul_zpow .e4m3 1 3 (r := 8) (t := 0)
    (by decide) (by decide) (by norm_num) (by rw [toReal_posMaxFinite_e4m3]; norm_num)
  norm_num at h
  exact h

/-- E4M3 stores 12 exactly. -/
theorem e4m3_fixes_12 : (Rounding.saturating .e4m3).Fixes 12 := by
  have h := Rounding.saturating_fixes_natCast_mul_zpow .e4m3 3 2 (r := 12) (t := 0)
    (by decide) (by decide) (by norm_num) (by rw [toReal_posMaxFinite_e4m3]; norm_num)
  norm_num at h
  exact h

/-! ## One outlier -/

/-- A matrix whose entries are `3/4` except the entry `42` at `p₀`. -/
noncomputable def outlier {m n : ℕ} (p₀ : Fin m × Fin n) (p : Fin m × Fin n) : ℝ :=
  if p = p₀ then 42 else 3 / 4

private theorem abs_outlier_le {m n : ℕ} (p₀ p : Fin m × Fin n) : |outlier p₀ p| ≤ 42 := by
  unfold outlier
  split <;> norm_num

private theorem amax_outlier_of_mem {m n : ℕ} (group : Fin m × Fin n → ℕ × ℕ)
    (p₀ p : Fin m × Fin n) (h : group p = group p₀) :
    amax group (outlier p₀) (group p) = 42 :=
  amax_eq (fun q _ => abs_outlier_le p₀ q) ⟨p₀, h.symm, by simp [outlier]⟩

private theorem amax_outlier_of_not_mem {m n : ℕ} (group : Fin m × Fin n → ℕ × ℕ)
    (p₀ p : Fin m × Fin n) (h : group p ≠ group p₀) :
    amax group (outlier p₀) (group p) = 3 / 4 := by
  have hne : ∀ q, group q = group p → q ≠ p₀ := fun q hq hq0 => h (hq0 ▸ hq.symm)
  have hval : ∀ q, group q = group p → outlier p₀ q = 3 / 4 := fun q hq => by
    simp [outlier, hne q hq]
  exact amax_eq (fun q hq => by rw [hval q hq]; norm_num) ⟨p, rfl, by rw [hval p rfl]; norm_num⟩

/--
NVFP4 with one outer scale for the tensor, on a matrix with one outlier: the elements flushed to
zero are exactly the other elements of the outlier's block, whatever the block shape.
-/
theorem nvfp4_outlier {m n : ℕ} (block : Fin m × Fin n → ℕ × ℕ) (p₀ p : Fin m × Fin n) :
    (nvfp4 (tiles 0 0) block).reconstruct (outlier p₀) p = 0 ↔ p ≠ p₀ ∧ block p = block p₀ := by
  have hT : amax (tiles 0 0) (outlier p₀) (tiles 0 0 p) = 42 :=
    amax_outlier_of_mem (tiles 0 0) p₀ p (by simp [tiles])
  have hnest : ∀ j, block j = block p → tiles (m := m) (n := n) 0 0 j = tiles 0 0 p :=
    fun j _ => by simp [tiles]
  by_cases hb : block p = block p₀
  · have ha := amax_outlier_of_mem block p₀ p hb
    rw [nvfp4_reconstruct_eq_zero_iff_of_fixes (tiles 0 0) block (outlier p₀) p hnest
      (by rw [ha]; norm_num) (by rw [hT]; norm_num) (by rw [hT]; exact binary32_fixes_outer)
      (by rw [ha, hT]; norm_num; exact e4m3_fixes_448), ha]
    by_cases hp : p = p₀
    · simp [outlier, hp]
      norm_num
    · simp [outlier, hp, hb]
      norm_num
  · have ha := amax_outlier_of_not_mem block p₀ p hb
    have hp : p ≠ p₀ := fun h => hb (h ▸ rfl)
    rw [nvfp4_reconstruct_eq_zero_iff_of_fixes (tiles 0 0) block (outlier p₀) p hnest
      (by rw [ha]; norm_num) (by rw [hT]; norm_num) (by rw [hT]; exact binary32_fixes_outer)
      (by rw [ha, hT]; norm_num; exact e4m3_fixes_8), ha]
    simp [outlier, hp, hb]
    norm_num

/--
MXFP4 (E2M1 elements, blocks of `k` along a row, the power-of-two rule) on a matrix with one
outlier: the elements flushed to zero are exactly the other elements of the outlier's block.
-/
theorem mxfp4_outlier {m n : ℕ} (k : ℕ) (p₀ p : Fin m × Fin n) :
    (mx (Rounding.saturating .e2m1) 2 k).reconstruct (outlier p₀) p = 0 ↔
      p ≠ p₀ ∧ tiles 1 k p = tiles 1 k p₀ := by
  have hzero := fun y => e2m1_round_eq_zero_iff y
  by_cases hb : tiles 1 k p = tiles 1 k p₀
  · have ha := amax_outlier_of_mem (tiles 1 k) p₀ p hb
    have hs : (mx (Rounding.saturating .e2m1) 2 k).scale (outlier p₀) p = 8 := by
      rw [mx_scale _ _ _ _ _ (by rw [ha]; norm_num), ha,
        Rounding.pow2Floor_round_eq (e := 3) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num)]
      norm_num
    rw [Format.reconstruct_eq_zero_iff_abs_le _ _ _ hzero (by rw [hs]; norm_num), hs]
    by_cases hp : p = p₀
    · simp [outlier, hp]
      norm_num
    · simp [outlier, hp, hb]
      norm_num
  · have ha := amax_outlier_of_not_mem (tiles 1 k) p₀ p hb
    have hp : p ≠ p₀ := fun h => hb (h ▸ rfl)
    have hs : (mx (Rounding.saturating .e2m1) 2 k).scale (outlier p₀) p = 1 / 8 := by
      rw [mx_scale _ _ _ _ _ (by rw [ha]; norm_num), ha,
        Rounding.pow2Floor_round_eq (e := -3) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num)]
      norm_num
    rw [Format.reconstruct_eq_zero_iff_abs_le _ _ _ hzero (by rw [hs]; norm_num), hs]
    simp [outlier, hp, hb]
    norm_num

set_option maxRecDepth 100000 in
/-- A `16 × 16` tile with one outlier in `1 × 16` NVFP4 blocks: 15 values are flushed to zero and
241 survive. -/
theorem nvfp4_tile_row_blocks :
    (Finset.univ.filter fun p : Fin 16 × Fin 16 =>
      (nvfp4 (tiles 0 0) (tiles 1 16)).reconstruct (outlier (0, 0)) p = 0).card = 15 := by
  rw [Finset.filter_congr fun p _ => nvfp4_outlier (tiles 1 16) (0, 0) p]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The same tile as one `16 × 16` NVFP4 block: 255 values are flushed to zero and only the
outlier survives. -/
theorem nvfp4_tile_square :
    (Finset.univ.filter fun p : Fin 16 × Fin 16 =>
      (nvfp4 (tiles 0 0) (tiles 16 16)).reconstruct (outlier (0, 0)) p = 0).card = 255 := by
  rw [Finset.filter_congr fun p _ => nvfp4_outlier (tiles 16 16) (0, 0) p]
  decide +kernel

set_option maxRecDepth 100000 in
/-- A `16 × 32` matrix with one outlier in `1 × 16` NVFP4 blocks: 15 values are flushed. -/
theorem nvfp4_wide_row_blocks :
    (Finset.univ.filter fun p : Fin 16 × Fin 32 =>
      (nvfp4 (tiles 0 0) (tiles 1 16)).reconstruct (outlier (0, 0)) p = 0).card = 15 := by
  rw [Finset.filter_congr fun p _ => nvfp4_outlier (tiles 1 16) (0, 0) p]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The same matrix in `1 × 32` MXFP4 blocks: 31 values are flushed. -/
theorem mxfp4_wide_row_blocks :
    (Finset.univ.filter fun p : Fin 16 × Fin 32 =>
      (mx (Rounding.saturating .e2m1) 2 32).reconstruct (outlier (0, 0)) p = 0).card = 31 := by
  rw [Finset.filter_congr fun p _ => mxfp4_outlier 32 (0, 0) p]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The same matrix in `16 × 16` NVFP4 tiles: 255 values are flushed. -/
theorem nvfp4_wide_square :
    (Finset.univ.filter fun p : Fin 16 × Fin 32 =>
      (nvfp4 (tiles 0 0) (tiles 16 16)).reconstruct (outlier (0, 0)) p = 0).card = 255 := by
  rw [Finset.filter_congr fun p _ => nvfp4_outlier (tiles 16 16) (0, 0) p]
  decide +kernel

/-! ## One large row, and transposition -/

/-- A `16 × 16` tile whose first row is `42`, with `3` in the second row and in the first three
entries of the third row, and `3/4` elsewhere. -/
noncomputable def rowTile (p : Fin 16 × Fin 16) : ℝ :=
  if p.1 = 0 then 42 else if p.1 = 1 ∨ (p.1 = 2 ∧ p.2.val < 3) then 3 else 3 / 4

private theorem abs_rowTile_le (p : Fin 16 × Fin 16) : |rowTile p| ≤ 42 := by
  unfold rowTile
  split_ifs <;> norm_num

private theorem rowTile_outer (p : Fin 16 × Fin 16) :
    amax (tiles 0 0) rowTile (tiles 0 0 p) = 42 :=
  amax_eq (fun q _ => abs_rowTile_le q) ⟨(0, 0), by simp [tiles], by simp [rowTile]⟩

private theorem rowTile_nest (block : Fin 16 × Fin 16 → ℕ × ℕ) (p : Fin 16 × Fin 16) :
    ∀ j, block j = block p → tiles (m := 16) (n := 16) 0 0 j = tiles 0 0 p :=
  fun j _ => by simp [tiles]

/-- With `16 × 1` blocks, the elements of `rowTile` flushed to zero are those equal to `3/4`. -/
theorem rowTile_col_flush (p : Fin 16 × Fin 16) :
    (nvfp4 (tiles 0 0) (tiles 16 1)).reconstruct rowTile p = 0 ↔
      p.1 ≠ 0 ∧ ¬(p.1 = 1 ∨ (p.1 = 2 ∧ p.2.val < 3)) := by
  have ha : amax (tiles 16 1) rowTile (tiles 16 1 p) = 42 :=
    amax_eq (fun q _ => abs_rowTile_le q)
      ⟨(0, p.2), by simp [tiles, Nat.div_eq_of_lt p.1.isLt], by simp [rowTile]⟩
  rw [nvfp4_reconstruct_eq_zero_iff_of_fixes (tiles 0 0) (tiles 16 1) rowTile p
    (rowTile_nest _ p) (by rw [ha]; norm_num) (by rw [rowTile_outer]; norm_num)
    (by rw [rowTile_outer]; exact binary32_fixes_outer)
    (by rw [ha, rowTile_outer]; norm_num; exact e4m3_fixes_448), ha]
  by_cases h0 : p.1 = 0
  · simp [rowTile, h0]
    norm_num
  · by_cases hb : p.1 = 1 ∨ (p.1 = 2 ∧ p.2.val < 3)
    · simp [rowTile, h0, hb]
      norm_num
    · simp [rowTile, h0, hb]
      norm_num

set_option maxRecDepth 100000 in
/-- With `16 × 1` blocks, 221 of the 256 values of `rowTile` are flushed to zero: the large row
and the nineteen entries `3` survive. -/
theorem rowTile_col_blocks :
    (Finset.univ.filter fun p : Fin 16 × Fin 16 =>
      (nvfp4 (tiles 0 0) (tiles 16 1)).reconstruct rowTile p = 0).card = 221 := by
  rw [Finset.filter_congr fun p _ => rowTile_col_flush p]
  decide +kernel

/-- With `1 × 16` blocks, every value of `rowTile` survives. -/
theorem rowTile_row_blocks (p : Fin 16 × Fin 16) :
    (nvfp4 (tiles 0 0) (tiles 1 16)).reconstruct rowTile p ≠ 0 := by
  have hgroup : ∀ q : Fin 16 × Fin 16, tiles 1 16 q = tiles 1 16 p ↔ q.1 = p.1 := by
    intro q
    simp [tiles, Nat.div_eq_of_lt q.2.isLt, Nat.div_eq_of_lt p.2.isLt, Fin.ext_iff]
  have hflush := fun (a : ℝ) (ha : amax (tiles 1 16) rowTile (tiles 1 16 p) = a) (ha0 : 0 < a)
      (hfix : (Rounding.saturating .e4m3).Fixes (a / 6 / (42 / (6 * 448)))) =>
    nvfp4_reconstruct_eq_zero_iff_of_fixes (tiles 0 0) (tiles 1 16) rowTile p
      (rowTile_nest _ p) (by rw [ha]; exact ha0) (by rw [rowTile_outer]; norm_num)
      (by rw [rowTile_outer]; exact binary32_fixes_outer) (by rw [ha, rowTile_outer]; exact hfix)
  by_cases h0 : p.1 = 0
  · have ha : amax (tiles 1 16) rowTile (tiles 1 16 p) = 42 :=
      amax_eq (fun q _ => abs_rowTile_le q) ⟨p, rfl, by simp [rowTile, h0]⟩
    rw [Ne, hflush 42 ha (by norm_num) (by norm_num; exact e4m3_fixes_448), ha]
    simp [rowTile, h0]
    norm_num
  by_cases h1 : p.1 = 1
  · have ha : amax (tiles 1 16) rowTile (tiles 1 16 p) = 3 :=
      amax_eq (fun q hq => by simp [rowTile, (hgroup q).mp hq, h1])
        ⟨p, rfl, by simp [rowTile, h1]⟩
    rw [Ne, hflush 3 ha (by norm_num) (by norm_num; exact e4m3_fixes_32), ha]
    simp [rowTile, h1]
    norm_num
  have h20 : ¬((2 : Fin 16) = 0) := by decide
  by_cases h2 : p.1 = 2
  · have ha : amax (tiles 1 16) rowTile (tiles 1 16 p) = 3 :=
      amax_eq (fun q hq => by
          have hq2 := (hgroup q).mp hq
          simp only [rowTile, hq2, h2, h20, ite_false]
          split_ifs <;> norm_num)
        ⟨(2, 0), (hgroup _).mpr h2.symm, by simp [rowTile]⟩
    rw [Ne, hflush 3 ha (by norm_num) (by norm_num; exact e4m3_fixes_32), ha]
    simp only [rowTile, h2, h20, ite_false]
    split_ifs <;> norm_num
  · have hval : ∀ q : Fin 16 × Fin 16, q.1 = p.1 → rowTile q = 3 / 4 := by
      intro q hq
      simp [rowTile, hq, h0, h1, h2]
    have ha : amax (tiles 1 16) rowTile (tiles 1 16 p) = 3 / 4 :=
      amax_eq (fun q hq => by rw [hval q ((hgroup q).mp hq)]; norm_num)
        ⟨p, rfl, by rw [hval p rfl]; norm_num⟩
    rw [Ne, hflush (3 / 4) ha (by norm_num) (by norm_num; exact e4m3_fixes_8), ha, hval p rfl]
    norm_num

/--
Transposition fails for `1 × 16` blocks: there is a `16 × 16` matrix whose transpose, quantized in
NVFP4, is not the transpose of the quantized matrix. On `rowTile` the entry in row 3 and column 0
is reconstructed as zero from the transpose and is nonzero from the matrix.
-/
theorem transpose_mismatch :
    ∃ (x : Fin 16 × Fin 16 → ℝ) (i j : Fin 16),
      (nvfp4 (tiles 0 0) (tiles 1 16)).reconstruct (fun p => x (p.2, p.1)) (j, i) ≠
        (nvfp4 (tiles 0 0) (tiles 1 16)).reconstruct x (i, j) := by
  refine ⟨rowTile, 3, 0, ?_⟩
  rw [nvfp4_reconstruct_transpose 16 1 rowTile 0 3,
    (rowTile_col_flush (3, 0)).mpr (by decide)]
  exact (rowTile_row_blocks (3, 0)).symm

/-! ## Four Over Six -/

/-- The block `(48, 42, 42)`. -/
noncomputable def fosBlock : Fin 3 → ℝ := ![48, 42, 42]

private theorem e2m1_monotone : Monotone (Rounding.saturating .e2m1).round :=
  Rounding.saturating_monotone .e2m1 .nearest

private theorem e2m1_round_eq {sig : ℕ} {exp : ℤ} {r : ℕ} {t : ℤ} {y v : ℝ}
    (ht : max ((sig.log2 : ℤ) + exp - FloatFormat.e2m1.fracWidth)
      FloatFormat.e2m1.minSubnormalExponent = t)
    (hr : roundMantissaAtExponentEven sig exp t = r)
    (hy : y = (sig : ℝ) * (2 : ℝ) ^ exp) (hv : (r : ℝ) * (2 : ℝ) ^ t = v) (hM : v ≤ 6) :
    (Rounding.saturating .e2m1).round y = v := by
  rw [hy, Rounding.saturating_round_natCast_mul_zpow .e2m1 sig exp ht hr
    (by rw [hv, toReal_posMaxFinite_e2m1]; exact hM), hv]

/--
Four Over Six does not minimize over all scales. For the block `(48, 42, 42)` the squared error
of both candidates, target `6` with scale `8` and target `4` with scale `12`, is `72`, and the
scale `11`, which E4M3 stores exactly, has squared error `24`.
-/
theorem fourOverSix_not_optimal :
    candidateError (fun _ : Fin 3 => ()) (Rounding.saturating .e4m3)
        (fun _ => Rounding.saturating .e2m1) (fun e => e ^ 2) fosBlock () 6 = 72 ∧
      candidateError (fun _ : Fin 3 => ()) (Rounding.saturating .e4m3)
        (fun _ => Rounding.saturating .e2m1) (fun e => e ^ 2) fosBlock () 4 = 72 ∧
      ∑ i, (((Rounding.saturating .e2m1).scaled 11).round (fosBlock i) - fosBlock i) ^ 2 = 24 := by
  have hmembers : members (fun _ : Fin 3 => ()) () = Finset.univ := by
    ext i
    simp
  have hamax : amax (fun _ : Fin 3 => ()) fosBlock () = 48 :=
    amax_eq (fun i _ => by fin_cases i <;> simp [fosBlock] <;> norm_num)
      ⟨0, rfl, by simp [fosBlock]⟩
  -- E2M1 values used below.
  have r6 : (Rounding.saturating .e2m1).round 6 = 6 := e2m1_round_of_le le_rfl
  have r21 : (Rounding.saturating .e2m1).round (21 / 4) = 6 :=
    e2m1_round_eq (sig := 21) (exp := -2) (r := 3) (t := 1) (by decide) (by decide)
      (by norm_num) (by norm_num) le_rfl
  have r4 : (Rounding.saturating .e2m1).round 4 = 4 :=
    e2m1_round_eq (sig := 1) (exp := 2) (r := 2) (t := 1) (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num)
  have r7 : (Rounding.saturating .e2m1).round (7 / 2) = 4 :=
    e2m1_round_eq (sig := 7) (exp := -1) (r := 4) (t := 0) (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num)
  have r9 : (Rounding.saturating .e2m1).round (9 / 2) = 4 :=
    e2m1_round_eq (sig := 9) (exp := -1) (r := 2) (t := 1) (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num)
  have r15 : (Rounding.saturating .e2m1).round (15 / 4) = 4 :=
    e2m1_round_eq (sig := 15) (exp := -2) (r := 4) (t := 0) (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num)
  have r48 : (Rounding.saturating .e2m1).round (48 / 11) = 4 :=
    Rounding.round_eq_of_le_of_le e2m1_monotone r4 r9 (by norm_num) (by norm_num)
  have r42 : (Rounding.saturating .e2m1).round (42 / 11) = 4 :=
    Rounding.round_eq_of_le_of_le e2m1_monotone r15 r4 (by norm_num) (by norm_num)
  have s8 : (Rounding.saturating .e4m3).round (48 / 6) = 8 := by
    have := e4m3_fixes_8
    norm_num [Rounding.Fixes] at this ⊢
    exact this
  have s12 : (Rounding.saturating .e4m3).round (48 / 4) = 12 := by
    have := e4m3_fixes_12
    norm_num [Rounding.Fixes] at this ⊢
    exact this
  have f0 : fosBlock 0 = 48 := rfl
  have f1 : fosBlock 1 = 42 := rfl
  have f2 : fosBlock 2 = 42 := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [candidateError, hmembers, hamax, s8, Fin.sum_univ_three, Rounding.scaled_round,
      f0, f1, f2]
    norm_num [r6, r21]
  · simp only [candidateError, hmembers, hamax, s12, Fin.sum_univ_three, Rounding.scaled_round,
      f0, f1, f2]
    norm_num [r4, r7]
  · simp only [Fin.sum_univ_three, Rounding.scaled_round, f0, f1, f2]
    norm_num [r48, r42]

end FloatLibTests.Conformance.Formats.BlockExamples
