/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Util.CollectAxioms
public import FloatLib.Floats.Formats.Block
public import FloatLib.Floats.Formats.OCP.MX
public import FloatLib.Floats.Formats.P3109
public import FloatLibTests.Conformance.Formats.BlockExamples

/-!
# The general block theory on named formats

The theorems of `Formats.Block` are stated for every element format, scale format, level structure
and selection rule. Each check below applies one of them to a named format and discharges its
premises, so the premise is not vacuous there:

* MXFP4 and MXFP8: the error of an element and of a block for every tensor, and flush to zero
  under ties away from zero and under rounding toward zero.
* NVFP4: the error in terms of the block maximum with E4M3's relative scale error, and
  transposition with square tiles, also for Four Over Six.
* S2F6 in blocks of 32: the error bound `a / 127` and the flush-to-zero threshold.
* Exact accumulation.

The stored formats run on three blocks of 16: NVFP4 with its policy, and Four Over Six on a block
where both candidates have the same squared error (the target `6` is kept) and on a block where
the target `4` is strictly better.

The bounds of the stored codes are instantiated for MXFP8, MXINT8 and NVFP4 storage, and so is
the equality of the stored elements with the real rounding of their format (saturating
nearest-even for the floating elements, S2F6 fixed point for the combine format), with one real
theorem (exactness on element values) carried to stored NVFP4 codes. Stored NVFP4 and stored
MX with their standard selections are identified with the real formats `nvfp4` and `mx`, scales
included. Two theorems of the real format are carried to the values of the executable quantizer:
transposition with square tiles, and the post's counts of flushed values (255 of 256 on the
outlier tile as one block, 221 of 256 on the row tile with column blocks). The two counts are
about those two tensors. The last command collects the axioms
of the theorems of the block theory by name. The checks above cover the stated formats, and the
three blocks are examples.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.BlockTheory

open FloatLib.Floats FloatLib.Floats.Formats FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics FloatLib.Floats.Formats.Block

/-! ## The value theory on named formats -/

section Value

variable (x : Fin 4 × Fin 64 → ℝ) (i : Fin 4 × Fin 64)

/-- MXFP4: the error of every element of every tensor. -/
example :
    |(mx (Rounding.saturating .e2m1) 2).reconstruct x i - x i| ≤
      1 / 4 * |x i| + (mx (Rounding.saturating .e2m1) 2).scale x i * (1 / 4) +
        max 0 (|x i| - (mx (Rounding.saturating .e2m1) 2).scale x i * 6) :=
  mx_abs_reconstruct_sub_le _ 2 32 x i e2m1_budget

/-- MXFP4: the summed error of a block of 32. -/
example (g : ℕ × ℕ) :
    ∑ j ∈ members (tiles 1 32) g,
        |(mx (Rounding.saturating .e2m1) 2).reconstruct x j - x j| ≤
      1 / 4 * ∑ j ∈ members (tiles 1 32) g, |x j| +
        1 / 4 * ∑ j ∈ members (tiles 1 32) g, (mx (Rounding.saturating .e2m1) 2).scale x j +
          ∑ j ∈ members (tiles 1 32) g,
            max 0 (|x j| - (mx (Rounding.saturating .e2m1) 2).scale x j * 6) :=
  Format.sum_abs_reconstruct_sub_le _ x _ (fun _ _ => e2m1_budget)
    (fun j _ => mx_scale_pos _ 2 32 x j)

/-- MXFP4 with ties away from zero, the default rounding of `microxcaling`: the zero set is
open. -/
example :
    (mx (Rounding.saturating .e2m1 .nearestAway) 2).reconstruct x i = 0 ↔
      2 * (x i / (mx (Rounding.saturating .e2m1 .nearestAway) 2).scale x i) ∈
        Set.Ioo (-(1 / 2) : ℝ) (1 / 2) :=
  Format.e2m1_reconstruct_eq_zero_iff _ x i rfl (mx_scale_pos _ 2 32 x i).ne'

/-- MXFP8 with E4M3 elements rounded toward zero: everything below the least subnormal times the
block scale is flushed. -/
example :
    (mx (Rounding.saturating .e4m3 .towardZero) 8).reconstruct x i = 0 ↔
      x i / (mx (Rounding.saturating .e4m3 .towardZero) 8).scale x i /
        (2 * Model.underflowErrorAt .e4m3) ∈ Set.Ioo (-1 : ℝ) 1 :=
  Format.reconstruct_eq_zero_iff_of_mode _ x i rfl (mx_scale_pos _ 8 32 x i).ne'

/-- S2F6 in blocks of 32 with the scale rounded up to a power of two: nothing saturates, and the
error of an element is at most `a / 127`. -/
example (ha : 0 < amax (tiles 1 32) x (tiles 1 32 i))
    (hlo : -127 ≤ Int.clog 2 (amax (tiles 1 32) x (tiles 1 32 i) / (127 / 64 : ℝ)))
    (hhi : Int.clog 2 (amax (tiles 1 32) x (tiles 1 32 i) / (127 / 64 : ℝ)) ≤ 127) :
    |(combine 2 6 32 (Rounding.pow2Ceil (-127) 127) (127 / 64)).reconstruct x i - x i| ≤
      amax (tiles 1 32) x (tiles 1 32 i) / 127 := by
  have hT : (2 : ℝ) ^ (((2 : ℕ) : ℤ) - 1) - (2 : ℝ) ^ (-((6 : ℕ) : ℤ)) = 127 / 64 := by norm_num
  have h := combine_abs_reconstruct_sub_le_of_ceil 2 6 32 x i (-127) 127 (by norm_num) ha
    (by rw [hT]; exact hlo) (by rw [hT]; exact hhi)
  rw [hT] at h
  refine h.trans (le_of_eq ?_)
  norm_num
  ring

/-- S2F6 flush to zero, for every tensor: magnitudes up to `2 ^ (-7)` times the block scale. -/
example :
    (combine 2 6 32 (Rounding.pow2Ceil (-127) 127) (127 / 64)).reconstruct x i = 0 ↔
      |x i| ≤ (2 : ℝ) ^ (-((6 : ℕ) : ℤ) - 1) *
        (combine 2 6 32 (Rounding.pow2Ceil (-127) 127) (127 / 64)).scale x i :=
  combine_reconstruct_eq_zero_iff_of_ceil 2 6 32 (127 / 64) x i (-127) 127 (by norm_num)

end Value

section NVFP4

variable (y : Fin 16 × Fin 16 → ℝ) (p : Fin 16 × Fin 16)

/-- NVFP4 with a block scale within E4M3's relative error `1 / 16` of the ideal scale: the error
of an element is at most a quarter of its magnitude and `41 / 384` of the block maximum. -/
example (ha : 0 < amax (tiles 1 16) y (tiles 1 16 p))
    (hs : |(nvfp4 (tiles 0 0) (tiles 1 16)).scale y p - amax (tiles 1 16) y (tiles 1 16 p) / 6| ≤
      1 / 16 * (amax (tiles 1 16) y (tiles 1 16 p) / 6)) :
    |(nvfp4 (tiles 0 0) (tiles 1 16)).reconstruct y p - y p| ≤
      1 / 4 * |y p| + 41 / 384 * amax (tiles 1 16) y (tiles 1 16 p) := by
  have h := nvfp4_abs_reconstruct_sub_le_of_scale _ _ y p (by norm_num) ha hs
  linarith

/-- Square tiles: quantizing the transpose is the transpose of quantizing, for NVFP4 and for
Four Over Six with the squared error. -/
example (z : Fin 32 × Fin 32 → ℝ) (a b : Fin 32) :
    (nvfp4 (tiles 0 0) (tiles 16 16)).reconstruct (fun q => z (q.2, q.1)) (a, b) =
        (nvfp4 (tiles 0 0) (tiles 16 16)).reconstruct z (b, a) ∧
      (fourOverSix (fun e => e ^ 2) (tiles 0 0) (tiles 16 16)).reconstruct
          (fun q => z (q.2, q.1)) (a, b) =
        (fourOverSix (fun e => e ^ 2) (tiles 0 0) (tiles 16 16)).reconstruct z (b, a) :=
  ⟨nvfp4_reconstruct_transpose 16 16 z a b,
    fourOverSix_reconstruct_transpose (fun e => e ^ 2) 16 16 z a b⟩

end NVFP4

/-- Accumulation in the exact format is the sum of the terms. -/
example (terms : List ℝ) : accumulate Rounding.exact terms = terms.sum :=
  accumulate_eq_sum terms fun _ _ => rfl

/-! ## Stored formats on three blocks -/

/-- One block of 16 that is also the only outer group. -/
def whole : Fin 16 → Unit := fun _ => ()

/-- NVFP4 storage with NVIDIA's selection. -/
def nvfp4Block (values : Fin 16 → ℚ) :=
  (nvfp4Stored whole whole).quantize (nvfp4Policy whole whole) fun i => SignedRat.ofRat (values i)

/-- NVFP4 storage with the Four Over Six selection under the squared error. -/
def fourOverSixBlock (values : Fin 16 → ℚ) :=
  (nvfp4Stored whole whole).quantize (fourOverSixPolicy whole whole fun e => e ^ 2)
    fun i => SignedRat.ofRat (values i)

/-- The first lanes of a block, the rest zero. -/
def lanes (head : List ℚ) : Fin 16 → ℚ := fun i => head.getD i.val 0

/-- Element words of a stored block. -/
def words (t : Tensor (nvfp4Stored whole whole)) : List Nat :=
  (List.finRange 16).map fun i => (t.elements i).toNat

/-- NVFP4: the block scale is `448`, and the binary32 outer scale decides the tie at `3 / 4`. -/
example : ((nvfp4Block (lanes [6, -3, 3 / 4, 1 / 4])).scales.2.1 ()).toNat = 126 ∧
    words (nvfp4Block (lanes [6, -3, 3 / 4, 1 / 4])) =
      [7, 13, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- Four Over Six on `(48, 42, 42)`: both candidates have squared error `72`, and the target `6`
is kept, with block scale `256` in units of the outer scale `1 / 32`. -/
example : ((fourOverSixBlock (lanes [48, 42, 42])).scales.2.1 ()).toNat = 120 ∧
    words (fourOverSixBlock (lanes [48, 42, 42])) =
      [7, 7, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- Four Over Six on `(4, 3)`: the target `4` stores both values, the target `6` does not, and
the block scale `384` of the target `4` is kept. NVFP4's own selection stores `448`. -/
example : ((fourOverSixBlock (lanes [4, 3])).scales.2.1 ()).toNat = 124 ∧
    words (fourOverSixBlock (lanes [4, 3])) =
      [6, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∧
    ((nvfp4Block (lanes [4, 3])).scales.2.1 ()).toNat = 126 := by
  decide +kernel

/-! ## Bounds for stored codes -/

section StoredCodes

open FloatLib.Floats.Formats.OCP.MX

/-- MXFP8 with E4M3 elements, stored: the error budget of the codes, for every policy. -/
example (policy : Policy (Fin 4 × Fin 64) (ℕ × ℕ)) (x : Fin 4 × Fin 64 → SignedRat)
    (i : Fin 4 × Fin 64)
    (hσ : 0 < ((Standard.format (tiles 1 32) .e4m3).quantize policy x).scale i) :
    |((Standard.format (tiles 1 32) .e4m3).quantize policy x).value i - (x i).value| ≤
      1 / 16 * |(x i).value| +
        ((Standard.format (tiles 1 32) .e4m3).quantize policy x).scale i * (1 / 1024) +
        max 0 (|(x i).value| -
          ((Standard.format (tiles 1 32) .e4m3).quantize policy x).scale i * 448) :=
  Standard.Profile.abs_value_quantize_sub_le_budget .e4m3 _ rfl policy x i hσ

/-- MXINT8, stored: an input is stored as zero exactly when its magnitude is at most `1 / 128`
of the block scale. -/
example (policy : Policy (Fin 4 × Fin 64) (ℕ × ℕ)) (x : Fin 4 × Fin 64 → SignedRat)
    (i : Fin 4 × Fin 64)
    (hσ : 0 < ((Standard.format (tiles 1 32) .int8).quantize policy x).scale i) :
    ((Standard.format (tiles 1 32) .int8).quantize policy x).value i = 0 ↔
      |(x i).value| ≤ 1 / 128 * ((Standard.format (tiles 1 32) .int8).quantize policy x).scale i :=
  Standard.Profile.value_quantize_eq_zero_iff .int8 _ rfl policy x i hσ

/-- Stored NVFP4 with Four Over Six selection: the same budget and flush rule as with NVIDIA's
selection, because they hold for every policy. -/
example (x : Fin 16 → SignedRat) (i : Fin 16)
    (hσ : 0 < ((nvfp4Stored whole whole).quantize
      (fourOverSixPolicy whole whole fun e => e ^ 2) x).scale i) :=
  And.intro
    (nvfp4Stored_abs_value_sub_le_budget whole whole
      (fourOverSixPolicy whole whole fun e => e ^ 2) x i hσ)
    (nvfp4Stored_value_eq_zero_iff whole whole
      (fourOverSixPolicy whole whole fun e => e ^ 2) x i hσ)

/-- The E2M1 codec is the real saturating E2M1 rounding, on every rational. -/
example (q : ℚ) :
    (((Standard.Profile.codec .e2m1 .saturate).rounding.round q : ℚ) : ℝ) =
      (Rounding.saturating .e2m1).round (q : ℝ) :=
  Standard.Profile.codec_round_eq_real .e2m1 q

/-- The E4M3 codec, which stores NVFP4's block scales, is the real saturating E4M3 rounding. -/
example (q : ℚ) :
    (((Standard.Profile.codec .e4m3 .saturate).rounding.round q : ℚ) : ℝ) =
      (Rounding.saturating .e4m3).round (q : ℝ) :=
  Standard.Profile.codec_round_eq_real .e4m3 q

/-- The INT8 codec is nearest-even fixed point with six fractional bits clipped to
`[-2, 127 / 64]`, the S2F6 format. -/
example (q : ℚ) :
    (((Standard.Profile.codec .int8 .saturate).rounding.round q : ℚ) : ℝ) =
      (Rounding.fixed 6 (-2) (127 / 64)).round (q : ℝ) :=
  Standard.Profile.codec_round_eq_real .int8 q

/-- The combine format stored as S2F6 elements with a power-of-two scale per block of 32, the
scale rounded up: each stored value is the real S2F6 rounding at the stored scale. -/
example (x : Fin 4 × Fin 64 → SignedRat) (i : Fin 4 × Fin 64) :
    ((((Standard.format (tiles 1 32) .int8).quantize
        (mxMaxCeil (tiles 1 32) (127 / 64)) x).value i : ℚ) : ℝ) =
      ((Rounding.signedFixed 2 6).scaled
        ((((Standard.format (tiles 1 32) .int8).quantize
          (mxMaxCeil (tiles 1 32) (127 / 64)) x).scale i : ℚ) : ℝ)).round
            (((x i).value : ℚ) : ℝ) :=
  int8_value_eq_signedFixed _ rfl _ x i

/-- MXFP8 with E5M2 elements, stored: each stored value is the real saturating E5M2 rounding of
the input at the stored scale, for every policy and with no premise on the scale. -/
example (policy : Policy (Fin 4 × Fin 64) (ℕ × ℕ)) (x : Fin 4 × Fin 64 → SignedRat)
    (i : Fin 4 × Fin 64) :
    ((((Standard.format (tiles 1 32) .e5m2).quantize policy x).value i : ℚ) : ℝ) =
      ((Rounding.saturating .e5m2).scaled
        ((((Standard.format (tiles 1 32) .e5m2).quantize policy x).scale i : ℚ) : ℝ)).round
          (((x i).value : ℚ) : ℝ) :=
  Standard.Profile.value_quantize_eq_real .e5m2 _ rfl policy x i

/-- Stored NVFP4 with Four Over Six selection: each stored value is the real saturating E2M1
rounding at the stored scale, so a real theorem transfers. Here: an input that is an E2M1 value
times its positive stored scale is stored exactly. -/
example (x : Fin 16 → SignedRat) (i : Fin 16) (word : Model FloatFormat.e2m1)
    (hword : Model.isFinite word = true)
    (hσ : ((nvfp4Stored whole whole).quantize
      (fourOverSixPolicy whole whole fun e => e ^ 2) x).scale i ≠ 0)
    (hx : (((x i).value : ℚ) : ℝ) = Model.toReal word *
      ((((nvfp4Stored whole whole).quantize
        (fourOverSixPolicy whole whole fun e => e ^ 2) x).scale i : ℚ) : ℝ)) :
    ((nvfp4Stored whole whole).quantize
      (fourOverSixPolicy whole whole fun e => e ^ 2) x).value i = (x i).value := by
  have h := nvfp4Stored_value_eq_saturating whole whole
    (fourOverSixPolicy whole whole fun e => e ^ 2) x i
  rw [hx] at h
  have hfix := (Rounding.saturating_fixes word hword).scaled
    (σ := ((((nvfp4Stored whole whole).quantize
      (fourOverSixPolicy whole whole fun e => e ^ 2) x).scale i : ℚ) : ℝ))
    (by exact_mod_cast hσ)
  rw [show ((Rounding.saturating FloatFormat.e2m1).scaled _).round _ = _ from hfix, ← hx] at h
  exact_mod_cast h

/-- The transposition theorem of the real format carried to the executable quantizer: with
square tiles, the stored values of the transposed data are the transposed stored values, for
every tensor of magnitudes below `2 ^ 128`. `nvfp4Stored_value_eq_reconstruct_of_lt` turns both
sides into the real format `nvfp4`. -/
example (x : Fin 32 × Fin 32 → SignedRat) (hx : ∀ j, |(x j).value| < 2 ^ 128) (a b : Fin 32) :
    ((nvfp4Stored (tiles 0 0) (tiles 16 16)).quantize (nvfp4Policy (tiles 0 0) (tiles 16 16))
        fun q => x (q.2, q.1)).value (a, b) =
      ((nvfp4Stored (tiles 0 0) (tiles 16 16)).quantize (nvfp4Policy (tiles 0 0) (tiles 16 16))
        x).value (b, a) := by
  have h1 := nvfp4Stored_value_eq_reconstruct_of_lt (tiles 0 0) (tiles 16 16)
    (fun q => x (q.2, q.1)) (fun j => hx _) (a, b)
  have h2 := nvfp4Stored_value_eq_reconstruct_of_lt (tiles 0 0) (tiles 16 16) x hx (b, a)
  have h3 := nvfp4_reconstruct_transpose 16 16 (fun j => (((x j).value : ℚ) : ℝ)) a b
  exact_mod_cast h1.trans (h3.trans h2.symm)

/-- The executable NVFP4 quantizer stores a position as zero exactly when the real format
reconstructs zero there, for rational data of magnitudes below `2 ^ 128`. -/
theorem stored_eq_zero_iff {m n : ℕ} (outer block : Fin m × Fin n → ℕ × ℕ)
    (data : Fin m × Fin n → ℚ) (hdata : ∀ j, |data j| < 2 ^ 128) (p : Fin m × Fin n) :
    ((nvfp4Stored outer block).quantize (nvfp4Policy outer block)
        fun j => SignedRat.ofRat (data j)).value p = 0 ↔
      (nvfp4 outer block).reconstruct (fun j => (data j : ℝ)) p = 0 := by
  have h := nvfp4Stored_value_eq_reconstruct_of_lt outer block
    (fun j => SignedRat.ofRat (data j)) hdata p
  change _ = (nvfp4 outer block).reconstruct (fun j => (data j : ℝ)) p at h
  rw [← h]
  exact Rat.cast_eq_zero.symm

/-- The post's single-outlier tile on the executable quantizer: stored as one `16 × 16` block,
255 of the 256 stored values are zero. The count is the theorem `BlockExamples.nvfp4_tile_square` of
the real format, carried to the stored codes. -/
example :
    (Finset.univ.filter fun p : Fin 16 × Fin 16 =>
      ((nvfp4Stored (tiles 0 0) (tiles 16 16)).quantize (nvfp4Policy (tiles 0 0) (tiles 16 16))
        fun q => SignedRat.ofRat (if q = (0, 0) then 42 else 3 / 4)).value p = 0).card = 255 := by
  have hdata : (fun j : Fin 16 × Fin 16 => ((if j = (0, 0) then 42 else 3 / 4 : ℚ) : ℝ)) =
      BlockExamples.outlier (0, 0) := by
    funext j
    unfold BlockExamples.outlier
    split_ifs <;> norm_num
  rw [Finset.filter_congr fun p _ => stored_eq_zero_iff (tiles 0 0) (tiles 16 16) _
    (fun j => by split_ifs <;> norm_num) p, hdata]
  exact BlockExamples.nvfp4_tile_square

/-- The row-to-column flip on the executable quantizer: with `16 × 1` blocks, 221 of the 256
stored values of the row tile are zero (`BlockExamples.rowTile_col_blocks`). -/
example :
    (Finset.univ.filter fun p : Fin 16 × Fin 16 =>
      ((nvfp4Stored (tiles 0 0) (tiles 16 1)).quantize (nvfp4Policy (tiles 0 0) (tiles 16 1))
        fun q => SignedRat.ofRat
          (if q.1 = 0 then 42 else if q.1 = 1 ∨ (q.1 = 2 ∧ q.2.val < 3) then 3 else 3 / 4)).value
            p = 0).card = 221 := by
  have hdata : (fun j : Fin 16 × Fin 16 =>
      ((if j.1 = 0 then 42 else if j.1 = 1 ∨ (j.1 = 2 ∧ j.2.val < 3) then 3 else 3 / 4 : ℚ) : ℝ)) =
      BlockExamples.rowTile := by
    funext j
    unfold BlockExamples.rowTile
    split_ifs <;> norm_num
  rw [Finset.filter_congr fun p _ => stored_eq_zero_iff (tiles 0 0) (tiles 16 1) _
    (fun j => by split_ifs <;> norm_num) p, hdata]
  exact BlockExamples.rowTile_col_blocks

/-- Stored MXFP4 with the standard selection has the values of the real format `mx` with E2M1
elements, when the scale exponents do not exceed `127`. -/
example (x : Fin 4 × Fin 64 → SignedRat)
    (hrange : ∀ g, Int.log 2 (Selection.ofMax (tiles 1 32) (2 ^ (2 : ℤ)) 1
      (fun j => (x j).value) g) ≤ 127)
    (i : Fin 4 × Fin 64) :
    ((((Standard.format (tiles 1 32) .e2m1).quantize (Standard.policy (tiles 1 32) .e2m1)
        x).value i : ℚ) : ℝ) =
      (mx (Rounding.saturating .e2m1) 2 32).reconstruct (fun j => (((x j).value : ℚ) : ℝ)) i :=
  mx_value_eq_reconstruct .e2m1 32 x hrange i

/-- The combine format on the executable quantizer: with S2F6 elements in blocks of 32 and the
scale rounded up so that the block maximum maps to at most `127 / 64`, the stored values are those
of the real format `combine`, for every rational tensor. So the bound `a / 127` of the real
format holds for the stored values. -/
example (x : Fin 4 × Fin 64 → SignedRat) (i : Fin 4 × Fin 64)
    (ha : 0 < amax (tiles 1 32) (fun j => (((x j).value : ℚ) : ℝ)) (tiles 1 32 i))
    (hlo : -127 ≤ Int.clog 2 (amax (tiles 1 32) (fun j => (((x j).value : ℚ) : ℝ))
      (tiles 1 32 i) / (127 / 64 : ℝ)))
    (hhi : Int.clog 2 (amax (tiles 1 32) (fun j => (((x j).value : ℚ) : ℝ))
      (tiles 1 32 i) / (127 / 64 : ℝ)) ≤ 127) :
    |((((Standard.format (tiles 1 32) .int8).quantize (mxMaxCeil (tiles 1 32) (127 / 64))
        x).value i : ℚ) : ℝ) - (((x i).value : ℚ) : ℝ)| ≤
      amax (tiles 1 32) (fun j => (((x j).value : ℚ) : ℝ)) (tiles 1 32 i) / 127 := by
  have hstored := combine_value_eq_reconstruct 32 (127 / 64) x i
  have hcast : ((127 / 64 : ℚ) : ℝ) = 127 / 64 := by norm_num
  rw [hcast] at hstored
  rw [hstored]
  have hT : (2 : ℝ) ^ (((2 : ℕ) : ℤ) - 1) - (2 : ℝ) ^ (-((6 : ℕ) : ℤ)) = 127 / 64 := by norm_num
  have h := combine_abs_reconstruct_sub_le_of_ceil 2 6 32
    (fun j => (((x j).value : ℚ) : ℝ)) i (-127) 127 (by norm_num) ha
    (by rw [hT]; exact hlo) (by rw [hT]; exact hhi)
  rw [hT] at h
  refine h.trans (le_of_eq ?_)
  norm_num
  ring

/-- MXFP8 with E4M3 elements and the scale rounded up (`mxCeil`): the stored values are those of
the real format with the scale format `pow2Ceil`, for every rational tensor. -/
example (x : Fin 4 × Fin 64 → SignedRat) (i : Fin 4 × Fin 64) :
    ((((Standard.format (tiles 1 32) .e4m3).quantize (mxCeil (tiles 1 32) 8) x).value i : ℚ) :
        ℝ) =
      (Format.mk (fun _ => Rounding.saturating .e4m3)
        [Level.ofMax (tiles 1 32) (Rounding.pow2Ceil (-127) 127) (2 ^ (8 : ℤ)) 1]).reconstruct
          (fun j => (((x j).value : ℚ) : ℝ)) i := by
  have h := mxMaxCeil_value_eq_reconstruct .e4m3 32 (2 ^ (8 : ℤ)) x i
  have hcast : (((2 : ℚ) ^ (8 : ℤ) : ℚ) : ℝ) = 2 ^ (8 : ℤ) := by norm_num
  rw [hcast] at h
  exact h

/-- The same for every tensor of magnitudes below `2 ^ 128`, with E4M3 elements. -/
example (x : Fin 4 × Fin 64 → SignedRat) (hx : ∀ j, |(x j).value| < 2 ^ 128)
    (i : Fin 4 × Fin 64) :
    ((((Standard.format (tiles 1 32) .e4m3).quantize (Standard.policy (tiles 1 32) .e4m3)
        x).value i : ℚ) : ℝ) =
      (mx (Rounding.saturating .e4m3) 8 32).reconstruct (fun j => (((x j).value : ℚ) : ℝ)) i :=
  mx_value_eq_reconstruct_of_lt .e4m3 32 x hx i

end StoredCodes

/-! ## Axioms of the block theory -/

run_cmd do
  for name in [
      -- Scaled roundings and the format
      ``Rounding.Budget.scaled, ``Rounding.Budget.scaled_abs,
      ``Rounding.scaled_round_eq_zero_iff_mem, ``Rounding.abs_scaled_round_sub_le_of_nearest,
      ``Format.reconstruct_eq, ``Format.abs_reconstruct_sub_le,
      ``Format.abs_reconstruct_sub_le_abs, ``Format.abs_reconstruct_sub_le_of_bounds,
      ``Format.sum_abs_reconstruct_sub_le, ``Format.reconstruct_eq_zero_iff_mem,
      ``Format.reconstruct_eq_zero_iff_abs_le, ``Format.reconstruct_eq_zero_of_scale,
      -- Scale selection
      ``amax_le_iff, ``amax_eq_zero_iff, ``exists_abs_eq_amax, ``Level.ofMax_scale_of_eq_zero,
      ``Level.supplied_scale, ``ofMax_abs_div_scale_le, ``ofMax_le_amax_div_scale,
      ``selectedTarget_mem, ``ofCandidates_error_le, ``sum_measure_reconstruct_ofCandidates,
      ``Rounding.pow2Floor_fixes, ``Rounding.pow2Floor_round_eq,
      -- Bounds in terms of the block maximum
      ``Format.reconstruct_eq_self, ``Format.abs_reconstruct_sub_le_of_max,
      ``Format.reconstruct_eq_zero_of_abs_le, ``Format.abs_le_of_reconstruct_eq_zero,
      ``Format.reconstruct_eq_zero_iff_of_scale_eq, ``Format.reconstruct_eq_of_saturated,
      ``Format.reconstruct_eq_of_saturated_neg, ``total_append_ofMax,
      -- Transposition, dot products and accumulation
      ``Format.reconstruct_relabel, ``Level.transports_supplied, ``reconstruct_transpose,
      ``reconstruct_transpose_square, ``sum_decode_mul_decode, ``abs_foldl_round_sub_le,
      ``abs_accumulate_sub_le, ``abs_accumulateChunked_sub_le,
      -- Binary descriptors and fixed point
      ``roundingFunction_eq_zero_iff, ``roundAt_eq_zero_iff_mem,
      ``Rounding.saturating_round_eq_zero_iff_mem, ``Rounding.fixed_round_eq_zero_iff_mem,
      ``Rounding.saturating_budget, ``Rounding.ofFormat_budget,
      ``Rounding.ofFormat_round_eq_zero_iff, ``Rounding.saturating_fixes,
      ``Rounding.toReal_cast_eq_ofFormat, ``Rounding.fixed_budget,
      -- Named formats
      ``mx_scaled_max, ``e4m3_budget, ``e2m1_round_of_le_neg, ``nvfp4_scale,
      ``nvfp4_abs_scale_sub_le, ``nvfp4_abs_le_of_le_scale, ``nvfp4_reconstruct_max_of_scale_le,
      ``nvfp4_reconstruct_eq_zero_iff_of_fixes, ``combine_abs_reconstruct_sub_le,
      -- Kernel-checked instances
      ``BlockExamples.nvfp4_outlier, ``BlockExamples.mxfp4_outlier,
      ``BlockExamples.nvfp4_tile_row_blocks, ``BlockExamples.nvfp4_tile_square,
      ``BlockExamples.nvfp4_wide_row_blocks, ``BlockExamples.mxfp4_wide_row_blocks,
      ``BlockExamples.nvfp4_wide_square, ``BlockExamples.rowTile_col_blocks,
      ``BlockExamples.rowTile_row_blocks, ``BlockExamples.transpose_mismatch,
      ``BlockExamples.fourOverSix_not_optimal,
      -- Stored tensors
      ``CodedFormat.value_quantize, ``CodedFormat.elements_quantize, ``CodedLevel.toLevel_ofMax,
      ``CodedLevel.toLevel_supplied, ``Codec.int_rounding_round, ``Codec.exponent_rounding_round,
      ``Extended.sum_eq_infinity, ``Tensor.dotExact_eq_nan_of_scale,
      ``Tensor.dotExact_eq_nan_of_zero_infinity, ``Tensor.Dot_nil,
      ``Tensor.abs_toReal_Dot_sub_le, ``Tensor.sum_value_mul_value, ``sharedScale_value,
      ``ExecFloat.Block.Conversion.implements_run,
      -- OCP MX and P3109 as instances
      ``OCP.MX.E8M0.codec_rounding_eq_pow2Floor, ``OCP.MX.Standard.toFormat_format,
      ``OCP.MX.Standard.format_elements_quantize, ``OCP.MX.Standard.abs_value_quantize_sub_le,
      ``nvfp4Stored_abs_value_sub_le, ``nvfp4Stored_abs_scale_sub_le, ``Level.ofMax_scale_congr,
      ``OCP.MX.Standard.Profile.codec_budget, ``OCP.MX.Standard.Profile.codec_round_eq_zero_iff,
      ``OCP.MX.Standard.Profile.codec_round_eq_real,
      ``OCP.MX.Standard.Profile.value_quantize_eq_real,
      ``OCP.MX.Standard.Profile.codec_round_eq_of_nearest,
      ``OCP.MX.Standard.Profile.codec_round_midpoint,
      ``OCP.MX.Standard.Profile.midpointsAgree_eq_true, ``OCP.MX.Standard.Profile.codec_nearest,
      ``Rounding.Nearest.round_eq_left, ``Rounding.Nearest.round_eq_right,
      ``Rounding.Nearest.round_eq_of_ge, ``Rounding.Nearest.round_eq_of_le,
      ``Rounding.saturating_nearest, ``Rounding.saturating_round_neg,
      ``Rounding.saturating_round_ratCast, ``Rounding.RoundsTo.round_eq,
      ``Rounding.fixed_round_ratCast, ``Rounding.fixedRat_nearest,
      ``nvfp4Stored_value_eq_saturating, ``int8_value_eq_signedFixed,
      ``Format.reconstruct_ratCast, ``total_ratCast, ``amax_ratCast,
      ``Level.ofMax_scale_ratCast, ``log_two_ratCast, ``Rounding.pow2Floor_round_ratCast,
      ``Codec.ofFormat_round_eq_grid, ``Codec.cast_finiteValue_decodeModel,
      ``nvfp4Stored_value_eq_reconstruct, ``mx_value_eq_reconstruct, ``signedFixed_eq_real_int8,
      ``nvfp4Stored_value_eq_reconstruct_of_lt, ``mx_value_eq_reconstruct_of_lt,
      ``stored_eq_zero_iff, ``combine_value_eq_reconstruct, ``mxMaxCeil_value_eq_reconstruct,
      ``Level.ofMax_ideal_ratCast,
      ``clog_two_ratCast, ``Rounding.pow2Ceil_round_ratCast,
      ``OCP.MX.Standard.Tensor.decode_of_nan_scale, ``OCP.MX.Standard.Tensor.decode_finite,
      ``OCP.MX.Standard.Tensor.decode_infinity,
      ``P3109.Block.convertTo_lane, ``P3109.Block.decode_lane, ``P3109.Block.dotExact_eq] do
    let axioms ← Lean.collectAxioms name
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unexpected axiom {dependency}"

end FloatLibTests.Conformance.Formats.BlockTheory
