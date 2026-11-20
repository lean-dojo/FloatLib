/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Binary
public import FloatLib.Numerics.Quantization.Block.Bounds
public import FloatLib.Numerics.Quantization.Block.Transpose

/-!
# Block-scaled formats of ML accelerators

Each format here is one choice of the parameters of `Block.Format`, and its theorems are instances
of the general ones.

* `mx element emax k`: OCP MX 1.0. Blocks of `k` consecutive elements of a row, one power-of-two
  scale per block, selected by the rule of section 6.3: the block's largest magnitude lands in
  the binade of `2 ^ emax`, the element format's largest power of two. MXFP8, MXFP6, MXFP4 and
  MXINT8 are `mx` at their element format (`OCP.MX.Standard.Profile.format`).
* `twoLevel`: an element format with largest magnitude `M`, a block scale format with largest
  magnitude `N` and an outer scale format. The outer level stores `amax / (M * N)` and the block
  level stores `amax / M` of the data divided by the outer scale.
* `nvfp4 outer block`: NVFP4 (NVIDIA, "Pretraining Large Language Models with NVFP4",
  arXiv:2509.25149, section 2 and appendix B) is `twoLevel` with E2M1 elements (`M = 6`), E4M3
  block scales (`N = 448`) and a binary32 outer scale. `block` is `tiles 1 16` in the format and
  `tiles 16 16` in the two-dimensional variant of that report, and `outer` is `tiles 0 0` for a
  tensor and `tiles 1 0` for a row (an expert of a weight, a token of an activation).
* `fourOverSix measure outer`: Four Over Six (Cook et al., arXiv:2512.02010, section 3). The block
  level tries the targets `6` and `4` and keeps `4` only when its measured error is strictly
  smaller, and the outer scale uses `256` in place of `448`.
* `combine int frac k scale target`: signed fixed-point elements with `int` integer bits and
  `frac` fractional bits in blocks of `k` with a power-of-two scale. With `int = 2`, `frac = 6`
  and `k = 32` these are the S2F6 blocks with UE8M0 scales of Thinking Machines' combine step.
  The post does not state the scale selection, so `scale` and `target` are parameters, and it
  does not say whether the endpoint `-128/64` is used; the element format here includes it.

## Main results

* `mx_scale`, `mx_scaled_max`: the stored scale and the position of the block maximum,
  `2 ^ emax ≤ amax / scale < 2 ^ (emax + 1)`. A maximum above the largest element magnitude
  saturates.
* `twoLevel_scale`: the effective block scale is one rounding of `amax / M` in the block scale
  format scaled by the stored outer scale.
* `nvfp4_abs_scale_sub_le`: what storing the scale in E4M3 does. The effective block scale
  differs from `amax / 6` by at most `amax / 96 + o / 1024 + max 0 (amax / 6 - 448 * o)`, with
  `o` the stored outer scale.
* `nvfp4_abs_le_of_le_scale`: if the stored scale is not below `amax / 6`, no element of the
  block saturates.
* `nvfp4_reconstruct_max_of_scale_le`: if it is below, the block maximum saturates and is
  reconstructed as `6` times the stored scale, with error `amax - 6 * scale`.
* `nvfp4_reconstruct_eq_zero_iff`: an element is flushed to zero exactly when its magnitude is at
  most a quarter of its effective block scale, which is `amax / 24` for an exact scale.
* `e2m1_budget`, `e4m3_budget`, `e2m1_round_eq_zero_iff`: the constants of the two formats.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Floats.Formats.BinaryInterchange.Model

variable {ι γ K : Type*}

section Generic

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/--
OCP MX: blocks of `k` consecutive elements of a row, with one power-of-two scale per block that
puts the block's largest magnitude in the binade of `2 ^ emax`. An all-zero block gets the
scale `2 ^ 0`.

Reference: OCP Microscaling Formats (MX) Specification v1.0, §§6.3.
-/
@[reducible] def mx [FloorRing K] {m n : ℕ} (element : Rounding K) (emax : ℤ) (k : ℕ := 32) :
    Format (Fin m × Fin n) (ℕ × ℕ) K where
  element _ := element
  levels := [Level.ofMax (tiles 1 k) (Rounding.pow2Floor (-127) 127) (2 ^ emax) 1]

/--
Two-level scaling: the outer level maps the largest magnitude of each outer group to `M * N`, and
the block level maps the largest magnitude of each block, after division by the outer scale, to
`M`. `M` and `N` are the largest magnitudes of the element format and of the block scale format.
-/
@[reducible] def twoLevel [Fintype ι] [DecidableEq γ]
    (element blockScale outerScale : Rounding K) (M N : K) (block outer : ι → γ) :
    Format ι γ K where
  element _ := element
  levels := [Level.ofMax outer outerScale (M * N) 1, Level.ofMax block blockScale M 0]

/-- The scale `mx` stores for a block that is not all zero. -/
theorem mx_scale [FloorRing K] {m n : ℕ} (element : Rounding K) (emax : ℤ) (k : ℕ)
    (x : Fin m × Fin n → K) (i : Fin m × Fin n) (ha : 0 < amax (tiles 1 k) x (tiles 1 k i)) :
    (mx element emax k).scale x i =
      (Rounding.pow2Floor (-127) 127).round (amax (tiles 1 k) x (tiles 1 k i) / 2 ^ emax) :=
  total_ofMax _ _ _ _ x i ha

/--
OCP MX places the largest magnitude of a block in the binade of `2 ^ emax`:
`2 ^ emax ≤ amax / scale < 2 ^ (emax + 1)`, when the selected exponent is inside E8M0's range.
A scaled maximum above the element format's largest magnitude saturates.

Reference: OCP Microscaling Formats (MX) Specification v1.0, §§6.3.
-/
theorem mx_scaled_max [FloorRing K] {m n : ℕ} (element : Rounding K) (emax : ℤ) (k : ℕ)
    (x : Fin m × Fin n → K) (i : Fin m × Fin n) (ha : 0 < amax (tiles 1 k) x (tiles 1 k i))
    (hlo : -127 ≤ Int.log 2 (amax (tiles 1 k) x (tiles 1 k i) / (2 : K) ^ emax))
    (hhi : Int.log 2 (amax (tiles 1 k) x (tiles 1 k i) / (2 : K) ^ emax) ≤ 127) :
    (2 : K) ^ emax ≤ amax (tiles 1 k) x (tiles 1 k i) / (mx element emax k).scale x i ∧
      amax (tiles 1 k) x (tiles 1 k i) / (mx element emax k).scale x i < 2 ^ (emax + 1) := by
  have ht : (0 : K) < 2 ^ emax := zpow_pos (two_pos) _
  have hideal : 0 < amax (tiles 1 k) x (tiles 1 k i) / (2 : K) ^ emax := div_pos ha ht
  have hs := Rounding.pow2Floor_pos (K := K) (-127) 127
    (amax (tiles 1 k) x (tiles 1 k i) / 2 ^ emax)
  have h1 := Rounding.pow2Floor_le hideal hlo hhi
  have h2 := Rounding.lt_two_mul_pow2Floor (K := K) hlo hhi
  rw [mx_scale element emax k x i ha]
  constructor
  · rw [le_div_iff₀ hs]
    calc (2 : K) ^ emax * _ ≤ 2 ^ emax * (amax (tiles 1 k) x (tiles 1 k i) / 2 ^ emax) :=
          mul_le_mul_of_nonneg_left h1 ht.le
      _ = amax (tiles 1 k) x (tiles 1 k i) := by field_simp
  · rw [div_lt_iff₀ hs, zpow_add_one₀ (two_ne_zero)]
    have h3 := mul_lt_mul_of_pos_left h2 ht
    have h4 : (2 : K) ^ emax * (amax (tiles 1 k) x (tiles 1 k i) / 2 ^ emax) =
        amax (tiles 1 k) x (tiles 1 k i) := by field_simp
    rw [h4] at h3
    linarith

/-- Every scale `mx` stores is positive: it is a power of two. -/
theorem mx_scale_pos [FloorRing K] {m n : ℕ} (element : Rounding K) (emax : ℤ) (k : ℕ)
    (x : Fin m × Fin n → K) (i : Fin m × Fin n) : 0 < (mx element emax k).scale x i :=
  total_pos_of_format _ (Rounding.pow2Floor_pos (-127) 127) x i

/-- Error of one element of `mx`, for every element format with a budget and every input: the
relative error of the element format, its absolute error times the block scale, and the loss of
saturating at `M` times the block scale. There is no premise on the data. -/
theorem mx_abs_reconstruct_sub_le [FloorRing K] {m n : ℕ} (element : Rounding K) (emax : ℤ)
    (k : ℕ) (x : Fin m × Fin n → K) (i : Fin m × Fin n) {u η M : K}
    (hE : element.Budget u η M) :
    |(mx element emax k).reconstruct x i - x i| ≤
      u * |x i| + (mx element emax k).scale x i * η +
        max 0 (|x i| - (mx element emax k).scale x i * M) :=
  (mx element emax k).abs_reconstruct_sub_le x i hE (mx_scale_pos element emax k x i)

/--
Effective block scale under two-level scaling. If every block lies in one outer group and the
stored outer scale `o` of the block's group is positive, the total scale of a block that is not
all zero is one rounding of `amax / M` in the block scale format scaled by `o`.
-/
theorem twoLevel_scale [Fintype ι] [DecidableEq γ] (element blockScale outerScale : Rounding K)
    (M N : K) (block outer : ι → γ) (x : ι → K) (i : ι)
    (hnest : ∀ j, block j = block i → outer j = outer i) (ha : 0 < amax block x (block i))
    (ho : 0 < (Level.ofMax outer outerScale (M * N) 1).scaleAt x i) :
    (twoLevel element blockScale outerScale M N block outer).scale x i =
      (blockScale.scaled ((Level.ofMax outer outerScale (M * N) 1).scaleAt x i)).round
        (amax block x (block i) / M) := by
  refine total_append_ofMax [Level.ofMax outer outerScale (M * N) 1] block blockScale M 0 x i
    ho (fun j hj => ?_) ha
  rw [total_singleton]
  simp only [Level.scaleAt, show (Level.ofMax outer outerScale (M * N) 1).group j = outer j
    from rfl, show (Level.ofMax outer outerScale (M * N) 1).group i = outer i from rfl,
    hnest j hj]

end Generic

/-! ## Constants of E2M1 and E4M3 -/

/-- E2M1 with saturation: relative error `1/4`, absolute error `1/4`, largest magnitude `6`. -/
theorem e2m1_budget : (Rounding.saturating .e2m1).Budget (1 / 4) (1 / 4) 6 := by
  have h := Rounding.saturating_budget_of_eq .e2m1 (p := 2) (k := 3) (e := -2) (q := 1)
    (by decide) (by decide) (by decide) (by decide)
  norm_num at h
  exact h

/-- E4M3 with saturation: relative error `1/16`, absolute error `1/1024`, largest magnitude
`448`. -/
theorem e4m3_budget : (Rounding.saturating .e4m3).Budget (1 / 16) (1 / 1024) 448 := by
  have h := Rounding.saturating_budget_of_eq .e4m3 (p := 4) (k := 14) (e := -10) (q := 5)
    (by decide) (by decide) (by decide) (by decide)
  norm_num at h
  exact h

/-- E2M1 stores exactly the magnitudes up to `1/4` as zero: the tie between `0` and `1/2` goes
to zero. -/
theorem e2m1_round_eq_zero_iff (x : ℝ) : (Rounding.saturating .e2m1).round x = 0 ↔ |x| ≤ 1 / 4 := by
  have h := Rounding.saturating_round_eq_zero_iff_of_eq .e2m1 (e := -2) (by decide) x
  norm_num at h
  exact h

/-- E2M1 in every rounding direction stores `y` as zero exactly when `2 * y` lies in
`modeZeroSet mode`: its least subnormal is one half. -/
theorem e2m1_round_eq_zero_iff_mem (mode : IEEERoundingMode) (y : ℝ) :
    (Rounding.saturating .e2m1 mode).round y = 0 ↔ 2 * y ∈ modeZeroSet mode := by
  have h := Rounding.saturating_round_eq_zero_iff_mem_of_eq .e2m1 mode (e := -1) (by decide) y
  rwa [show y / (2 : ℝ) ^ (-1 : ℤ) = 2 * y by norm_num; ring] at h

/-- E2M1 stores everything from `6` up as `6`. -/
theorem e2m1_round_of_le {x : ℝ} (hx : 6 ≤ x) : (Rounding.saturating .e2m1).round x = 6 := by
  have h := Rounding.saturating_round_of_le_of_eq .e2m1 (k := 3) (q := 1) (by decide) (by decide)
    (x := x) (by norm_num; exact hx)
  norm_num at h
  exact h

/-- The largest finite E2M1 value is 6. -/
theorem toReal_posMaxFinite_e2m1 : toReal (posMaxFinite .e2m1) = 6 := by
  have h := toReal_posMaxFinite_of_eq .e2m1 (significand := 3) (exponent := 1) (by decide)
    (by decide)
  norm_num at h
  exact h

/-- The largest finite E4M3 value is 448. -/
theorem toReal_posMaxFinite_e4m3 : toReal (posMaxFinite .e4m3) = 448 := by
  have h := toReal_posMaxFinite_of_eq .e4m3 (significand := 14) (exponent := 5) (by decide)
    (by decide)
  norm_num at h
  exact h

/-- E2M1 stores everything from `-6` down as `-6`. -/
theorem e2m1_round_of_le_neg {x : ℝ} (hx : x ≤ -6) : (Rounding.saturating .e2m1).round x = -6 := by
  have h := Rounding.saturating_round_of_le_neg (fmt := .e2m1) (x := x)
    (by rw [toReal_posMaxFinite_e2m1]; exact hx)
  rwa [toReal_posMaxFinite_e2m1] at h

/-! ## Flush to zero by rounding direction -/

/--
Flush to zero in every rounding direction, for an element that saturates a binary descriptor: the
element is reconstructed as zero exactly when its input, in units of the least subnormal times
its total scale, lies in `modeZeroSet mode`. This holds for every level structure and selection
rule.
-/
theorem Format.reconstruct_eq_zero_iff_of_mode {ι γ : Type*} (F : Format ι γ ℝ) (x : ι → ℝ)
    (i : ι) {fmt : FloatFormat} {mode : IEEERoundingMode}
    (hE : F.element i = Rounding.saturating fmt mode) (hσ : F.scale x i ≠ 0) :
    F.reconstruct x i = 0 ↔
      x i / F.scale x i / (2 * underflowErrorAt fmt) ∈ modeZeroSet mode :=
  F.reconstruct_eq_zero_iff_mem x i
    (Z := {y | y / (2 * underflowErrorAt fmt) ∈ modeZeroSet mode})
    (fun y => by rw [hE]; exact Rounding.saturating_round_eq_zero_iff_mem fmt mode y) hσ

/--
Flush to zero of E2M1 elements in every rounding direction: with total scale `σ`, the element is
reconstructed as zero exactly when `2 * (x / σ)` lies in `modeZeroSet mode`. For a positive `σ`
this is `|x| ≤ σ / 4` for ties to even, `|x| < σ / 4` for ties away, `|x| < σ / 2` toward zero,
`-σ / 2 < x ≤ 0` upward, `0 ≤ x < σ / 2` downward, and `x = 0` away from zero.
-/
theorem Format.e2m1_reconstruct_eq_zero_iff {ι γ : Type*} (F : Format ι γ ℝ) (x : ι → ℝ) (i : ι)
    {mode : IEEERoundingMode} (hE : F.element i = Rounding.saturating .e2m1 mode)
    (hσ : F.scale x i ≠ 0) :
    F.reconstruct x i = 0 ↔ 2 * (x i / F.scale x i) ∈ modeZeroSet mode :=
  F.reconstruct_eq_zero_iff_mem x i (Z := {y | 2 * y ∈ modeZeroSet mode})
    (fun y => by rw [hE]; exact e2m1_round_eq_zero_iff_mem mode y) hσ

/-! ## NVFP4, Four Over Six and the combine format -/

/--
NVFP4: E2M1 elements, one E4M3 scale per block of `block`, and one binary32 scale per group of
`outer`. The format's shape is `block = tiles 1 16`.
-/
@[reducible] noncomputable def nvfp4 {m n : ℕ} (outer : Fin m × Fin n → ℕ × ℕ := tiles 0 0)
    (block : Fin m × Fin n → ℕ × ℕ := tiles 1 16) : Format (Fin m × Fin n) (ℕ × ℕ) ℝ :=
  twoLevel (Rounding.saturating .e2m1) (Rounding.saturating .e4m3) (Rounding.grid .binary32)
    6 448 block outer

/--
Four Over Six: NVFP4 whose block level keeps, for each block, the target `4` when its measured
error is strictly smaller than that of the target `6`, and whose outer scale maps the largest
magnitude to `6 * 256`.
-/
@[reducible] noncomputable def fourOverSix {m n : ℕ} (measure : ℝ → ℝ)
    (outer : Fin m × Fin n → ℕ × ℕ := tiles 0 0) (block : Fin m × Fin n → ℕ × ℕ := tiles 1 16) :
    Format (Fin m × Fin n) (ℕ × ℕ) ℝ where
  element _ := Rounding.saturating .e2m1
  levels :=
    [Level.ofMax outer (Rounding.grid .binary32) (6 * 256) 1,
      Level.ofCandidates block (Rounding.saturating .e4m3)
        (fun _ => Rounding.saturating .e2m1) measure [6, 4] 0]

/-- Signed two's-complement fixed point with `int` integer bits, the sign included, and `frac`
fractional bits: the multiples of `2 ^ (-frac)` from `-2 ^ (int - 1)` to
`2 ^ (int - 1) - 2 ^ (-frac)`. -/
noncomputable def Rounding.signedFixed (int frac : ℕ) : Rounding ℝ :=
  Rounding.fixed frac (-(2 : ℝ) ^ ((int : ℤ) - 1))
    ((2 : ℝ) ^ ((int : ℤ) - 1) - (2 : ℝ) ^ (-(frac : ℤ)))

/--
The combine format: blocks of `k` signed fixed-point elements with one scale per block, stored by
`scale` and selected so that the block's largest magnitude maps to `target`.
`combine 2 6 32 (Rounding.pow2Ceil (-127) 127) (127 / 64)` is S2F6 in blocks of 32 with a
power-of-two scale that has the exponent range of E8M0, the scale rounded up so that no element
saturates.

Thinking Machines' description (2026-11-13) fixes the element format (S2F6, from `-128 / 64` to
`127 / 64`), the block size 32 and the scale format (UE8M0, in the conversion instructions it
quotes). It does not state how the scale of a block is selected, the rounding direction of the
element conversion (the instruction's modifier `frnd2` is not defined there), or the exponent
range of UE8M0. These are the parameters `scale` and `target`, and the element rounding here is
to nearest with ties to even. The random Hadamard transform applied before quantization is not
part of the format.
-/
@[reducible] noncomputable def combine {m n : ℕ} (int frac : ℕ) (k : ℕ) (scale : Rounding ℝ)
    (target : ℝ) : Format (Fin m × Fin n) (ℕ × ℕ) ℝ where
  element _ := Rounding.signedFixed int frac
  levels := [Level.ofMax (tiles 1 k) scale target 1]

section Combine

variable (int frac : ℕ)

/-- Signed fixed point has no relative error, absolute error half a step, and saturates at its
largest value `2 ^ (int - 1) - 2 ^ (-frac)`. -/
theorem signedFixed_budget :
    (Rounding.signedFixed int frac).Budget 0 ((2 : ℝ) ^ (-(frac : ℤ) - 1))
      ((2 : ℝ) ^ ((int : ℤ) - 1) - (2 : ℝ) ^ (-(frac : ℤ))) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(frac : ℤ)) := zpow_pos (two_pos) _
  have h := Rounding.fixed_budget (frac : ℤ) (lo := -(2 : ℝ) ^ ((int : ℤ) - 1))
    (hi := (2 : ℝ) ^ ((int : ℤ) - 1) - (2 : ℝ) ^ (-(frac : ℤ)))
  exact h.mono le_rfl le_rfl (le_min (by linarith) le_rfl)

/-- Error of one element of the combine format, for every scale format and target: half a step
of the fixed-point format times the block scale, and the loss of saturating at the largest
element value times the block scale. -/
theorem combine_abs_reconstruct_sub_le {m n : ℕ} (k : ℕ) (scale : Rounding ℝ) (target : ℝ)
    (x : Fin m × Fin n → ℝ) (i : Fin m × Fin n)
    (hσ : 0 < (combine int frac k scale target).scale x i) :
    |(combine int frac k scale target).reconstruct x i - x i| ≤
      (combine int frac k scale target).scale x i * (2 : ℝ) ^ (-(frac : ℤ) - 1) +
        max 0 (|x i| - (combine int frac k scale target).scale x i *
          ((2 : ℝ) ^ ((int : ℤ) - 1) - (2 : ℝ) ^ (-(frac : ℤ)))) := by
  simpa using (combine int frac k scale target).abs_reconstruct_sub_le x i
    (signedFixed_budget int frac) hσ

variable [NeZero int]

/-- The largest value of signed fixed point with at least one integer bit is nonnegative, and
positive when the format has at least two bits. -/
private theorem signedFixed_bounds :
    (1 : ℝ) ≤ (2 : ℝ) ^ ((int : ℤ) - 1) ∧ (2 : ℝ) ^ (-(frac : ℤ)) ≤ 1 ∧
      (2 ≤ int + frac → (2 : ℝ) ^ (-(frac : ℤ)) < (2 : ℝ) ^ ((int : ℤ) - 1)) := by
  have hint : 1 ≤ int := NeZero.one_le
  refine ⟨one_le_zpow₀ (by norm_num) (by omega), zpow_le_one_of_nonpos₀ (by norm_num) (by omega),
    fun h => zpow_lt_zpow_right₀ (one_lt_two) (by omega)⟩

/-- Signed fixed point with at least two bits stores exactly the magnitudes up to half a step as
zero. -/
theorem signedFixed_round_eq_zero_iff (hbits : 2 ≤ int + frac) (y : ℝ) :
    (Rounding.signedFixed int frac).round y = 0 ↔ |y| ≤ (2 : ℝ) ^ (-(frac : ℤ) - 1) := by
  obtain ⟨h1, -, h3⟩ := signedFixed_bounds int frac
  exact Rounding.fixed_round_eq_zero_iff (frac : ℤ) (by linarith) (by linarith [h3 hbits]) y

variable {m n : ℕ} (k : ℕ) (scale : Rounding ℝ) (target : ℝ) (x : Fin m × Fin n → ℝ)
  (i : Fin m × Fin n)

/-- Flush to zero in the combine format: an element is reconstructed as zero exactly when its
magnitude is at most half a step of the fixed-point format times the block scale. -/
theorem combine_reconstruct_eq_zero_iff (hbits : 2 ≤ int + frac)
    (hσ : 0 < (combine int frac k scale target).scale x i) :
    (combine int frac k scale target).reconstruct x i = 0 ↔
      |x i| ≤ (2 : ℝ) ^ (-(frac : ℤ) - 1) * (combine int frac k scale target).scale x i :=
  (combine int frac k scale target).reconstruct_eq_zero_iff_abs_le x i
    (signedFixed_round_eq_zero_iff int frac hbits) hσ

/-- Flush to zero in the combine format with a power-of-two scale rounded up: the scale is
positive for every input, so there is no premise on the data. -/
theorem combine_reconstruct_eq_zero_iff_of_ceil (lo hi : ℤ) (hbits : 2 ≤ int + frac) :
    (combine int frac k (Rounding.pow2Ceil lo hi) target).reconstruct x i = 0 ↔
      |x i| ≤ (2 : ℝ) ^ (-(frac : ℤ) - 1) *
        (combine int frac k (Rounding.pow2Ceil lo hi) target).scale x i :=
  combine_reconstruct_eq_zero_iff int frac k _ target x i hbits
    (total_pos_of_format _ (Rounding.pow2Ceil_pos lo hi) x i)

/--
The combine format with the scale rounded up to a power of two and the largest element value
`T = 2 ^ (int - 1) - 2 ^ (-frac)` as target: no element saturates, and the error of each element
is at most `2 ^ (-frac) * (a / T)`, with `a` the largest magnitude of its block, when the
exponent of `a / T` is inside the range of the scale format. For S2F6 this is `a / 127`.
-/
theorem combine_abs_reconstruct_sub_le_of_ceil (lo hi : ℤ) (hbits : 2 ≤ int + frac)
    (ha : 0 < amax (tiles 1 k) x (tiles 1 k i))
    (hlo : lo ≤ Int.clog 2 (amax (tiles 1 k) x (tiles 1 k i) /
      ((2 : ℝ) ^ ((int : ℤ) - 1) - (2 : ℝ) ^ (-(frac : ℤ)))))
    (hhi : Int.clog 2 (amax (tiles 1 k) x (tiles 1 k i) /
      ((2 : ℝ) ^ ((int : ℤ) - 1) - (2 : ℝ) ^ (-(frac : ℤ)))) ≤ hi) :
    |(combine int frac k (Rounding.pow2Ceil lo hi)
        ((2 : ℝ) ^ ((int : ℤ) - 1) - (2 : ℝ) ^ (-(frac : ℤ)))).reconstruct x i - x i| ≤
      (2 : ℝ) ^ (-(frac : ℤ)) * (amax (tiles 1 k) x (tiles 1 k i) /
        ((2 : ℝ) ^ ((int : ℤ) - 1) - (2 : ℝ) ^ (-(frac : ℤ)))) := by
  obtain ⟨-, -, h3⟩ := signedFixed_bounds int frac
  have hT : (0 : ℝ) < (2 : ℝ) ^ ((int : ℤ) - 1) - (2 : ℝ) ^ (-(frac : ℤ)) := by
    exact sub_pos.mpr (h3 hbits)
  set T := (2 : ℝ) ^ ((int : ℤ) - 1) - (2 : ℝ) ^ (-(frac : ℤ))
  set a := amax (tiles 1 k) x (tiles 1 k i)
  have hscale : (combine int frac k (Rounding.pow2Ceil lo hi) T).scale x i =
      (Rounding.pow2Ceil lo hi).round (a / T) := total_ofMax _ _ _ _ x i ha
  have h := (combine int frac k (Rounding.pow2Ceil lo hi) T).abs_reconstruct_sub_le_of_max x i
    (a := a) (t := T) (c₁ := 1) (c₂ := 2) (signedFixed_budget int frac)
    (zpow_pos (two_pos) _).le ha hT one_pos (abs_le_amax (tiles 1 k) x i)
    (by rw [hscale, one_mul]; exact Rounding.le_pow2Ceil hlo hhi)
    (by rw [hscale]; exact (Rounding.pow2Ceil_lt_two_mul (div_pos ha hT) hlo hhi).le)
    (by rw [div_one])
  have hpow : (2 : ℝ) * (a / T) * (2 : ℝ) ^ (-(frac : ℤ) - 1) =
      (2 : ℝ) ^ (-(frac : ℤ)) * (a / T) := by
    rw [zpow_sub_one₀ (two_ne_zero (α := ℝ))]
    ring
  rw [zero_mul, zero_add, hpow] at h
  exact h

end Combine

section NVFP4

variable {m n : ℕ} (outer block : Fin m × Fin n → ℕ × ℕ) (x : Fin m × Fin n → ℝ)
  (i : Fin m × Fin n)

/-- The outer scale NVFP4 stores for the group of an element. -/
noncomputable def nvfp4Outer : ℝ :=
  (Level.ofMax outer (Rounding.grid .binary32) (6 * 448) 1).scaleAt x i

/-- The effective block scale of NVFP4 is one rounding of `amax / 6` in E4M3 scaled by the stored
outer scale. -/
theorem nvfp4_scale (hnest : ∀ j, block j = block i → outer j = outer i)
    (ha : 0 < amax block x (block i)) (ho : 0 < nvfp4Outer outer x i) :
    (nvfp4 outer block).scale x i =
      ((Rounding.saturating .e4m3).scaled (nvfp4Outer outer x i)).round
        (amax block x (block i) / 6) :=
  twoLevel_scale _ _ _ 6 448 block outer x i hnest ha ho

/--
What storing the block scale in E4M3 does: the effective block scale differs from the ideal scale
`amax / 6` by at most a sixteenth of it, plus `o / 1024` in E4M3's subnormal range, plus the
excess of the ideal scale over `448 * o`, where `o` is the stored outer scale.
-/
theorem nvfp4_abs_scale_sub_le (hnest : ∀ j, block j = block i → outer j = outer i)
    (ha : 0 < amax block x (block i)) (ho : 0 < nvfp4Outer outer x i) :
    |(nvfp4 outer block).scale x i - amax block x (block i) / 6| ≤
      1 / 16 * (amax block x (block i) / 6) + nvfp4Outer outer x i * (1 / 1024) +
        max 0 (amax block x (block i) / 6 - nvfp4Outer outer x i * 448) := by
  rw [nvfp4_scale outer block x i hnest ha ho]
  have h := (e4m3_budget.scaled ho) (amax block x (block i) / 6)
  rwa [abs_of_nonneg (div_nonneg (amax_nonneg block x (block i)) (Nat.ofNat_nonneg' 6))] at h

/-- Error of one NVFP4 element: a quarter of its magnitude, a quarter of its effective block
scale, and its excess over six times that scale. -/
theorem nvfp4_abs_reconstruct_sub_le (hσ : 0 < (nvfp4 outer block).scale x i) :
    |(nvfp4 outer block).reconstruct x i - x i| ≤
      1 / 4 * |x i| + (nvfp4 outer block).scale x i * (1 / 4) +
        max 0 (|x i| - (nvfp4 outer block).scale x i * 6) :=
  (nvfp4 outer block).abs_reconstruct_sub_le x i e2m1_budget hσ

/--
Error of one NVFP4 element in terms of the largest magnitude `a` of its block. If the effective
block scale is within a relative `ε < 1` of the ideal scale `a / 6`, the error is at most
`|x| / 4 + (1 + ε) * (a / 24) + ε * a`: the last term is the saturation of elements near the
maximum when the scale is rounded down. With E4M3's `ε = 1 / 16` in its normal range this is
`|x| / 4 + 41 / 384 * a`.
-/
theorem nvfp4_abs_reconstruct_sub_le_of_scale {ε : ℝ} (hε : ε < 1)
    (ha : 0 < amax block x (block i))
    (hs : |(nvfp4 outer block).scale x i - amax block x (block i) / 6| ≤
      ε * (amax block x (block i) / 6)) :
    |(nvfp4 outer block).reconstruct x i - x i| ≤
      1 / 4 * |x i| + (1 + ε) * (amax block x (block i) / 24) +
        ε * amax block x (block i) := by
  obtain ⟨hlo, hhi⟩ := scale_bounds_of_relative hs
  have hideal : 0 < amax block x (block i) / 6 := div_pos ha (Nat.ofNat_pos)
  have hσ : 0 < (nvfp4 outer block).scale x i :=
    (mul_pos (by linarith) hideal).trans_le hlo
  have h := nvfp4_abs_reconstruct_sub_le outer block x i hσ
  have hx := abs_le_amax block x i
  have hε0 : 0 ≤ ε := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans hs) hideal
  have hsat : max 0 (|x i| - (nvfp4 outer block).scale x i * 6) ≤
      ε * amax block x (block i) :=
    max_le (mul_nonneg hε0 ha.le) (by linarith)
  linarith

/-- If the stored block scale is not below the ideal scale `amax / 6`, no element of the block
exceeds the E2M1 range: every element is at most `6` times its scale. -/
theorem nvfp4_abs_le_of_le_scale (ha : 0 < amax block x (block i))
    (hs : amax block x (block i) / 6 ≤ (nvfp4 outer block).scale x i) :
    |x i| ≤ (nvfp4 outer block).scale x i * 6 := by
  have hσ : 0 < (nvfp4 outer block).scale x i := (div_pos ha (Nat.ofNat_pos)).trans_le hs
  have h := abs_div_scale_le (c := 1) ha (Nat.ofNat_pos : (0 : ℝ) < 6) one_pos
    (by simpa using hs) (abs_le_amax block x i)
  rw [abs_div, abs_of_pos hσ, div_le_iff₀ hσ] at h
  simpa only [mul_comm, one_mul, div_one] using h

/--
If the stored block scale is below the ideal scale, the positive block maximum saturates: it is
reconstructed as `6` times the stored scale, short of its value by `amax - 6 * scale`.
-/
theorem nvfp4_reconstruct_max_of_scale_le (hσ : 0 < (nvfp4 outer block).scale x i)
    (hmax : x i = amax block x (block i))
    (hs : (nvfp4 outer block).scale x i ≤ amax block x (block i) / 6) :
    (nvfp4 outer block).reconstruct x i = 6 * (nvfp4 outer block).scale x i :=
  Format.reconstruct_eq_of_saturated _ x i (fun _ hy => e2m1_round_of_le hy) hσ
    (by rw [hmax]; simpa only [mul_comm] using (le_div_iff₀ (Nat.ofNat_pos)).mp hs)

/--
Flush to zero in NVFP4: an element is reconstructed as zero exactly when its magnitude is at most
a quarter of its effective block scale. The tie at a quarter goes to zero.
-/
theorem nvfp4_reconstruct_eq_zero_iff (hσ : 0 < (nvfp4 outer block).scale x i) :
    (nvfp4 outer block).reconstruct x i = 0 ↔ |x i| ≤ 1 / 4 * (nvfp4 outer block).scale x i :=
  Format.reconstruct_eq_zero_iff_abs_le _ x i (fun y => e2m1_round_eq_zero_iff y) hσ

/-- With an exact block scale `amax / 6`, NVFP4 flushes exactly the elements of magnitude at most
`amax / 24`. -/
theorem nvfp4_reconstruct_eq_zero_iff_of_exact (ha : 0 < amax block x (block i))
    (hs : (nvfp4 outer block).scale x i = amax block x (block i) / 6) :
    (nvfp4 outer block).reconstruct x i = 0 ↔ |x i| ≤ amax block x (block i) / 24 := by
  rw [nvfp4_reconstruct_eq_zero_iff outer block x i (hs ▸ div_pos ha (Nat.ofNat_pos)), hs]
  rw [one_div_mul_eq_div, div_div]
  norm_num

/--
An exact NVFP4 block scale: when binary32 stores the ideal outer scale and E4M3 stores the ideal
block scale in units of the outer scale, the effective block scale is `amax / 6`.
-/
theorem nvfp4_scale_of_fixes (hnest : ∀ j, block j = block i → outer j = outer i)
    (ha : 0 < amax block x (block i)) (haT : 0 < amax outer x (outer i))
    (ho : (Rounding.grid .binary32).Fixes (amax outer x (outer i) / (6 * 448)))
    (hb : (Rounding.saturating .e4m3).Fixes
      (amax block x (block i) / 6 / (amax outer x (outer i) / (6 * 448)))) :
    (nvfp4 outer block).scale x i = amax block x (block i) / 6 := by
  have hoEq : nvfp4Outer outer x i = amax outer x (outer i) / (6 * 448) := by
    rw [nvfp4Outer, Level.scaleAt,
      show (Level.ofMax outer (Rounding.grid .binary32) (6 * 448) 1).group i = outer i from rfl,
      Level.ofMax_scale haT]
    exact ho
  have hpos : 0 < amax outer x (outer i) / (6 * 448) := div_pos haT (by norm_num)
  rw [nvfp4_scale outer block x i hnest ha (hoEq ▸ hpos), Rounding.scaled_round, hoEq, hb,
    div_mul_cancel₀ _ hpos.ne']

/-- With exact scales, NVFP4 flushes exactly the elements of magnitude at most `amax / 24`. -/
theorem nvfp4_reconstruct_eq_zero_iff_of_fixes
    (hnest : ∀ j, block j = block i → outer j = outer i)
    (ha : 0 < amax block x (block i)) (haT : 0 < amax outer x (outer i))
    (ho : (Rounding.grid .binary32).Fixes (amax outer x (outer i) / (6 * 448)))
    (hb : (Rounding.saturating .e4m3).Fixes
      (amax block x (block i) / 6 / (amax outer x (outer i) / (6 * 448)))) :
    (nvfp4 outer block).reconstruct x i = 0 ↔ |x i| ≤ amax block x (block i) / 24 :=
  nvfp4_reconstruct_eq_zero_iff_of_exact outer block x i ha
    (nvfp4_scale_of_fixes outer block x i hnest ha haT ho hb)

end NVFP4

/--
Quantizing the transpose in NVFP4 with `l × k` blocks is the transpose of quantizing with `k × l`
blocks, with one outer scale for the tensor. So `1 × 16` blocks on the transpose are `16 × 1`
blocks on the matrix, and only square tiles give the forward and the backward pass the same
decoded weight.
-/
theorem nvfp4_reconstruct_transpose {m n : ℕ} (k l : ℕ) (x : Fin m × Fin n → ℝ) (i : Fin n)
    (j : Fin m) :
    (nvfp4 (tiles 0 0) (tiles l k)).reconstruct (fun p => x (p.2, p.1)) (i, j) =
      (nvfp4 (tiles 0 0) (tiles k l)).reconstruct x (j, i) :=
  Format.reconstruct_relabel (π := Equiv.prodComm (Fin n) (Fin m))
    (F' := nvfp4 (tiles 0 0) (tiles l k)) (F := nvfp4 (tiles 0 0) (tiles k l)) (fun _ => rfl)
    (List.Forall₂.cons
      (Level.transports_ofMax (Equiv.prodComm (Fin n) (Fin m)) Prod.swap Prod.swap_injective
        (tiles_swap 0 0) _ _ _)
      (List.Forall₂.cons
        (Level.transports_ofMax (Equiv.prodComm (Fin n) (Fin m)) Prod.swap Prod.swap_injective
          (tiles_swap k l) _ _ _) List.Forall₂.nil)) x (i, j)

/--
Four Over Six commutes with transposition in the same way: quantizing the transpose with `l × k`
blocks is the transpose of quantizing with `k × l` blocks, for every error measure.
-/
theorem fourOverSix_reconstruct_transpose {m n : ℕ} (measure : ℝ → ℝ) (k l : ℕ)
    (x : Fin m × Fin n → ℝ) (i : Fin n) (j : Fin m) :
    (fourOverSix measure (tiles 0 0) (tiles l k)).reconstruct (fun p => x (p.2, p.1)) (i, j) =
      (fourOverSix measure (tiles 0 0) (tiles k l)).reconstruct x (j, i) :=
  Format.reconstruct_relabel (π := Equiv.prodComm (Fin n) (Fin m))
    (F' := fourOverSix measure (tiles 0 0) (tiles l k))
    (F := fourOverSix measure (tiles 0 0) (tiles k l)) (fun _ => rfl)
    (List.Forall₂.cons
      (Level.transports_ofMax (Equiv.prodComm (Fin n) (Fin m)) Prod.swap Prod.swap_injective
        (tiles_swap 0 0) _ _ _)
      (List.Forall₂.cons
        (Level.transports_ofCandidates (Equiv.prodComm (Fin n) (Fin m)) Prod.swap
          Prod.swap_injective (tiles_swap k l) (Rounding.saturating .e4m3)
          (element := fun _ => Rounding.saturating .e2m1)
          (element' := fun _ => Rounding.saturating .e2m1) (fun _ => rfl) measure [6, 4] 0)
        List.Forall₂.nil))
    x (i, j)

end FloatLib.Floats.Formats.Block
