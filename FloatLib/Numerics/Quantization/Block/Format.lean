/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Rounding
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.CharZero

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Block-scaled formats

A block-scaled format stores every element in a narrow element format and shares scales between
groups of elements. `Format ι γ K` has four parameters, and a format of an ML accelerator is one
choice of them:

* the element format of each position `i : ι`, a `Rounding K` (OCP FP8, FP6 and FP4, P3109, a
  binary format of any width, fixed point, integers; a position may have its own rounding, which
  covers a stochastic rounding fed by one entropy value per element);
* a list of scale levels, outermost first. A `Level` has the group of each element (the block
  shape for the last level: `1 × k` along either axis, `k × k` tiles; a tensor, row, expert or
  token for an outer level), the storage format of its scales (a power of two for E8M0, E4M3,
  binary32), and its scale-selection rule `ideal`;
* the selection rule sees the data already divided by the scales of the levels above it, and the
  level stores its ideal scale rounded in its own format.

`Format.quantize` rounds each element once, at its exact scaled input `Format.normalized`, and
`Format.decode` multiplies a stored element by its scales, with no rounding. `Format.reconstruct`
is their composition.

## Main results, for every format at once

* `Format.reconstruct_eq`: the reconstructed element is one rounding of the input in the element
  format scaled by the element's total scale.
* `Format.abs_reconstruct_sub_le`: with element budget `(u, η, M)` and positive total scale `σ`,
  the error of an element is at most `u * |x| + σ * η + max 0 (|x| - σ * M)`.
* `Format.abs_reconstruct_sub_le_of_abs_le`: without saturation it is at most `u * |x| + σ * η`.
* `Format.abs_reconstruct_sub_le_abs`: the same budget with `|σ|`, for a total scale of any sign,
  zero included.
* `Format.sum_abs_reconstruct_sub_le`: the same budget summed over a block or any set of elements.
* `Format.reconstruct_eq_zero_iff_mem`, `Format.reconstruct_eq_zero_iff_abs_le`: an element is
  reconstructed as zero exactly when its input lies in the element format's zero set multiplied by
  its total scale, for any rounding direction, and for the closed symmetric zero set of nearest
  rounding with ties to zero.
* `total_pos`: the total scale is positive when every stored scale is.

* `LiftsAt`, `total_ratCast`, `Format.reconstruct_ratCast`: a format over the rationals and a
  format over another field reconstruct the same values when their levels select the same scales
  and their element formats round alike. This is how the theorems of a real format reach the
  rational format an executable quantizer computes.

No theorem here depends on how a level selects its scale. `Block.Policy` has the selection rules.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

/--
One level of shared scaling over elements `ι` with groups `γ`: which group's scale an element
uses, how the level's scales are stored, and how the unrounded scale of a group is selected.
-/
structure Level (ι γ K : Type*) where
  /-- The group whose scale an element uses. -/
  group : ι → γ
  /-- Storage format of the level's scales. -/
  format : Rounding K
  /-- Scale selection: the unrounded scale of each group, from the data already divided by the
  scales of the levels above this one. -/
  ideal : (ι → K) → γ → K

/--
A block-scaled format: the element format of each position and the scale levels, outermost first.
The last level is the block scale and the levels before it are the outer scales.
-/
structure Format (ι γ K : Type*) where
  /-- Element format of each position. -/
  element : ι → Rounding K
  /-- Scale levels, outermost first. -/
  levels : List (Level ι γ K)

variable {ι γ K : Type*}

namespace Level

/-- Stored scale of each group: the ideal scale rounded in the level's format. -/
def scale (L : Level ι γ K) (y : ι → K) (g : γ) : K :=
  L.format.round (L.ideal y g)

/-- Stored scale an element uses at this level. -/
def scaleAt (L : Level ι γ K) (y : ι → K) (i : ι) : K :=
  L.scale y (L.group i)

end Level

section Field

variable [Field K]

/-- The data divided by the stored scales of every level, outermost first. -/
def normalize : List (Level ι γ K) → (ι → K) → ι → K
  | [], x => x
  | L :: Ls, x => normalize Ls fun i => x i / L.scaleAt x i

/-- Total scale of each element: the product of the stored scales of its groups. -/
def total : List (Level ι γ K) → (ι → K) → ι → K
  | [], _, _ => 1
  | L :: Ls, x, i => L.scaleAt x i * total Ls (fun j => x j / L.scaleAt x j) i

/-- The normalized data is the input divided by the total scale. -/
theorem normalize_eq_div_total (levels : List (Level ι γ K)) (x : ι → K) (i : ι) :
    normalize levels x i = x i / total levels x i := by
  induction levels generalizing x with
  | nil => simp [normalize, total]
  | cons L Ls ih => rw [normalize, ih, total, div_div]

namespace Format

/-- Exact scaled input of each element: the data divided by every selected scale. -/
def normalized (F : Format ι γ K) (x : ι → K) : ι → K :=
  normalize F.levels x

/-- Total scale selected for each element. -/
def scale (F : Format ι γ K) (x : ι → K) : ι → K :=
  total F.levels x

/-- Stored element values: one rounding of each exact scaled input in the element format. -/
def quantize (F : Format ι γ K) (x : ι → K) (i : ι) : K :=
  (F.element i).round (F.normalized x i)

/-- Exact decoding of stored elements `e` under total scales `σ`: element times scales. -/
def decode (σ e : ι → K) (i : ι) : K :=
  e i * σ i

/-- The values a format reconstructs from `x`: quantization followed by exact decoding. -/
def reconstruct (F : Format ι γ K) (x : ι → K) (i : ι) : K :=
  decode (F.scale x) (F.quantize x) i

/-- The scaled input is the input divided by the total scale. -/
theorem normalized_eq (F : Format ι γ K) (x : ι → K) (i : ι) :
    F.normalized x i = x i / F.scale x i :=
  normalize_eq_div_total F.levels x i

/--
Each reconstructed element is one rounding of its input in the element format scaled by the
element's total scale. This holds for every element format, level structure and selection rule.
-/
theorem reconstruct_eq (F : Format ι γ K) (x : ι → K) (i : ι) :
    F.reconstruct x i = ((F.element i).scaled (F.scale x i)).round (x i) := by
  simp [reconstruct, decode, quantize, normalized_eq]

/-- An element with total scale zero is reconstructed as zero. -/
theorem reconstruct_eq_zero_of_scale (F : Format ι γ K) (x : ι → K) {i : ι}
    (h : F.scale x i = 0) : F.reconstruct x i = 0 := by
  simp [reconstruct, decode, h]

/--
Flush to zero, for any rounding direction: an element is reconstructed as zero exactly when its
scaled input lies in the element format's zero set `Z`.
-/
theorem reconstruct_eq_zero_iff_mem (F : Format ι γ K) (x : ι → K) (i : ι) {Z : Set K}
    (hZ : ∀ y, (F.element i).round y = 0 ↔ y ∈ Z) (hσ : F.scale x i ≠ 0) :
    F.reconstruct x i = 0 ↔ x i / F.scale x i ∈ Z := by
  rw [reconstruct_eq, Rounding.scaled_round_eq_zero_iff_mem hZ hσ]

end Format

end Field

section Ordered

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The total scale is positive when every level stores positive scales. -/
theorem total_pos (levels : List (Level ι γ K))
    (h : ∀ L ∈ levels, ∀ y g, 0 < L.scale y g) (x : ι → K) (i : ι) :
    0 < total levels x i := by
  induction levels generalizing x with
  | nil => simp [total]
  | cons L Ls ih =>
    rw [total]
    exact mul_pos (h L List.mem_cons_self _ _)
      (ih (fun L' hL' => h L' (List.mem_cons_of_mem _ hL')) _)

namespace Format

/--
Error of one element: relative error `u` of the element format, its absolute error `η` multiplied
by the total scale, and the loss of saturating at `M` times the total scale.
-/
theorem abs_reconstruct_sub_le (F : Format ι γ K) (x : ι → K) (i : ι) {u η M : K}
    (hE : (F.element i).Budget u η M) (hσ : 0 < F.scale x i) :
    |F.reconstruct x i - x i| ≤
      u * |x i| + F.scale x i * η + max 0 (|x i| - F.scale x i * M) := by
  rw [reconstruct_eq]
  exact hE.scaled hσ (x i)

/--
Error of one element with no condition on the scale: the budget of the element format with the
absolute error and the saturation threshold multiplied by the magnitude of the total scale.
-/
theorem abs_reconstruct_sub_le_abs (F : Format ι γ K) (x : ι → K) (i : ι) {u η M : K}
    (hE : (F.element i).Budget u η M) (hu : 0 ≤ u) :
    |F.reconstruct x i - x i| ≤
      u * |x i| + |F.scale x i| * η + max 0 (|x i| - |F.scale x i| * M) := by
  rw [reconstruct_eq]
  exact hE.scaled_abs hu (F.scale x i) (x i)

/-- Error of one element that does not saturate: `u * |x| + σ * η`. -/
theorem abs_reconstruct_sub_le_of_abs_le (F : Format ι γ K) (x : ι → K) (i : ι) {u η M : K}
    (hE : (F.element i).Budget u η M) (hσ : 0 < F.scale x i)
    (hx : |x i| ≤ F.scale x i * M) :
    |F.reconstruct x i - x i| ≤ u * |x i| + F.scale x i * η := by
  rw [reconstruct_eq]
  exact (hE.scaled hσ).abs_sub_le hx

/--
Error of a set of elements with one element budget, for example a block: the sum of the element
errors is at most `u` times the sum of the magnitudes, `η` times the sum of the total scales, and
the summed saturation losses.
-/
theorem sum_abs_reconstruct_sub_le (F : Format ι γ K) (x : ι → K) (s : Finset ι) {u η M : K}
    (hE : ∀ i ∈ s, (F.element i).Budget u η M) (hσ : ∀ i ∈ s, 0 < F.scale x i) :
    ∑ i ∈ s, |F.reconstruct x i - x i| ≤
      u * ∑ i ∈ s, |x i| + η * ∑ i ∈ s, F.scale x i +
        ∑ i ∈ s, max 0 (|x i| - F.scale x i * M) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have h := F.abs_reconstruct_sub_le x i (hE i hi) (hσ i hi)
  rwa [mul_comm (F.scale x i) η] at h

/--
Largest error in a set of elements that do not saturate: if every magnitude is at most `A` and
every total scale at most `S`, every element error is at most `u * A + S * η`.
-/
theorem abs_reconstruct_sub_le_of_bounds (F : Format ι γ K) (x : ι → K) (i : ι) {u η M A S : K}
    (hE : (F.element i).Budget u η M) (hu : 0 ≤ u) (hη : 0 ≤ η) (hσ : 0 < F.scale x i)
    (hx : |x i| ≤ F.scale x i * M) (hA : |x i| ≤ A) (hS : F.scale x i ≤ S) :
    |F.reconstruct x i - x i| ≤ u * A + S * η := by
  have h := F.abs_reconstruct_sub_le_of_abs_le x i hE hσ hx
  have h1 : u * |x i| ≤ u * A := mul_le_mul_of_nonneg_left hA hu
  have h2 : F.scale x i * η ≤ S * η := mul_le_mul_of_nonneg_right hS hη
  linarith

/--
Flush to zero under nearest rounding with ties to zero (ties to even): if the element format
stores exactly the magnitudes up to `τ` as zero, an element is reconstructed as zero exactly when
its magnitude is at most `τ` times its total scale.
-/
theorem reconstruct_eq_zero_iff_abs_le (F : Format ι γ K) (x : ι → K) (i : ι) {τ : K}
    (hZ : ∀ y, (F.element i).round y = 0 ↔ |y| ≤ τ) (hσ : 0 < F.scale x i) :
    F.reconstruct x i = 0 ↔ |x i| ≤ τ * F.scale x i := by
  rw [reconstruct_eq, Rounding.scaled_round_eq_zero_iff_abs_le hZ hσ]

end Format

end Ordered

section RatCast

variable [Field K] [CharZero K]

/--
The levels `Ls'` over `K` select, at the rational data `x`, the scales that the levels `Ls` over
`ℚ` select. The comparison is level by level, outermost first, and each later level is compared
at the data divided by the scales of the earlier ones.
-/
def LiftsAt : List (Level ι γ ℚ) → List (Level ι γ K) → (ι → ℚ) → Prop
  | [], [], _ => True
  | L :: Ls, L' :: Ls', x =>
      (∀ i, ((L.scaleAt x i : ℚ) : K) = L'.scaleAt (fun j => (x j : K)) i) ∧
        LiftsAt Ls Ls' fun i => x i / L.scaleAt x i
  | [], _ :: _, _ => False
  | _ :: _, [], _ => False

/-- Levels that select the same scales have the same total scales. -/
theorem total_ratCast : ∀ {Ls : List (Level ι γ ℚ)} {Ls' : List (Level ι γ K)} {x : ι → ℚ},
    LiftsAt Ls Ls' x → ∀ i, ((total Ls x i : ℚ) : K) = total Ls' (fun j => (x j : K)) i
  | [], [], _, _, _ => by simp [total]
  | L :: Ls, L' :: Ls', x, h, i => by
    obtain ⟨h1, h2⟩ := h
    have hdata : (fun j => ((x j / L.scaleAt x j : ℚ) : K)) =
        fun j => (x j : K) / L'.scaleAt (fun k => (x k : K)) j := by
      funext j
      rw [Rat.cast_div, h1 j]
    rw [total, total, Rat.cast_mul, h1 i, total_ratCast h2 i, hdata]
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim

/--
A format over the rationals and a format over `K` reconstruct the same value at a position, when
their levels select the same scales at the data and their element formats round the position's
scaled input to the same value. This carries a theorem about a format over the reals to the
format over the rationals that an executable quantizer computes.
-/
theorem Format.reconstruct_ratCast {F : Format ι γ ℚ} {F' : Format ι γ K} {x : ι → ℚ}
    (hlevels : LiftsAt F.levels F'.levels x) (i : ι)
    (helement : (((F.element i).round (x i / total F.levels x i) : ℚ) : K) =
      (F'.element i).round (((x i / total F.levels x i : ℚ)) : K)) :
    ((F.reconstruct x i : ℚ) : K) = F'.reconstruct (fun j => (x j : K)) i := by
  have hσ := total_ratCast hlevels i
  rw [Format.reconstruct_eq, Format.reconstruct_eq, Rounding.scaled_round, Rounding.scaled_round]
  change (((F.element i).round (x i / total F.levels x i) * total F.levels x i : ℚ) : K) =
    (F'.element i).round ((x i : K) / total F'.levels (fun j => (x j : K)) i) *
      total F'.levels (fun j => (x j : K)) i
  rw [Rat.cast_mul, helement, Rat.cast_div, hσ]

end RatCast

end FloatLib.Floats.Formats.Block
