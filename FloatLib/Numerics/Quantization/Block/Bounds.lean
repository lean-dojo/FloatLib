/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Block.Policy

/-!
# Error and flush to zero as functions of the block maximum

`Block.Format` bounds the error of an element through its total scale. A level that selects from
the largest magnitude `a` of a block stores a scale near `a / t`, with `t` its target. This module
states the consequences in terms of `a`, for any format whose total scale at an element lies
between `c₁ * (a / t)` and `c₂ * (a / t)`:

* `Format.abs_reconstruct_sub_le_of_max`: without saturation (`t / c₁` at most the element
  format's largest magnitude), the error of an element is at most `u * |x| + c₂ * (a / t) * η`.
  The absolute part is a fixed fraction of the block maximum.
* `Format.reconstruct_eq_zero_of_abs_le`, `Format.abs_le_of_reconstruct_eq_zero`,
  `Format.reconstruct_eq_zero_iff_of_scale_eq`: with zero threshold `τ` of the element format,
  an element of magnitude at most `τ * c₁ * (a / t)` is reconstructed as zero, an element
  reconstructed as zero has magnitude at most `τ * c₂ * (a / t)`, and with an exact scale the
  flushed elements are exactly those of magnitude at most `τ * (a / t)`.
* `Format.reconstruct_eq_self`: an element whose scaled input is stored exactly is reconstructed
  exactly. With an exact scale and the element format's largest magnitude as target, this is the
  block maximum.
* `Format.reconstruct_eq_of_saturated`, `Format.reconstruct_eq_of_saturated_neg`: an element that
  saturates is reconstructed as the largest element magnitude times its total scale. A scale
  rounded below `a / t` does this to the block maximum, with error `a - t * σ`.

`total_pos_of_format` discharges the positivity premise for a level with a power-of-two scale
format. `total_append_ofMax` supplies the scale: under outer levels whose total scale is the
constant `o` on a block, the block's effective scale is one rounding of `a / t` in the scale
format scaled by `o`. With no outer level, `o = 1`. So the scale-format facts of `Block.Policy`
and the budgets of
`Rounding.scaled` give `c₁` and `c₂` at any depth of scaling.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

variable {ι γ K : Type*}

section Field

variable [Field K]

/-- An element whose scaled input the element format stores exactly is reconstructed exactly. -/
theorem Format.reconstruct_eq_self (F : Format ι γ K) (x : ι → K) (i : ι)
    (hfix : (F.element i).Fixes (x i / F.scale x i)) (hσ : F.scale x i ≠ 0) :
    F.reconstruct x i = x i := by
  rw [Format.reconstruct_eq]
  simpa only [Rounding.Fixes, div_mul_cancel₀ _ hσ] using hfix.scaled hσ

end Field

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace Format

/--
Error of an element as a function of its block's largest magnitude `a`. If the total scale lies
between `c₁ * (a / t)` and `c₂ * (a / t)` and `t / c₁` is inside the element range, the error is
at most `u * |x| + c₂ * (a / t) * η`.
-/
theorem abs_reconstruct_sub_le_of_max (F : Format ι γ K) (x : ι → K) (i : ι)
    {u η M a t c₁ c₂ : K} (hE : (F.element i).Budget u η M) (hη : 0 ≤ η) (ha : 0 < a)
    (ht : 0 < t) (hc₁ : 0 < c₁) (hx : |x i| ≤ a) (hlo : c₁ * (a / t) ≤ F.scale x i)
    (hhi : F.scale x i ≤ c₂ * (a / t)) (hM : t / c₁ ≤ M) :
    |F.reconstruct x i - x i| ≤ u * |x i| + c₂ * (a / t) * η := by
  have hσ : 0 < F.scale x i := (mul_pos hc₁ (div_pos ha ht)).trans_le hlo
  have hdiv : |x i / F.scale x i| ≤ t / c₁ := abs_div_scale_le ha ht hc₁ hlo hx
  have hrange : |x i| ≤ F.scale x i * M := by
    have h := hdiv.trans hM
    rw [abs_div, abs_of_pos hσ, div_le_iff₀ hσ] at h
    linarith
  have h := F.abs_reconstruct_sub_le_of_abs_le x i hE hσ hrange
  have h2 : F.scale x i * η ≤ c₂ * (a / t) * η := mul_le_mul_of_nonneg_right hhi hη
  linarith

/--
Sufficient condition for flush to zero: with zero threshold `τ` and total scale at least
`c * (a / t)`, an element of magnitude at most `τ * (c * (a / t))` is reconstructed as zero.
-/
theorem reconstruct_eq_zero_of_abs_le (F : Format ι γ K) (x : ι → K) (i : ι) {τ a t c : K}
    (hZ : ∀ y, (F.element i).round y = 0 ↔ |y| ≤ τ) (hτ : 0 ≤ τ) (hσ : 0 < F.scale x i)
    (hlo : c * (a / t) ≤ F.scale x i) (hx : |x i| ≤ τ * (c * (a / t))) :
    F.reconstruct x i = 0 :=
  (F.reconstruct_eq_zero_iff_abs_le x i hZ hσ).mpr
    (hx.trans (mul_le_mul_of_nonneg_left hlo hτ))

/--
Necessary condition for flush to zero: with zero threshold `τ` and total scale at most
`c * (a / t)`, an element reconstructed as zero has magnitude at most `τ * (c * (a / t))`.
-/
theorem abs_le_of_reconstruct_eq_zero (F : Format ι γ K) (x : ι → K) (i : ι) {τ a t c : K}
    (hZ : ∀ y, (F.element i).round y = 0 ↔ |y| ≤ τ) (hτ : 0 ≤ τ) (hσ : 0 < F.scale x i)
    (hhi : F.scale x i ≤ c * (a / t)) (h0 : F.reconstruct x i = 0) :
    |x i| ≤ τ * (c * (a / t)) :=
  ((F.reconstruct_eq_zero_iff_abs_le x i hZ hσ).mp h0).trans
    (mul_le_mul_of_nonneg_left hhi hτ)

/--
Flush to zero with an exact scale: when the total scale is exactly `a / t`, the elements
reconstructed as zero are exactly those of magnitude at most `τ * (a / t)`. For E2M1 with target
`6`, `τ = 1 / 4` and the threshold is `a / 24`.
-/
theorem reconstruct_eq_zero_iff_of_scale_eq (F : Format ι γ K) (x : ι → K) (i : ι) {τ a t : K}
    (hZ : ∀ y, (F.element i).round y = 0 ↔ |y| ≤ τ) (hσ : F.scale x i = a / t)
    (hpos : 0 < a / t) : F.reconstruct x i = 0 ↔ |x i| ≤ τ * (a / t) := by
  rw [F.reconstruct_eq_zero_iff_abs_le x i hZ (hσ ▸ hpos), hσ]

/--
A positive element that saturates is reconstructed as the largest element magnitude times its
total scale.
-/
theorem reconstruct_eq_of_saturated (F : Format ι γ K) (x : ι → K) (i : ι) {M : K}
    (hsat : ∀ y, M ≤ y → (F.element i).round y = M) (hσ : 0 < F.scale x i)
    (hx : F.scale x i * M ≤ x i) : F.reconstruct x i = M * F.scale x i := by
  rw [reconstruct_eq, Rounding.scaled_round, hsat _ ((le_div_iff₀ hσ).mpr (by linarith))]

/--
A negative element that saturates is reconstructed as minus the largest element magnitude times
its total scale.
-/
theorem reconstruct_eq_of_saturated_neg (F : Format ι γ K) (x : ι → K) (i : ι) {M : K}
    (hsat : ∀ y, y ≤ -M → (F.element i).round y = -M) (hσ : 0 < F.scale x i)
    (hx : x i ≤ -(F.scale x i * M)) : F.reconstruct x i = -M * F.scale x i := by
  rw [reconstruct_eq, Rounding.scaled_round, hsat _ ((div_le_iff₀ hσ).mpr (by linarith))]

end Format

section Max

variable [Fintype ι] [DecidableEq γ]

/--
Effective scale of a block under outer scales. If the levels above an `ofMax` level have the
constant total scale `o` on a block that is not all zero, the total scale of the block is one
rounding of its ideal scale `amax / target` in the scale format scaled by `o`. With no level
above, `o = 1` and the scaled format is the scale format itself.
-/
theorem total_append_ofMax (outer : List (Level ι γ K)) (group : ι → γ) (format : Rounding K)
    (target zero : K) (x : ι → K) (i : ι) {o : K} (ho : 0 < o)
    (hconst : ∀ j, group j = group i → total outer x j = o)
    (ha : 0 < amax group x (group i)) :
    total (outer ++ [Level.ofMax group format target zero]) x i =
      (format.scaled o).round (amax group x (group i) / target) := by
  have hnorm : normalize outer x = fun j => x j / total outer x j :=
    funext fun j => normalize_eq_div_total outer x j
  have hamax : amax group (normalize outer x) (group i) = amax group x (group i) / o := by
    rw [hnorm]
    exact amax_div ho hconst
  have hpos : 0 < amax group (normalize outer x) (group i) := hamax ▸ div_pos ha ho
  rw [total_append, total_singleton, hconst i rfl, Level.scaleAt,
    show (Level.ofMax group format target zero).group i = group i from rfl,
    Level.ofMax_scale hpos, hamax, Rounding.scaled_round, div_right_comm, mul_comm]

/-- The total scale of a single `ofMax` level on a block that is not all zero is the rounded
ideal scale. -/
theorem total_ofMax (group : ι → γ) (format : Rounding K) (target zero : K) (x : ι → K)
    (i : ι) (ha : 0 < amax group x (group i)) :
    total [Level.ofMax group format target zero] x i =
      format.round (amax group x (group i) / target) := by
  have h := total_append_ofMax [] group format target zero x i (o := 1) one_pos
    (fun _ _ => rfl) ha
  simpa [Rounding.scaled_one] using h

end Max

/-- With one level whose scale format stores positive scales only, such as a power-of-two
rounding, every total scale is positive. -/
theorem total_pos_of_format (L : Level ι γ K) (hpos : ∀ y, 0 < L.format.round y) (x : ι → K)
    (i : ι) : 0 < total [L] x i :=
  total_pos _ (fun L' hL' y g => by rw [List.mem_singleton.mp hL']; exact hpos _) x i

end FloatLib.Floats.Formats.Block
