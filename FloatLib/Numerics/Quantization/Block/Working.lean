/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Block.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantization in a working arithmetic

`Format.quantize` rounds each element once, at its exact scaled input `x i / σ i`. An
implementation does not have that quotient: it computes the scaled input in its working arithmetic
(binary32 for the reference quantizers of NVFP4 and OCP MX), and the element format then rounds a
value that is already rounded. This module states what such a quantizer stores, for every
block-scaled format: any element format, any list of levels, any scale selection and any working
arithmetic.

* `Format.quantizeWith F input` stores `(F.element i).round (input x i)`: the element format
  applied to whatever the implementation computed as the scaled input. `Format.reconstructWith`
  decodes it with the total scale. With `input = F.normalized` they are `Format.quantize` and
  `Format.reconstruct`.
* `Rounding.Budget.abs_round_mul_sub_le` is the same bound for one stored value at any positive
  scale, with no reference to a scale selection: the form a bit-level quantizer uses.
* `Format.abs_reconstructWith_sub_le`: if the computed scaled input is within
  `δ * |x i / σ i| + θ` of the exact one and the element format has budget `(u, η, M)`, the error
  of an element is at most
  `(u * (1 + δ) + δ) * |x i| + σ i * (η + (1 + u) * θ) + max 0 ((1 + δ) * |x i| + σ i * θ - σ i
    * M)`.
  With `δ = θ = 0` this is `Format.abs_reconstruct_sub_le`.
* `Rounding.Nearest.round_eq_round` and `Format.quantizeWith_eq_quantize`: a nearest element
  format stores the computed input exactly as it stores the exact one when both lie between the
  same two adjacent stored values and the computed input is closer to the exact one than the
  exact one is to their midpoint. So the working quantizer and the exact rational quantizer can
  differ only at inputs within the working error of a midpoint of the element format.
* `Rounding.Accurate W ε θ`: the working arithmetic `W` rounds every value with relative error
  `ε` and absolute error `θ` (no overflow). `Rounding.Accurate.abs_round_mul_sub_le`: the
  product `W.round (x * r)` of an input with a reciprocal scale `r` of relative error `ρ` is
  within `((1 + ε) * (1 + ρ) - 1) * |x / σ| + θ` of `x / σ`, and
  `Rounding.Accurate.abs_round_div_sub_le` is the same for the reciprocal itself. This is the
  order of operations of torchao's `nvfp4_quantize`: one reciprocal per block, one product per
  element.
Concrete binary32/NVFP4 corollaries are in `Floats.Formats.Block.Working`.

The statements are about real or rational values. They do not model overflow of the working
arithmetic (`Accurate` is the budget of a format at every threshold, which `Rounding.grid` has).
The quantizer on the encodings of a binary working format, with its overflow, is
`Floats.Formats.Block.Working.Quantizer`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block


variable {ι γ K : Type*}

namespace Rounding

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `W` rounds every input with relative error `ε` and absolute error `θ`: a working arithmetic
whose range is never exceeded. -/
def Accurate (W : Rounding K) (ε θ : K) : Prop :=
  ∀ y, |W.round y - y| ≤ ε * |y| + θ

/-- A format with the budget `(ε, θ, M)` at every threshold `M` is accurate. -/
theorem accurate_of_budget {W : Rounding K} {ε θ : K} (h : ∀ M, W.Budget ε θ M) :
    W.Accurate ε θ := fun y => (h |y|).abs_sub_le le_rfl

/-- The exact format is accurate with no error. -/
theorem exact_accurate : (exact : Rounding K).Accurate 0 0 := by
  intro y
  simp [exact]

/--
One rounded product with a reciprocal scale. If `r` is within `ρ / σ` of `1 / σ`, the working
product `W.round (x * r)` is within `((1 + ε) * (1 + ρ) - 1) * |x / σ| + θ` of the exact scaled
input `x / σ`.
-/
theorem Accurate.abs_round_mul_sub_le {W : Rounding K} {ε θ ρ σ r : K} (hW : W.Accurate ε θ)
    (hε : 0 ≤ ε) (hσ : 0 < σ) (hr : |r - 1 / σ| ≤ ρ / σ) (x : K) :
    |W.round (x * r) - x / σ| ≤ ((1 + ε) * (1 + ρ) - 1) * |x / σ| + θ := by
  have hxσ : |x / σ| = |x| / σ := by rw [abs_div, abs_of_pos hσ]
  have h1 : |x * r - x / σ| ≤ ρ * |x / σ| := by
    have h : x * r - x / σ = x * (r - 1 / σ) := by ring
    rw [h, abs_mul, hxσ]
    calc |x| * |r - 1 / σ| ≤ |x| * (ρ / σ) := mul_le_mul_of_nonneg_left hr (abs_nonneg x)
      _ = ρ * (|x| / σ) := by ring
  have h2 : |x * r| ≤ (1 + ρ) * |x / σ| := by
    have h := abs_sub_abs_le_abs_sub (x * r) (x / σ)
    linarith
  have h3 := hW (x * r)
  have h4 : ε * |x * r| ≤ ε * ((1 + ρ) * |x / σ|) := mul_le_mul_of_nonneg_left h2 hε
  calc |W.round (x * r) - x / σ| ≤ |W.round (x * r) - x * r| + |x * r - x / σ| :=
        abs_sub_le _ _ _
    _ ≤ ((1 + ε) * (1 + ρ) - 1) * |x / σ| + θ := by linarith

/--
One rounded division of a reciprocal. If `c` is within `ρ / o` of `1 / o`, the working quotient
`W.round (c / s)` is within `((1 + ε) * (1 + ρ) - 1) / (o * s) + θ` of `1 / (o * s)`: the
reciprocal of the product of an outer scale `o` and a block scale `s`.
-/
theorem Accurate.abs_round_div_sub_le {W : Rounding K} {ε θ ρ o s c : K} (hW : W.Accurate ε θ)
    (hε : 0 ≤ ε) (ho : 0 < o) (hs : 0 < s) (hc : |c - 1 / o| ≤ ρ / o) :
    |W.round (c / s) - 1 / (o * s)| ≤ ((1 + ε) * (1 + ρ) - 1) / (o * s) + θ := by
  have h := hW.abs_round_mul_sub_le hε ho hc (1 / s)
  have e1 : 1 / s * c = c / s := by ring
  have e2 : 1 / s / o = 1 / (o * s) := by rw [div_div, mul_comm]
  have e3 : |1 / (o * s)| = 1 / (o * s) := abs_of_pos (one_div_pos.mpr (mul_pos ho hs))
  rw [e1, e2, e3] at h
  calc |W.round (c / s) - 1 / (o * s)| ≤ ((1 + ε) * (1 + ρ) - 1) * (1 / (o * s)) + θ := h
    _ = ((1 + ε) * (1 + ρ) - 1) / (o * s) + θ := by ring

/--
A nearest rounding stores two inputs alike when both lie between the same two adjacent stored
values `a` and `b` and the second is closer to the first than the first is to the midpoint. The
premise `hm` states that no stored value lies strictly between `a` and `b`, as in
`Nearest.round_eq_left`.
-/
theorem Nearest.round_eq_round {E : Rounding K} (h : E.Nearest) {a b y y' : K} (ha : E.Fixes a)
    (hb : E.Fixes b) (hm : E.round ((a + b) / 2) = a ∨ E.round ((a + b) / 2) = b)
    (hy : a ≤ y ∧ y ≤ b) (hy' : a ≤ y' ∧ y' ≤ b) (hclose : |y' - y| < |y - (a + b) / 2|) :
    E.round y' = E.round y := by
  have hd := abs_lt.mp hclose
  rcases lt_trichotomy y ((a + b) / 2) with hlt | heq | hgt
  · rw [abs_of_neg (by linarith)] at hd
    rw [h.round_eq_left ha hm hy.1 hlt, h.round_eq_left ha hm hy'.1 (by linarith [hd.2])]
  · rw [heq, sub_self, abs_zero] at hclose
    exact absurd hclose (not_lt.mpr (abs_nonneg _))
  · rw [abs_of_pos (by linarith)] at hd
    rw [h.round_eq_right hb hm hgt hy.2, h.round_eq_right hb hm (by linarith [hd.1]) hy'.2]

/--
One stored value decoded at the scale `σ > 0`, for an element format with budget `(u, η, M)` and
a scaled input `y'` within `δ * |x / σ| + θ` of the exact one: `E.round y' * σ` is within
`(u * (1 + δ) + δ) * |x| + σ * (η + (1 + u) * θ) + max 0 ((1 + δ) * |x| + σ * θ - σ * M)` of
`x`. Nothing is assumed about how the scale was selected.
-/
theorem Budget.abs_round_mul_sub_le {E : Rounding K} {u η M δ θ σ x y' : K}
    (hE : E.Budget u η M) (hu : 0 ≤ u) (hσ : 0 < σ)
    (hin : |y' - x / σ| ≤ δ * |x / σ| + θ) :
    |E.round y' * σ - x| ≤
      (u * (1 + δ) + δ) * |x| + σ * (η + (1 + u) * θ) +
        max 0 ((1 + δ) * |x| + σ * θ - σ * M) := by
  set y := x / σ
  have hx : y * σ = x := div_mul_cancel₀ x hσ.ne'
  have habs : |y| * σ = |x| := by
    calc |y| * σ = |y| * |σ| := by rw [abs_of_pos hσ]
      _ = |x| := by rw [← abs_mul, hx]
  have hrec : E.round y' * σ - x = (E.round y' - y) * σ := by rw [sub_mul, hx]
  have hy'le : |y'| ≤ (1 + δ) * |y| + θ := by
    have h := abs_sub_abs_le_abs_sub y' y
    linarith
  have hE' := hE y'
  have hmax : max 0 (|y'| - M) ≤ max 0 ((1 + δ) * |y| + θ - M) :=
    max_le_max le_rfl (by linarith)
  have hmul : u * |y'| ≤ u * ((1 + δ) * |y| + θ) := mul_le_mul_of_nonneg_left hy'le hu
  have hscale : max 0 ((1 + δ) * |y| + θ - M) * σ = max 0 ((1 + δ) * |x| + σ * θ - σ * M) := by
    rw [max_mul_of_nonneg _ _ hσ.le, zero_mul, ← habs]
    congr 1
    ring
  have hround : |E.round y' - y| ≤
      (u * (1 + δ) + δ) * |y| + (η + (1 + u) * θ) + max 0 ((1 + δ) * |y| + θ - M) := by
    calc |E.round y' - y| ≤ |E.round y' - y'| + |y' - y| := _root_.abs_sub_le _ _ _
      _ ≤ (u * (1 + δ) + δ) * |y| + (η + (1 + u) * θ) + max 0 ((1 + δ) * |y| + θ - M) := by
          linarith
  rw [hrec, abs_mul, abs_of_pos hσ]
  calc |E.round y' - y| * σ
      ≤ ((u * (1 + δ) + δ) * |y| + (η + (1 + u) * θ) + max 0 ((1 + δ) * |y| + θ - M)) * σ :=
        mul_le_mul_of_nonneg_right hround hσ.le
    _ = (u * (1 + δ) + δ) * |x| + σ * (η + (1 + u) * θ) +
          max 0 ((1 + δ) * |x| + σ * θ - σ * M) := by
        rw [add_mul, add_mul, hscale, ← habs]
        ring

end Rounding

namespace Format

section Field

variable [Field K]

/-- Stored element values of a quantizer that hands `input x i` to the element format in place
of the exact scaled input `F.normalized x i`: the scaled input as an implementation computes it
in its working arithmetic. -/
def quantizeWith (F : Format ι γ K) (input : (ι → K) → ι → K) (x : ι → K) (i : ι) : K :=
  (F.element i).round (input x i)

/-- The values reconstructed from `quantizeWith`: the stored elements decoded exactly with the
total scales. -/
def reconstructWith (F : Format ι γ K) (input : (ι → K) → ι → K) (x : ι → K) (i : ι) : K :=
  decode (F.scale x) (F.quantizeWith input x) i

/-- With the exact scaled input, `quantizeWith` is `quantize`. -/
theorem quantizeWith_normalized (F : Format ι γ K) : F.quantizeWith F.normalized = F.quantize :=
  rfl

/-- With the exact scaled input, `reconstructWith` is `reconstruct`. -/
theorem reconstructWith_normalized (F : Format ι γ K) :
    F.reconstructWith F.normalized = F.reconstruct :=
  rfl

end Field

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/--
The working quantizer stores what the exact quantizer stores at a position whose element format
is a nearest rounding, when the computed and the exact scaled input lie between the same two
adjacent element values `a` and `b` and differ by less than the distance of the exact one to the
midpoint of `a` and `b`.
-/
theorem quantizeWith_eq_quantize (F : Format ι γ K) (input : (ι → K) → ι → K) (x : ι → K)
    (i : ι) {a b : K} (h : (F.element i).Nearest) (ha : (F.element i).Fixes a)
    (hb : (F.element i).Fixes b)
    (hm : (F.element i).round ((a + b) / 2) = a ∨ (F.element i).round ((a + b) / 2) = b)
    (hy : a ≤ F.normalized x i ∧ F.normalized x i ≤ b) (hy' : a ≤ input x i ∧ input x i ≤ b)
    (hclose : |input x i - F.normalized x i| < |F.normalized x i - (a + b) / 2|) :
    F.quantizeWith input x i = F.quantize x i :=
  h.round_eq_round ha hb hm hy hy' hclose

/--
Error of one element of a working quantizer, for every element format, level structure and
scale selection. If the element format has budget `(u, η, M)`, the total scale `σ` is positive
and the computed scaled input is within `δ * |x / σ| + θ` of the exact one, the error is at most
`(u * (1 + δ) + δ) * |x| + σ * (η + (1 + u) * θ) + max 0 ((1 + δ) * |x| + σ * θ - σ * M)`.
-/
theorem abs_reconstructWith_sub_le (F : Format ι γ K) (input : (ι → K) → ι → K) (x : ι → K)
    (i : ι) {u η M δ θ : K} (hE : (F.element i).Budget u η M) (hu : 0 ≤ u)
    (hσ : 0 < F.scale x i)
    (hin : |input x i - x i / F.scale x i| ≤ δ * |x i / F.scale x i| + θ) :
    |F.reconstructWith input x i - x i| ≤
      (u * (1 + δ) + δ) * |x i| + F.scale x i * (η + (1 + u) * θ) +
        max 0 ((1 + δ) * |x i| + F.scale x i * θ - F.scale x i * M) :=
  hE.abs_round_mul_sub_le hu hσ hin

/--
Error of one element of a quantizer that multiplies by a reciprocal scale in a working
arithmetic: with `W` accurate to `(ε, θ)` and `r i` within `ρ / σ` of `1 / σ`, the bound of
`abs_reconstructWith_sub_le` holds with `δ = (1 + ε) * (1 + ρ) - 1`.
-/
theorem abs_reconstructWith_mul_sub_le (F : Format ι γ K) (W : Rounding K) (r : ι → K)
    (x : ι → K) (i : ι) {u η M ε θ ρ : K} (hE : (F.element i).Budget u η M) (hu : 0 ≤ u)
    (hW : W.Accurate ε θ) (hε : 0 ≤ ε) (hσ : 0 < F.scale x i)
    (hr : |r i - 1 / F.scale x i| ≤ ρ / F.scale x i) :
    |F.reconstructWith (fun x i => W.round (x i * r i)) x i - x i| ≤
      (u * (1 + ((1 + ε) * (1 + ρ) - 1)) + ((1 + ε) * (1 + ρ) - 1)) * |x i| +
        F.scale x i * (η + (1 + u) * θ) +
        max 0 ((1 + ((1 + ε) * (1 + ρ) - 1)) * |x i| + F.scale x i * θ - F.scale x i * M) :=
  F.abs_reconstructWith_sub_le _ x i hE hu hσ (hW.abs_round_mul_sub_le hε hσ hr (x i))

end Format

end FloatLib.Floats.Formats.Block
