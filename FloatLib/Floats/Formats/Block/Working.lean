/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Catalog
public import FloatLib.Floats.Formats.Block.Working.Binary
public import FloatLib.Numerics.Quantization.Block.Working

/-!
# Quantization in a binary working format: errors, and NVFP4 in binary32

`Block.Working.Quantizer` is a block quantizer on the encodings of a binary working format, in
the order of torchao's `nvfp4_quantize`. `Block.Working.Binary` proves what it stores. This
module turns that into errors, for every working format, scale format and element format:

* `grid_accurate`: the grid of a binary descriptor rounds with its unit roundoff and half its
  least subnormal.
* `Working.Quantizer.abs_reciprocal_sub_le`: a reciprocal that did not overflow is within
  `((1 + u) * (1 + (u + θ * o)) - 1) / (o * s) + θ` of `1 / (o * s)`, with `u` and `θ` the unit
  roundoff and the underflow error of the working format, `o` the outer scale and `s` the
  stored block scale.
* `Working.Quantizer.abs_element_mul_sub_le`: the error of a stored element, decoded at the
  total scale `σ`, for a quantizer whose target is the largest element value and a reciprocal
  within `ρ / σ` of `1 / σ`. The product may overflow: the clamp of the quantizer and the
  saturation of the element format agree there.
* `Working.Quantizer.abs_element_sub_le`: the two together, with no premise on the reciprocal
  but that it is finite.

`nvfp4Working` is the instance binary32, E4M3, E2M1 with the target `6`, the floor `2 ^ -6` and
the ceiling `448`, and `nvfp4Working_abs_element_sub_le` is its error. The theorems about
`nvfp4 outer block` below are the earlier real-valued forms, whose scale is selected in exact
arithmetic and whose reciprocal error is a premise.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Floats.Formats.BinaryInterchange.Model

/-- The grid of a binary descriptor, with no upper limit, rounds every value with the unit
roundoff of the descriptor and half its least subnormal. -/
theorem grid_accurate (fmt : FloatFormat) :
    (Rounding.grid fmt).Accurate (unitRoundoffAt fmt) (underflowErrorAt fmt) :=
  Rounding.accurate_of_budget (Rounding.grid_budget fmt)

namespace Working.Quantizer

variable {W S E : FloatFormat} (Q : Working.Quantizer W S E)

/--
Accuracy of the reciprocal of the total scale, for every IEEE working format: a reciprocal that
did not overflow is within `((1 + u) * (1 + (u + θ * o)) - 1) / (o * s) + θ` of `1 / (o * s)`.
Here `o` is the outer scale, `s` the stored block scale as the working format holds it, and `u`
and `θ` the unit roundoff and the underflow error of the working format.
-/
theorem abs_reciprocal_sub_le (hW : W.isIEEE = true) {outer : Model W}
    (ho : isFinite outer = true) (ho0 : 0 < toReal outer) {stored : Model S}
    (hs : isFinite (Model.cast S W stored) = true) (hs0 : 0 < toReal (Model.cast S W stored))
    (hfin : isFinite (Q.reciprocal outer stored) = true) :
    |toReal (Q.reciprocal outer stored) -
        1 / (toReal outer * toReal (Model.cast S W stored))| ≤
      ((1 + unitRoundoffAt W) *
          (1 + (unitRoundoffAt W + underflowErrorAt W * toReal outer)) - 1) /
        (toReal outer * toReal (Model.cast S W stored)) + underflowErrorAt W := by
  rcases Q.reciprocal_eq hW ho ho0 hs hs0 with ⟨-, hval⟩ | hinf
  · rw [hval]
    have hc : |roundAt W (1 / toReal outer) - 1 / toReal outer| ≤
        (unitRoundoffAt W + underflowErrorAt W * toReal outer) / toReal outer := by
      have h := grid_accurate W (1 / toReal outer)
      rw [abs_of_pos (one_div_pos.mpr ho0)] at h
      calc |roundAt W (1 / toReal outer) - 1 / toReal outer|
          ≤ unitRoundoffAt W * (1 / toReal outer) + underflowErrorAt W := h
        _ = (unitRoundoffAt W + underflowErrorAt W * toReal outer) / toReal outer := by
            field_simp
    exact (grid_accurate W).abs_round_div_sub_le (unitRoundoffAt_pos W).le ho0 hs0 hc
  · rw [hinf, isFinite_posInf W (FloatFormat.supportsInfinity_eq_true_of_isIEEE W hW)] at hfin
    exact absurd hfin (by decide)

/--
Error of one stored element, decoded at the total scale `σ`, for every IEEE working format and
every element format, when the target of the quantizer is the largest element value. If the
element format has the budget `(u_E, η_E, M)` and the reciprocal `r` is finite and within
`ρ / σ` of `1 / σ`, the error is that budget with the working error
`δ = (1 + u) * (1 + ρ) - 1` added to the relative part and to the saturating magnitude, and
`(1 + u_E) * θ` per unit of scale, where `u` and `θ` are the unit roundoff and the underflow
error of the working format. The product `x * r` may overflow: the bound holds as it is.
-/
theorem abs_element_mul_sub_le (hW : W.isIEEE = true) (hT : isFinite Q.target = true)
    (hTE : toReal Q.target = toReal (posMaxFinite E)) {u η M : ℝ}
    (hB : (Rounding.saturating E).Budget u η M) (hu : 0 ≤ u) {r x : Model W}
    (hr : isFinite r = true) (hx : isFinite x = true) {σ ρ : ℝ} (hσ : 0 < σ)
    (hrσ : |toReal r - 1 / σ| ≤ ρ / σ) :
    |toReal (Q.element r x) * σ - toReal x| ≤
      (u * (1 + ((1 + unitRoundoffAt W) * (1 + ρ) - 1)) +
          ((1 + unitRoundoffAt W) * (1 + ρ) - 1)) * |toReal x| +
        σ * (η + (1 + u) * underflowErrorAt W) +
        max 0 ((1 + ((1 + unitRoundoffAt W) * (1 + ρ) - 1)) * |toReal x| +
          σ * underflowErrorAt W - σ * M) := by
  have hT0 : 0 ≤ toReal Q.target := by
    rw [hTE]
    exact (toReal_posMaxFinite_pos E).le
  obtain ⟨-, hval⟩ := Q.toReal_element hW hT hT0 hTE.le hr hx
  rw [hval, hTE, Rounding.saturating_round_clamp]
  exact hB.abs_round_mul_sub_le hu hσ
    ((grid_accurate W).abs_round_mul_sub_le (unitRoundoffAt_pos W).le hσ hrσ (toReal x))

/--
Error of one stored element under the reciprocal that the quantizer computes, for every IEEE
working format: with `o` the outer scale, `s` the stored block scale as the working format holds
it and `σ = o * s`, a finite reciprocal is within `ρ / σ` of `1 / σ` for
`ρ = (1 + u) * (1 + (u + θ * o)) - 1 + θ * σ`, and the error of the element is the bound of
`abs_element_mul_sub_le` at that `ρ`. The only premise on the arithmetic is that the reciprocal
is finite: the product may overflow.
-/
theorem abs_element_sub_le (hW : W.isIEEE = true) (hT : isFinite Q.target = true)
    (hTE : toReal Q.target = toReal (posMaxFinite E)) {u η M : ℝ}
    (hB : (Rounding.saturating E).Budget u η M) (hu : 0 ≤ u) {outer : Model W}
    (ho : isFinite outer = true) (ho0 : 0 < toReal outer) {stored : Model S}
    (hs : isFinite (Model.cast S W stored) = true) (hs0 : 0 < toReal (Model.cast S W stored))
    (hfin : isFinite (Q.reciprocal outer stored) = true) {x : Model W}
    (hx : isFinite x = true) {ρ : ℝ}
    (hρ : ρ = (1 + unitRoundoffAt W) *
        (1 + (unitRoundoffAt W + underflowErrorAt W * toReal outer)) - 1 +
      underflowErrorAt W * (toReal outer * toReal (Model.cast S W stored))) :
    |toReal (Q.element (Q.reciprocal outer stored) x) *
          (toReal outer * toReal (Model.cast S W stored)) - toReal x| ≤
      (u * (1 + ((1 + unitRoundoffAt W) * (1 + ρ) - 1)) +
          ((1 + unitRoundoffAt W) * (1 + ρ) - 1)) * |toReal x| +
        toReal outer * toReal (Model.cast S W stored) * (η + (1 + u) * underflowErrorAt W) +
        max 0 ((1 + ((1 + unitRoundoffAt W) * (1 + ρ) - 1)) * |toReal x| +
          toReal outer * toReal (Model.cast S W stored) * underflowErrorAt W -
          toReal outer * toReal (Model.cast S W stored) * M) := by
  have hσ : 0 < toReal outer * toReal (Model.cast S W stored) := mul_pos ho0 hs0
  refine Q.abs_element_mul_sub_le hW hT hTE hB hu hfin hx hσ ?_
  refine (Q.abs_reciprocal_sub_le hW ho ho0 hs hs0 hfin).trans (le_of_eq ?_)
  rw [hρ]
  field_simp

end Working.Quantizer

/-! ## NVFP4 in binary32 -/

/--
NVFP4 quantized in binary32, with the constants of torchao's `nvfp4_quantize`: the target `6`
(the largest E2M1 value), the floor `2 ^ -6` and the ceiling `448` of a stored scale (the least
normal and the largest E4M3 value). The scales are E4M3 words and the elements E2M1 words. A
quantizer without an outer scale is the one with the outer scale `1`, by which a division is
exact.
-/
def nvfp4Working : Working.Quantizer .binary32 .e4m3 .e2m1 where
  target := Model.ofNatBits 0x40C00000
  floor := Model.ofNatBits 0x3C800000
  ceiling := Model.ofNatBits 0x43E00000

/-- A value whose rational value is `q` has the real value `q`. -/
private theorem toReal_of_toRat? {fmt : FloatFormat} {x : Model fmt} {q : ℚ}
    (h : toRat? x = some q) : toReal x = (q : ℝ) := by
  rw [← cast_toRat_eq_toReal, h]
  rfl

/-- The target of NVFP4 in binary32 is finite and equal to `6`. -/
theorem nvfp4Working_target :
    isFinite nvfp4Working.target = true ∧ toReal nvfp4Working.target = 6 :=
  ⟨by decide +kernel, by
    rw [toReal_of_toRat? (q := 6) (by decide +kernel)]
    norm_num⟩

/-- The floor of a stored NVFP4 scale in binary32 is finite and equal to `2 ^ -6`. -/
theorem nvfp4Working_floor :
    isFinite nvfp4Working.floor = true ∧ toReal nvfp4Working.floor = 1 / 64 :=
  ⟨by decide +kernel, by
    rw [toReal_of_toRat? (q := 1 / 64) (by decide +kernel)]
    norm_num⟩

/-- The ceiling of a stored NVFP4 scale in binary32 is finite and equal to `448`. -/
theorem nvfp4Working_ceiling :
    isFinite nvfp4Working.ceiling = true ∧ toReal nvfp4Working.ceiling = 448 :=
  ⟨by decide +kernel, by
    rw [toReal_of_toRat? (q := 448) (by decide +kernel)]
    norm_num⟩

/-- Binary32 holds every finite E4M3 value exactly. -/
theorem cast_e4m3_binary32 {stored : Model FloatFormat.e4m3} (hs : isFinite stored = true) :
    isFinite (Model.cast .e4m3 .binary32 stored) = true ∧
      toReal (Model.cast .e4m3 .binary32 stored) = toReal stored := by
  refine Working.cast_exact_of_grid stored hs (by decide) (by decide) ?_
  rw [toReal_posMaxFinite_e4m3,
    toReal_posMaxFinite_of_eq .binary32 (significand := 16777215) (exponent := 104) (by decide)
      (by decide)]
  norm_num

/--
The block scale that NVFP4 stores in binary32, for a finite block and a finite positive outer
scale: with `a` the largest magnitude of the block and `g` the rounding onto the binary32 grid,
it is the E4M3 rounding of `g (g (a / 6) / outer)` clamped to `[2 ^ -6, 448]`. No premise
excludes an overflow of the second quotient.
-/
theorem nvfp4Working_toReal_scale {outer : Model FloatFormat.binary32}
    (ho : isFinite outer = true) (ho0 : 0 < toReal outer)
    {block : List (Model FloatFormat.binary32)} (hb : ∀ x ∈ block, isFinite x = true) :
    isFinite (nvfp4Working.scale outer block) = true ∧
      toReal (nvfp4Working.scale outer block) =
        (Rounding.saturating .e4m3).round (max (1 / 64) (min 448
          (roundAt .binary32 (roundAt .binary32 (toReal (Working.blockMax block) / 6) /
            toReal outer)))) := by
  have h := nvfp4Working.toReal_scale (by decide) nvfp4Working_target.1
    (by rw [nvfp4Working_target.2]; norm_num) nvfp4Working_floor.1
    (by rw [nvfp4Working_floor.2]; norm_num) nvfp4Working_ceiling.1
    (by rw [nvfp4Working_floor.2, nvfp4Working_ceiling.2]; norm_num)
    (by rw [nvfp4Working_ceiling.2, toReal_posMaxFinite_e4m3]) ho ho0 hb
  rwa [nvfp4Working_target.2, nvfp4Working_floor.2, nvfp4Working_ceiling.2] at h

/--
The element that NVFP4 stores in binary32, for a finite input and a finite reciprocal: the
saturating E2M1 rounding of the product rounded onto the binary32 grid. The clamp to `±6` is
absorbed by the saturation, and no premise excludes an overflow of the product.
-/
theorem nvfp4Working_toReal_element {r x : Model FloatFormat.binary32} (hr : isFinite r = true)
    (hx : isFinite x = true) :
    isFinite (nvfp4Working.element r x) = true ∧
      toReal (nvfp4Working.element r x) =
        (Rounding.saturating .e2m1).round (roundAt .binary32 (toReal x * toReal r)) := by
  have h := nvfp4Working.toReal_element (by decide) nvfp4Working_target.1
    (by rw [nvfp4Working_target.2]; norm_num)
    (by rw [nvfp4Working_target.2, toReal_posMaxFinite_e2m1]) hr hx
  rwa [nvfp4Working_target.2, ← toReal_posMaxFinite_e2m1, Rounding.saturating_round_clamp] at h

/--
Error of one NVFP4 element quantized in binary32, decoded at the total scale `σ = o * s` of a
finite positive outer scale `o` and a finite positive stored block scale `s`. When the
reciprocal that the quantizer computes is finite, the error is the E2M1 budget (a quarter of the
magnitude, a quarter of the scale, saturation at six times the scale) with the working error
`δ = (1 + u) * (1 + ρ) - 1` added to the relative part and to the saturating magnitude, and
`5 / 4` of the binary32 underflow error `θ` per unit of scale, for
`ρ = (1 + u) * (1 + (u + θ * o)) - 1 + θ * σ` and `u` the binary32 unit roundoff. The product of
an element with the reciprocal may overflow: the bound holds as it is.
-/
theorem nvfp4Working_abs_element_sub_le {outer : Model FloatFormat.binary32}
    (ho : isFinite outer = true) (ho0 : 0 < toReal outer) {stored : Model FloatFormat.e4m3}
    (hs : isFinite stored = true) (hs0 : 0 < toReal stored)
    (hfin : isFinite (nvfp4Working.reciprocal outer stored) = true)
    {x : Model FloatFormat.binary32} (hx : isFinite x = true) {ρ : ℝ}
    (hρ : ρ = (1 + unitRoundoffAt .binary32) *
        (1 + (unitRoundoffAt .binary32 + underflowErrorAt .binary32 * toReal outer)) - 1 +
      underflowErrorAt .binary32 * (toReal outer * toReal stored)) :
    |toReal (nvfp4Working.element (nvfp4Working.reciprocal outer stored) x) *
          (toReal outer * toReal stored) - toReal x| ≤
      (1 / 4 * (1 + ((1 + unitRoundoffAt .binary32) * (1 + ρ) - 1)) +
          ((1 + unitRoundoffAt .binary32) * (1 + ρ) - 1)) * |toReal x| +
        toReal outer * toReal stored * (1 / 4 + (1 + 1 / 4) * underflowErrorAt .binary32) +
        max 0 ((1 + ((1 + unitRoundoffAt .binary32) * (1 + ρ) - 1)) * |toReal x| +
          toReal outer * toReal stored * underflowErrorAt .binary32 -
          toReal outer * toReal stored * 6) := by
  obtain ⟨hc, hcr⟩ := cast_e4m3_binary32 hs
  have h := nvfp4Working.abs_element_sub_le (by decide) nvfp4Working_target.1
    (by rw [nvfp4Working_target.2, toReal_posMaxFinite_e2m1]) e2m1_budget (by norm_num) ho ho0
    hc (by rw [hcr]; exact hs0) hfin hx (ρ := ρ) (by rw [hcr]; exact hρ)
  rwa [hcr] at h

section NVFP4

variable {m n : ℕ} (outer block : Fin m × Fin n → ℕ × ℕ) (x : Fin m × Fin n → ℝ)
  (i : Fin m × Fin n)

/-- Binary32 arithmetic without overflow is accurate to its unit roundoff and half its least
subnormal. -/
theorem binary32_accurate :
    (Rounding.grid .binary32).Accurate (unitRoundoffAt .binary32) (underflowErrorAt .binary32) :=
  grid_accurate .binary32

/--
NVFP4 quantized in binary32 in the order of torchao's reference: each element is multiplied by a
reciprocal `r i` of its total scale, the product is rounded to binary32, and the result is
rounded to E2M1 with saturation. If `r i` is within `ρ / σ` of `1 / σ`, the error of the element
is the E2M1 budget (a quarter of the magnitude, a quarter of the scale, saturation at six times
the scale) with the working error `δ = (1 + u₃₂) * (1 + ρ) - 1` added to the relative part and
to the saturating magnitude, and `5 / 4` of the binary32 underflow error per unit of scale.
-/
theorem nvfp4_abs_reconstructWith_sub_le (r : Fin m × Fin n → ℝ) {ρ : ℝ}
    (hσ : 0 < (nvfp4 outer block).scale x i)
    (hr : |r i - 1 / (nvfp4 outer block).scale x i| ≤ ρ / (nvfp4 outer block).scale x i) :
    |(nvfp4 outer block).reconstructWith
        (fun x i => (Rounding.grid .binary32).round (x i * r i)) x i - x i| ≤
      (1 / 4 * (1 + ((1 + unitRoundoffAt .binary32) * (1 + ρ) - 1)) +
          ((1 + unitRoundoffAt .binary32) * (1 + ρ) - 1)) * |x i| +
        (nvfp4 outer block).scale x i * (1 / 4 + (1 + 1 / 4) * underflowErrorAt .binary32) +
        max 0 ((1 + ((1 + unitRoundoffAt .binary32) * (1 + ρ) - 1)) * |x i| +
          (nvfp4 outer block).scale x i * underflowErrorAt .binary32 -
          (nvfp4 outer block).scale x i * 6) :=
  (nvfp4 outer block).abs_reconstructWith_mul_sub_le (Rounding.grid .binary32) r x i e2m1_budget
    (by norm_num) binary32_accurate (unitRoundoffAt_pos .binary32).le hσ hr

/--
NVFP4: a quantizer that computes the scaled input in a working arithmetic stores the E2M1 value of
the exact quantizer at every element whose computed and exact scaled inputs lie between the same
two adjacent E2M1 values `a` and `b` and differ by less than the distance of the exact one to
their midpoint. E2M1 with saturation is a nearest rounding (`Rounding.saturating_nearest`).
-/
theorem nvfp4_quantizeWith_eq_quantize (input : (Fin m × Fin n → ℝ) → Fin m × Fin n → ℝ)
    {a b : ℝ} (ha : (Rounding.saturating .e2m1).Fixes a) (hb : (Rounding.saturating .e2m1).Fixes b)
    (hm : (Rounding.saturating .e2m1).round ((a + b) / 2) = a ∨
      (Rounding.saturating .e2m1).round ((a + b) / 2) = b)
    (hy : a ≤ (nvfp4 outer block).normalized x i ∧ (nvfp4 outer block).normalized x i ≤ b)
    (hy' : a ≤ input x i ∧ input x i ≤ b)
    (hclose : |input x i - (nvfp4 outer block).normalized x i| <
      |(nvfp4 outer block).normalized x i - (a + b) / 2|) :
    (nvfp4 outer block).quantizeWith input x i = (nvfp4 outer block).quantize x i :=
  (nvfp4 outer block).quantizeWith_eq_quantize input x i (Rounding.saturating_nearest .e2m1) ha hb
    hm hy hy' hclose

end NVFP4

end FloatLib.Floats.Formats.Block
