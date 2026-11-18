/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Catalog
public import FloatLib.Numerics.Quantization.Block.Working

/-!
# NVFP4 quantization with binary32 working products

These are instances of the general working-arithmetic error and agreement theorems.
The grid models no overflow; the reciprocal scale error remains an explicit premise.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Floats.Formats.BinaryInterchange.Model

section NVFP4

variable {m n : ℕ} (outer block : Fin m × Fin n → ℕ × ℕ) (x : Fin m × Fin n → ℝ)
  (i : Fin m × Fin n)

/-- Binary32 arithmetic without overflow is accurate to its unit roundoff and half its least
subnormal. -/
theorem binary32_accurate :
    (Rounding.grid .binary32).Accurate (unitRoundoffAt .binary32) (underflowErrorAt .binary32) :=
  Rounding.accurate_of_budget (Rounding.grid_budget .binary32)

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
