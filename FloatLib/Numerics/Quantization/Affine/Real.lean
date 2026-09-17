/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Affine
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Affine quantization over the reals

`RealAffineQuantizer` describes a positive-scale integer grid with bounded storage. Its rounding
function is supplied by the caller: order preservation, integer round trips, and error bounds
each require only the corresponding property of that function. In particular, the error result
is not restricted to nearest-even rounding.

`AffineQuantizer.toReal` embeds the executable rational quantizer's parameters without changing
the code interval. `toReal_quantize` and `toReal_roundedValue` transport any agreement between
rational and real integer rounding to the complete saturated operation. The Flocq rounding
adapter specializes this agreement to nearest-even; executable clients can continue importing
`Affine` alone without loading real-number theory.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization

/-- A bounded affine grid with real-valued spacing and caller-supplied integer rounding. -/
structure RealAffineQuantizer where
  /-- Distance between adjacent reconstructed values. -/
  scale : ℝ
  /-- Integer code whose reconstruction is zero. It need not be inside the storage interval. -/
  zeroPoint : ℤ
  /-- Smallest stored code. -/
  qmin : ℤ
  /-- Largest stored code. -/
  qmax : ℤ
  /-- The grid spacing is strictly positive. -/
  scale_pos : 0 < scale
  /-- The storage interval is nonempty. -/
  codeRange : qmin ≤ qmax

namespace RealAffineQuantizer

/-- Saturate an integer to the storage interval using the shared clamp. -/
def clampCode (q : RealAffineQuantizer) (code : ℤ) : ℤ :=
  Saturating.clamp q.qmin q.qmax code

/-- Integer code before saturation. -/
noncomputable def rawCode (q : RealAffineQuantizer) (rnd : ℝ → ℤ) (x : ℝ) : ℤ :=
  rnd (x / q.scale) + q.zeroPoint

/-- Round onto the affine grid and saturate to the storage interval. -/
noncomputable def quantize (q : RealAffineQuantizer) (rnd : ℝ → ℤ) (x : ℝ) : ℤ :=
  q.clampCode (q.rawCode rnd x)

/-- Reconstruct the real value denoted by an integer code. -/
noncomputable def dequantize (q : RealAffineQuantizer) (code : ℤ) : ℝ :=
  q.scale * ((code - q.zeroPoint : ℤ) : ℝ)

/-- Reconstructed value after rounding and saturation. -/
noncomputable def roundedValue (q : RealAffineQuantizer) (rnd : ℝ → ℤ) (x : ℝ) : ℝ :=
  q.dequantize (q.quantize rnd x)

/-- Saturation always produces a code in the declared interval. -/
theorem clampCode_mem (q : RealAffineQuantizer) (code : ℤ) :
    q.qmin ≤ q.clampCode code ∧ q.clampCode code ≤ q.qmax :=
  ⟨Saturating.lower_le_clamp _ _ _, Saturating.clamp_le_upper q.codeRange⟩

/-- Saturation fixes every code already in the storage interval. -/
@[simp] theorem clampCode_eq_self (q : RealAffineQuantizer) {code : ℤ}
    (hlo : q.qmin ≤ code) (hhi : code ≤ q.qmax) : q.clampCode code = code :=
  Saturating.clamp_eq_self hlo hhi

/-- Every quantized value lies in the storage interval, independently of the rounding rule. -/
theorem quantize_mem (q : RealAffineQuantizer) (rnd : ℝ → ℤ) (x : ℝ) :
    q.qmin ≤ q.quantize rnd x ∧ q.quantize rnd x ≤ q.qmax :=
  q.clampCode_mem _

/-- The zero point reconstructs to zero, even if it lies outside the storage interval. -/
@[simp] theorem dequantize_zeroPoint (q : RealAffineQuantizer) :
    q.dequantize q.zeroPoint = 0 := by
  simp [dequantize]

/-- A monotone integer rounder gives monotone saturated quantization. -/
theorem quantize_monotone (q : RealAffineQuantizer) {rnd : ℝ → ℤ}
    (hmono : Monotone rnd) : Monotone (q.quantize rnd) := by
  intro x y hxy
  apply max_le_max le_rfl
  apply min_le_min le_rfl
  simpa [rawCode, add_comm] using
    add_le_add_right (hmono (div_le_div_of_nonneg_right hxy q.scale_pos.le)) q.zeroPoint

/-- Reconstruction preserves integer-code order because the scale is positive. -/
theorem dequantize_strictMono (q : RealAffineQuantizer) : StrictMono q.dequantize := by
  intro x y hxy
  apply mul_lt_mul_of_pos_left _ q.scale_pos
  exact_mod_cast sub_lt_sub_right hxy q.zeroPoint

/-- A rounder that fixes integers preserves in-range codes under reconstruction and rounding. -/
@[simp] theorem quantize_dequantize (q : RealAffineQuantizer) {rnd : ℝ → ℤ}
    (hfix : ∀ n : ℤ, rnd n = n) {code : ℤ}
    (hlo : q.qmin ≤ code) (hhi : code ≤ q.qmax) :
    q.quantize rnd (q.dequantize code) = code := by
  have hscaled : q.dequantize code / q.scale = ((code - q.zeroPoint : ℤ) : ℝ) := by
    simp [dequantize, ne_of_gt q.scale_pos]
  rw [quantize, rawCode, hscaled, hfix, sub_add_cancel]
  exact q.clampCode_eq_self hlo hhi

/-- An integer-rounding error bound scales by the spacing of the affine grid. -/
theorem dequantize_rawCode_error_le (q : RealAffineQuantizer) (rnd : ℝ → ℤ)
    (x ε : ℝ) (hround : |(rnd (x / q.scale) : ℝ) - x / q.scale| ≤ ε) :
    |q.dequantize (q.rawCode rnd x) - x| ≤ q.scale * ε := by
  have hscale : q.scale ≠ 0 := ne_of_gt q.scale_pos
  have hrewrite : q.dequantize (q.rawCode rnd x) - x =
      q.scale * ((rnd (x / q.scale) : ℝ) - x / q.scale) := by
    simp only [dequantize, rawCode, Int.cast_sub, Int.cast_add]
    field_simp
    ring
  rw [hrewrite, abs_mul, abs_of_pos q.scale_pos]
  exact mul_le_mul_of_nonneg_left hround q.scale_pos.le

/-- Without clipping, an integer-rounding error bound scales by the grid spacing. -/
theorem dequantize_quantize_error_le (q : RealAffineQuantizer) (rnd : ℝ → ℤ)
    (x ε : ℝ) (hround : |(rnd (x / q.scale) : ℝ) - x / q.scale| ≤ ε)
    (hlo : q.qmin ≤ q.rawCode rnd x) (hhi : q.rawCode rnd x ≤ q.qmax) :
    |q.roundedValue rnd x - x| ≤ q.scale * ε := by
  rw [roundedValue, quantize, q.clampCode_eq_self hlo hhi]
  exact q.dequantize_rawCode_error_le rnd x ε hround

/-- Without clipping, nearest integer rounding reconstructs within half a grid step. -/
theorem dequantize_quantize_error_le_half (q : RealAffineQuantizer) (rnd : ℝ → ℤ)
    (x : ℝ) (hround : |(rnd (x / q.scale) : ℝ) - x / q.scale| ≤ 1 / 2)
    (hlo : q.qmin ≤ q.rawCode rnd x) (hhi : q.rawCode rnd x ≤ q.qmax) :
    |q.roundedValue rnd x - x| ≤ q.scale / 2 := by
  simpa only [mul_one_div] using
    q.dequantize_quantize_error_le rnd x (1 / 2) hround hlo hhi

end RealAffineQuantizer

namespace AffineQuantizer

/-- View an executable rational grid as a real grid with the same integer codes. -/
noncomputable def toReal (q : AffineQuantizer) : RealAffineQuantizer where
  scale := q.scale
  zeroPoint := q.zeroPoint
  qmin := q.qmin
  qmax := q.qmax
  scale_pos := Rat.cast_pos_of_pos q.scale_pos
  codeRange := q.codeRange

/-- Reconstruction commutes with the exact rational-to-real embedding. -/
@[simp] theorem toReal_dequantize (q : AffineQuantizer) (code : ℤ) :
    q.toReal.dequantize code = (q.dequantize code : ℝ) := by
  simp [toReal, RealAffineQuantizer.dequantize, dequantize]

/-- Agreement of integer rounding lifts to affine quantization, including saturation. -/
theorem toReal_quantize (q : AffineQuantizer) (rnd : ℝ → ℤ)
    (hround : ∀ x : ℚ, rnd x = roundRatEven x) (x : ℚ) :
    q.toReal.quantize rnd x = q.quantize x := by
  unfold RealAffineQuantizer.quantize RealAffineQuantizer.rawCode toReal
  rw [← Rat.cast_div, hround]
  rfl

/-- Reconstruction commutes with exact embedding whenever integer rounding does. -/
theorem toReal_roundedValue (q : AffineQuantizer) (rnd : ℝ → ℤ)
    (hround : ∀ x : ℚ, rnd x = roundRatEven x) (x : ℚ) :
    q.toReal.roundedValue rnd x = (q.roundedValue x : ℝ) := by
  rw [RealAffineQuantizer.roundedValue, q.toReal_quantize rnd hround, toReal_dequantize]
  rfl

end AffineQuantizer

end FloatLib.Numerics.Quantization
