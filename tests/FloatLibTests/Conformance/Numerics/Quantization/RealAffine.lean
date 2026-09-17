/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Affine

/-!
# Real affine quantization and executable refinement

These examples exercise arbitrary valid rounding rules, exact rational embedding, both signs of
nearest-even ties, and saturation at both endpoints. Finite checks use kernel reduction rather
than native proof evaluation.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.Quantization.RealAffine

open FloatLib.Numerics FloatLib.Numerics.Quantization FloatLib.Floats.Formats.Flocq

private def shifted : AffineQuantizer where
  scale := 1 / 2
  zeroPoint := 3
  qmin := -4
  qmax := 7
  scale_pos := by norm_num
  codeRange := by norm_num

example : shifted.quantize (1 / 4) = 3 := by decide +kernel
example : shifted.quantize (3 / 4) = 5 := by decide +kernel
example : shifted.quantize (-1 / 4) = 3 := by decide +kernel
example : shifted.quantize (-3 / 4) = 1 := by decide +kernel
example : shifted.quantize 100 = 7 := by decide +kernel
example : shifted.quantize (-100) = -4 := by decide +kernel

example (q : AffineQuantizer) (x : ℚ) :
    q.toReal.quantize nearestEven (x : ℝ) = q.quantize x :=
  affine_toReal_quantize q x

example (q : AffineQuantizer) (x : ℚ) :
    q.toReal.roundedValue nearestEven (x : ℝ) = (q.roundedValue x : ℝ) :=
  affine_toReal_roundedValue q x

example (q : RealAffineQuantizer) : Monotone (q.quantize floorRound) :=
  affine_quantize_monotone q floorRound

example (q : RealAffineQuantizer) (code : ℤ)
    (hlo : q.qmin ≤ code) (hhi : code ≤ q.qmax) :
    q.quantize ceilRound (q.dequantize code) = code :=
  affine_quantize_dequantize q ceilRound hlo hhi

example (q : RealAffineQuantizer) (x : ℝ)
    (hlo : q.qmin ≤ q.rawCode nearestEven x) (hhi : q.rawCode nearestEven x ≤ q.qmax) :
    |q.roundedValue nearestEven x - x| ≤ q.scale / 2 :=
  affine_dequantize_quantize_error_le_half q nearestEven x hlo hhi

example (q : RealAffineQuantizer) (rnd : ℝ → ℤ) (x ε : ℝ)
    (hround : |(rnd (x / q.scale) : ℝ) - x / q.scale| ≤ ε) :
    |q.dequantize (q.rawCode rnd x) - x| ≤ q.scale * ε :=
  q.dequantize_rawCode_error_le rnd x ε hround

end FloatLibTests.Conformance.Numerics.Quantization.RealAffine
