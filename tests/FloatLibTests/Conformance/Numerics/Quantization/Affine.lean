/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Automation
public meta import FloatLib.Numerics.Quantization

/-!
# Affine-quantization refinement check

The symbolic example checks that `numerics_refine` uses a supplied rounded-value equality for
an affine quantizer with scale `1 / 4` and signed eight-bit code bounds.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.Quantization.Affine

open FloatLib.Numerics.Quantization

private def int8Quarter : AffineQuantizer where
  scale := 1 / 4
  zeroPoint := 0
  qmin := -128
  qmax := 127
  scale_pos := by norm_num
  codeRange := by norm_num

attribute [numerics_reduction] int8Quarter

example {x expected : ℚ} (hround : int8Quarter.roundedValue x = expected) :
    AffineQuantizer.AtFinite int8Quarter expected :=
  numerics_refine (int8Quarter.quantizeCode x)

end FloatLibTests.Conformance.Numerics.Quantization.Affine
