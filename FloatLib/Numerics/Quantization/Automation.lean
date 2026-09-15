/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Affine
public import FloatLib.Numerics.Automation.Numerics -- shake: keep
public import Mathlib.Tactic.NormNum

/-!
# Affine-quantization rules for numerical automation

Symbolic refinement uses the generic quantizer contract. Closed evaluation unfolds the exact
rational kernel only during the explicit reduction phase.
-/

public meta section

namespace FloatLib.Numerics.Quantization

attribute [numerics_simps]
  AffineQuantizer.numericalSystem_represents_iff

attribute [aesop safe apply (rule_sets := [Numerics])]
  AffineQuantizer.quantizeCode_quantizerOn_roundedValue

attribute [numerics_reduction]
  roundQuotientEven
  roundRatEven
  Saturating.clamp
  AffineQuantizer.clampCode
  AffineQuantizer.rawCode
  AffineQuantizer.quantize
  AffineQuantizer.dequantize
  AffineQuantizer.roundedValue
  AffineQuantizer.quantizeCode
  AffineQuantizer.numericalSystem

end FloatLib.Numerics.Quantization
