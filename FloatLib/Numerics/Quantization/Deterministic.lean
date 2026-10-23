/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Deterministic.Quotient
public import FloatLib.Numerics.Quantization.Deterministic.ShiftRight
public import FloatLib.Numerics.Quantization.Deterministic.MagnitudeRounding
public import FloatLib.Numerics.Quantization.Deterministic.ModularPower
public import FloatLib.Numerics.Quantization.Deterministic.Rational

/-!
# Deterministic executable quantization primitives

Deterministic quantization primitives include nearest-even quotient, shift, and rational
rounding, the four magnitude rounding rules for shifts and quotients, and bounded modular
exponentiation. Import an individual submodule when only one primitive family is needed.
-/

@[expose] public section
