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

Here are the deterministic quantization primitives: nearest-even quotient, shift, and rational
rounding, the four magnitude rounding rules for shifts and quotients, and bounded modular
exponentiation. Import a single submodule if you need only one primitive family.
-/

@[expose] public section
