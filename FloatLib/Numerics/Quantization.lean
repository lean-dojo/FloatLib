/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Affine
public import FloatLib.Numerics.Quantization.Deterministic
public import FloatLib.Numerics.Quantization.Directed
public import FloatLib.Numerics.Quantization.Ordered
public import FloatLib.Numerics.Quantization.Saturating
public import FloatLib.Numerics.Quantization.Spec
public import FloatLib.Numerics.Quantization.Stochastic

/-!
# Representation-independent quantization

Quantization combines relational specifications, deterministic arithmetic primitives,
order-directed specifications, explicit-entropy stochastic contracts, saturation, and an
executable affine rational quantizer.

Quantization remains separate from representability: a numerical system describes which values
its codes mean, while these modules describe which code or outcome a policy permits for a
particular exact input.
-/

@[expose] public section
