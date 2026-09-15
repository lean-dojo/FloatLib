/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FiniteOnly.E4M3FNUZ
public import FloatLib.Floats.Formats.FiniteOnly.E5M2FNUZ

/-!
# Finite-only floating-point formats

Nominal, byte-backed executable packages for formats that do not represent infinity. The FNUZ
variants exported here retain a NaN code and use unsigned zero, following the ONNX float8
conventions.

## Reference

* ONNX, *Float stored in 8 bits*,
  <https://onnx.ai/onnx/technical/float8.html>.
-/

@[expose] public section
