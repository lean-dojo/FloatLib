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

These are the 8-bit formats with no infinity at all. Each one is its own nominal type, stored in a
single byte and run through the common executable interface. Both formats exported here are FNUZ
variants from the ONNX float8 conventions, so they keep one NaN code and have only an unsigned zero.

## Reference

* ONNX, *Float stored in 8 bits*,
  <https://onnx.ai/onnx/technical/float8.html>.
-/

@[expose] public section
