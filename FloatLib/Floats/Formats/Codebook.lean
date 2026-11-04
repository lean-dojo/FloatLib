/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.Codebook.Arithmetic.Proof
public import FloatLib.Floats.Formats.Codebook.Automation
public import FloatLib.Floats.Formats.Codebook.Configured.Catalog
public import FloatLib.Floats.Formats.Codebook.Configured.Display
public import FloatLib.Floats.Formats.Codebook.Configured.Proof
public import FloatLib.Floats.Formats.Codebook.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.Codebook.Configured.Conversion.Proof
public meta import FloatLib.Floats.Formats.Codebook.Configured.Info
public meta import FloatLib.Floats.Formats.Codebook.Info

/-!
# Exact-width lookup numerical systems

A codebook format is a lookup table. Each stored word means whatever its table entry says, so the
two-bit ternary code in the catalog maps `00`, `01` and `10` to `0`, `+1` and `-1` and keeps `11`
reserved. The table is the whole format specification, and FloatLib never infers arithmetic from
the bit width or the element type.

This module is the public entry point. It exports the generic codebook representation, the
supplied catalog with its proved arithmetic, the configured `ExecFloat.Codebook` carrier, numerical
automation, and `#float_info` support. If you're defining another codebook family inside the
library, import the narrower submodules.

## Reference

`Codebook.denote` specifies the meaning of every stored word, including exceptional entries.
`nearestCode` supplies nearest-entry quantization, and catalog arithmetic lives in
`Codebook.Arithmetic`.
-/

@[expose] public section
