/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.Codebook.Arithmetic.Proof
public import FloatLib.Floats.Formats.Codebook.Automation
public import FloatLib.Floats.Formats.Codebook.Configured.Catalog
public import FloatLib.Floats.Formats.Codebook.Configured.Proof
public import FloatLib.Floats.Formats.Codebook.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.Codebook.Configured.Conversion.Proof
public meta import FloatLib.Floats.Formats.Codebook.Configured.Info
public meta import FloatLib.Floats.Formats.Codebook.Info

/-!
# Exact-width lookup numerical systems

This is the public entry point for lookup-table numerical formats. It exports the generic
codebook representation, the supplied catalog, proved catalog arithmetic, the configured
`ExecFloat.Codebook` carrier, numerical automation, and `#float_info` support.

Import narrower submodules when defining another codebook family internally.

Unlike standardized interchange formats, a codebook is defined by its complete denotation table.
Consequently, the table itself is the authoritative format specification; FloatLib does not
silently infer arithmetic from bit width or element type.

## Reference

`Codebook.denote` specifies the meaning of every stored word, including exceptional entries.
`nearestCode` supplies nearest-entry quantization; catalog arithmetic is defined separately.
-/

@[expose] public section
