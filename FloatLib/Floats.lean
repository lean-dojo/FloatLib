/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Numerics
public import FloatLib.Kernels
public import FloatLib.Floats.ExecFloat
public import FloatLib.Floats.Formats
public import FloatLib.Floats.Interval

/-!
# Executable numerical formats

This is the part of FloatLib you compute with: the binary, decimal, posit, P3109, fixed-point,
logarithmic, codebook, block, complex, and interval APIs. `ExecFloat` gives them a common carrier
and common operation contracts, and each family under `Formats` defines its own encoding, its
mathematical interpretation, and its arithmetic implementations. If you only need one family, import
`FloatLib.Floats.Formats.<Family>`.

Code that doesn't depend on a format lives elsewhere. New format-independent algorithms belong under
`FloatLib.Kernels`, and definitions and theorems about numerical systems belong under
`FloatLib.Numerics`. Optional Arb comparisons are in `FloatLibTests.Arb.Oracle`.
-/

@[expose] public section
