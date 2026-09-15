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

Binary, decimal, posit, P3109, fixed-point, logarithmic, codebook, block, complex, and interval APIs.
`ExecFloat` provides the common carrier and operation contracts. Each family under `Formats`
defines its encoding, mathematical interpretation, and arithmetic implementations.

Import `FloatLib.Floats.Formats.<Family>` for one family. New format-independent algorithms belong
under `FloatLib.Kernels`; definitions and theorems about numerical systems belong under
`FloatLib.Numerics`. Optional Arb comparisons are in `FloatLibTests.Arb.Oracle`.
-/

@[expose] public section
