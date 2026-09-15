/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange
public import FloatLib.Floats.Formats.Block
public import FloatLib.Floats.Formats.Codebook
public import FloatLib.Floats.Formats.DecimalInterchange
public import FloatLib.Floats.Formats.FiniteOnly
public import FloatLib.Floats.Formats.FixedPoint
public import FloatLib.Floats.Formats.Flocq
public import FloatLib.Floats.Formats.IEEE754
public import FloatLib.Floats.Formats.Logarithmic
public import FloatLib.Floats.Formats.OCP
public import FloatLib.Floats.Formats.P3109
public import FloatLib.Floats.Formats.Posit

/-!
# Executable numerical format families

Each family defines its representation, mathematical interpretation, and supported operations.
`ExecFloat` supplies the common carrier and operation interfaces. External conformance checks
live in the separate `tests` package.
-/

@[expose] public section
