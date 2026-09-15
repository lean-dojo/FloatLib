/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Adjacent.Proof.Boundaries
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Adjacent.Proof.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.MatmulProof
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.Exponent
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.InvalidSignals
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.Remainder
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.RoundToIntegral

/-!
# Contracts for standard binary operations

The standard-operation contracts cover comparison, adjacent values, mixed-precision accumulation
and matrix multiplication, IEEE remainder, integral rounding, exponent operations, and the
`invalid` flags of selection operations.
-/
