/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Adjacent.Proof.Boundaries
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Adjacent.Proof.Classification
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.EReal
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.MatmulProof
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.Exponent
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.InvalidSignals
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.Remainder
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.RoundToIntegral.Real

/-!
# Contracts for standard binary operations

Import this file for the contracts of the standard operations: comparison, adjacent values,
mixed-precision accumulation and matrix multiplication, IEEE remainder, integral rounding,
exponent operations, and the `invalid` flags of the selection operations.
-/
