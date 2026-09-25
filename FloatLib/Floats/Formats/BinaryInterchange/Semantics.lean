/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Special
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Finiteness
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.DivisionSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SqrtSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Constants
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Subtraction
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Addition
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Division
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.FiniteBounds
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Multiplication
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.SquareRoot
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Subtraction
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.BFloat16
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Sterbenz
public import FloatLib.Floats.Formats.BinaryInterchange.Status
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof

/-!
# Semantic theorems for format-parameterized executable floats

The binary semantic API combines the exact bit/model bridge, real interpretation, nearest-even
rounding, arithmetic refinement, symbolic no-overflow criteria, signed arithmetic,
arbitrary-format directed-rounding bounds, comparison semantics, extended-real min/max, interval
enclosure soundness, cross-format casts, finite arithmetic bridges to Lean's unpacked model,
generic error bounds, and exact-subtraction results.

Import the operation-specific `Arithmetic.Runtime` and `Operations.Runtime` modules when keeping
runtime dependencies narrow, or the `FloatLib.Floats.Formats.BinaryInterchange` family entry
point for the complete public API. Import this module for format-generic proofs.

## Packing

This module collects packing facts for special and finite values. Import the smaller modules
directly when only one representation class is needed.

## Arithmetic

This module exports extended-real lower and upper bounds for directed addition, subtraction,
multiplication, division, and square root on finite operands, subject to the stated domain
hypotheses. It also exports exactness of the implemented rounding directions on representable
dyadics. All proofs are parameterized by
`FloatFormat`.
-/
