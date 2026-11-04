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
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel.MulDiv
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
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError
public import FloatLib.Floats.Formats.BinaryInterchange.Status
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof

/-!
# Semantic theorems for format-parameterized executable floats

Import this module when you prove things about binary formats in general. It gathers the
semantic half of the binary API: the exact bit/model bridge, real interpretation, nearest-even
rounding, arithmetic refinement, symbolic no-overflow criteria, signed arithmetic,
arbitrary-format directed-rounding bounds, comparison semantics, extended-real min/max, interval
enclosure soundness, cross-format casts, finite arithmetic bridges to Lean's unpacked model,
generic error bounds, mixed-error propagation, and exact-subtraction results.

If you want narrow runtime dependencies, import the operation-specific `Arithmetic.Runtime` and
`Operations.Runtime` modules. For the complete public API, use the
`FloatLib.Floats.Formats.BinaryInterchange` family entry point.

## Packing

Packing facts for special and finite values come in through this module too. When you need only
one representation class, import its smaller module.

## Arithmetic

For directed addition, subtraction, multiplication, division, and square root on finite
operands, this module exports extended-real lower and upper bounds, subject to the stated domain
hypotheses. It also exports exactness of the implemented rounding directions on representable
dyadics. Every proof is parameterized by `FloatFormat`.
-/
