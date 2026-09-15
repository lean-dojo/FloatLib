/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Semantics.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime

/-!
# Executable standard posit quire operations

Quire arithmetic implements the operations of Posit Standard (2022), §5.11. Every accumulation
kernel works on the signed fixed-point coefficient. Posit operands decode to the shared exact
dyadic carrier and are shifted directly to the quire's fixed scale. No operation normalizes
through `Rat`.

The standard reserves the most-negative quire word for NaR. Consequently every checked result
uses `Model.ofCoefficient`: NaR propagates, and either signed overflow or a result equal to the
reserved word produces quire NaR.

The exact coefficient, dyadic, and rational refinement theorems live in `Arithmetic.Proof`.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Section 5.11, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Quire.Model

variable {format : Format}

/--
Add an exact dyadic increment to an ordinary quire.

This shared integer kernel underlies posit addition and fused product accumulation. The function
is total and produces quire NaR in three cases: the accumulator is NaR, the increment's stored
exponent is below the quire scale, or the exact coefficient sum is not an ordinary quire
coefficient. The exponent check is sufficient for alignment; it can reject an otherwise aligned
dyadic with trailing zeros in its significand. Decoded ordinary posits and their exact products
always pass this check, so it only restricts direct callers of this kernel.
-/
@[inline] def addDyadic
    (accumulator : Model format)
    (increment : FloatLib.Numerics.Dyadic) : Model format :=
  if accumulator.isNaR then
    nar format
  else if increment.exponent < scaleExponent format then
    nar format
  else
    ofCoefficient format
      (accumulator.coefficient + coefficientOfDyadic format increment)

/-- Convert a posit into the exact quire associated with the same descriptor. -/
@[inline] def pToQ
    (value : FloatLib.Floats.Formats.Posit.Model format) : Model format :=
  match value.toDyadic? with
  | some dyadic =>
      ofCoefficient format (coefficientOfDyadic format dyadic)
  | none =>
      nar format

/-- Negate an ordinary quire; quire NaR remains quire NaR. -/
@[inline] def qNegate (value : Model format) : Model format :=
  if value.isNaR then
    nar format
  else
    ofCoefficient format (-value.coefficient)

/-- Absolute value of an ordinary quire; quire NaR remains quire NaR. -/
@[inline] def qAbs (value : Model format) : Model format :=
  if value.isNaR then
    nar format
  else if value.coefficient < 0 then
    qNegate value
  else
    value

/-- Add one posit exactly to a quire, producing NaR on exceptional input or quire overflow. -/
@[inline] def qAddP
    (accumulator : Model format)
    (addend : FloatLib.Floats.Formats.Posit.Model format) : Model format :=
  match addend.toDyadic? with
  | some dyadic => addDyadic accumulator dyadic
  | none => nar format

/-- Subtract one posit exactly from a quire. -/
@[inline] def qSubP
    (accumulator : Model format)
    (subtrahend : FloatLib.Floats.Formats.Posit.Model format) : Model format :=
  match subtrahend.toDyadic? with
  | some dyadic => addDyadic accumulator dyadic.neg
  | none => nar format

/-- Add two quires exactly, returning quire NaR on NaR input or signed overflow. -/
@[inline] def qAddQ (left right : Model format) : Model format :=
  if left.isNaR || right.isNaR then
    nar format
  else
    ofCoefficient format (left.coefficient + right.coefficient)

/-- Subtract two quires exactly, returning quire NaR on NaR input or signed overflow. -/
@[inline] def qSubQ (left right : Model format) : Model format :=
  if left.isNaR || right.isNaR then
    nar format
  else
    ofCoefficient format (left.coefficient - right.coefficient)

/--
Accumulate one exact posit product with no intermediate rounding.

Both posit operands must use the same `format` as the quire, enforced by the type.
-/
@[inline] def qMulAdd
    (accumulator : Model format)
    (left right : FloatLib.Floats.Formats.Posit.Model format) : Model format :=
  match left.toDyadic?, right.toDyadic? with
  | some leftValue, some rightValue =>
      addDyadic accumulator
        (FloatLib.Numerics.Dyadic.mul leftValue rightValue)
  | _, _ =>
      nar format

/-- Subtract one exact posit product from a quire with no intermediate rounding. -/
@[inline] def qMulSub
    (accumulator : Model format)
    (left right : FloatLib.Floats.Formats.Posit.Model format) : Model format :=
  match left.toDyadic?, right.toDyadic? with
  | some leftValue, some rightValue =>
      addDyadic accumulator
        (FloatLib.Numerics.Dyadic.mul leftValue rightValue).neg
  | _, _ =>
      nar format

/--
Round a quire once to its associated posit.

The ordinary path turns the fixed-point coefficient into a shared dyadic and applies the
Posit Standard (2022) rounder, without constructing a `Rat`.
-/
@[inline] def qToP (value : Model format) :
    FloatLib.Floats.Formats.Posit.Model format :=
  match value.toDyadic? with
  | some dyadic => FloatLib.Floats.Formats.Posit.Model.DyadicRounding.round format dyadic
  | none => FloatLib.Floats.Formats.Posit.Model.nar format

end FloatLib.Floats.Formats.Posit.Quire.Model
