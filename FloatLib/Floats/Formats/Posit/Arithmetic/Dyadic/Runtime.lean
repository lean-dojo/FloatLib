/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Runtime

/-!
# Exact-dyadic posit arithmetic

Finite posit values are dyadic. These kernels therefore perform their exact intermediate work on
integer significands and binary exponents rather than constructing normalized rational operands.
Addition, subtraction, multiplication, division, square root, and fused multiply-add all round
once according to the Posit Standard (2022).

The equality proofs against the independent rational specification live in `Dyadic.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DyadicArithmetic

variable {format : Format}

/--
Exact integer addition followed by standardized posit rounding.

The dyadic operands are aligned at their smaller exponent and added as signed integers. Final
threshold comparisons remain in the exact dyadic domain.
-/
@[noinline] def add (left right : Model format) : Model format :=
  match left.toDyadic?, right.toDyadic? with
  | some leftValue, some rightValue =>
      DyadicRounding.round format
        (FloatLib.Numerics.Dyadic.add leftValue rightValue)
  | _, _ =>
      nar format

/--
Exact integer subtraction followed by standardized posit rounding.

Subtraction shares the exact dyadic alignment kernel with addition and performs no host
floating-point computation.
-/
@[noinline] def sub (left right : Model format) : Model format :=
  match left.toDyadic?, right.toDyadic? with
  | some leftValue, some rightValue =>
      DyadicRounding.round format
        (FloatLib.Numerics.Dyadic.sub leftValue rightValue)
  | _, _ =>
      nar format

/--
Exact integer multiplication followed by standardized posit rounding.

Compared with `Model.Spec.mul`, this forms one integer product and converts only that exact result
directly with the certified dyadic rounder; it allocates no rational operands.
-/
@[noinline] def mul (left right : Model format) : Model format :=
  match left.toDyadic?, right.toDyadic? with
  | some leftValue, some rightValue =>
      DyadicRounding.round format
        (FloatLib.Numerics.Dyadic.mul leftValue rightValue)
  | _, _ =>
      nar format

/--
Correctly rounded division through exact dyadic cross-multiplication.

The kernel never constructs a rational quotient. Candidate values and rounding thresholds are
multiplied by the positive divisor magnitude and compared directly with the dividend magnitude.
Division by zero and every NaR case retain the specification's NaR result.
-/
@[noinline] def div (left right : Model format) : Model format :=
  match left.toDyadic?, right.toDyadic? with
  | some numerator, some denominator =>
      DyadicQuotient.round format numerator denominator
  | _, _ =>
      nar format

/--
Correctly rounded square root through exact dyadic squared comparisons.

The result itself may be irrational, so this kernel never constructs it. Candidate and threshold
squares are compared directly with the decoded dyadic radicand.
-/
@[noinline] def sqrt (value : Model format) : Model format :=
  match value.toDyadic? with
  | none =>
      nar format
  | some radicand =>
      if radicand.isLess FloatLib.Numerics.Dyadic.zero then
        nar format
      else
        DyadicSquareRoot.round format radicand

/--
Exact fused multiply-add with one final standardized rounding.

Both multiplication and addition stay in the shared dyadic carrier. The exact result is converted
directly after accumulating the addend, preserving the specification's single-rounding semantics.
-/
@[noinline] def fma (left right addend : Model format) : Model format :=
  match left.toDyadic?, right.toDyadic?, addend.toDyadic? with
  | some leftValue, some rightValue, some addendValue =>
      DyadicRounding.round format
        (FloatLib.Numerics.Dyadic.add
          (FloatLib.Numerics.Dyadic.mul leftValue rightValue)
          addendValue)
  | _, _, _ =>
      nar format

end FloatLib.Floats.Formats.Posit.Model.DyadicArithmetic
