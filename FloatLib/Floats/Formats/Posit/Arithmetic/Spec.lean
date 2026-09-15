/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof

/-!
# Exact reference arithmetic for standardized posits

These operations are the mathematical specifications for executable posit arithmetic.
Every finite operand is decoded to an exact `Rat`. Rational arithmetic is evaluated exactly
before one final rounding by the Posit Standard rule; square root uses the boundary comparisons
described below.

NaR is never interpreted as infinity. It propagates through the six core operations. Division by
zero and square root of a negative finite value produce NaR. Fused multiply-add computes the exact
rational expression `left * right + addend` and rounds only the final result.

Square root is also exact as a rounding decision: `roundSqrtRat` compares the rational
radicand against squared posit boundaries, so an irrational root never passes through an
approximate floating-point value.

Executable backends refine these definitions.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Sections 4--5, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.Spec

variable {format : Format}

/-- Exact addition followed by one standardized posit rounding. -/
@[inline] def add (left right : Model format) : Model format :=
  match left.toRat?, right.toRat? with
  | some leftValue, some rightValue =>
      roundRat format (leftValue + rightValue)
  | _, _ =>
      nar format

/-- Exact subtraction followed by one standardized posit rounding. -/
@[inline] def sub (left right : Model format) : Model format :=
  match left.toRat?, right.toRat? with
  | some leftValue, some rightValue =>
      roundRat format (leftValue - rightValue)
  | _, _ =>
      nar format

/-- Exact multiplication followed by one standardized posit rounding. -/
@[inline] def mul (left right : Model format) : Model format :=
  match left.toRat?, right.toRat? with
  | some leftValue, some rightValue =>
      roundRat format (leftValue * rightValue)
  | _, _ =>
      nar format

/--
Exact division followed by one standardized posit rounding.

The standard's real-number interpretation has no result for a zero divisor, so the operation
returns NaR in that case.
-/
@[inline] def div (left right : Model format) : Model format :=
  match left.toRat?, right.toRat? with
  | some leftValue, some rightValue =>
      if rightValue = 0 then
        nar format
      else
        roundRat format (leftValue / rightValue)
  | _, _ =>
      nar format

/--
Correctly rounded square root for the standardized real domain.

NaR and negative finite inputs produce NaR. Zero and positive inputs use exact rational boundary
comparisons.
-/
@[inline] def sqrt (value : Model format) : Model format :=
  match value.toRat? with
  | none =>
      nar format
  | some rational =>
      if rational < 0 then
        nar format
      else
        roundSqrtRat format rational

/-- Exact fused multiply-add with a single final standardized rounding. -/
@[inline] def fma (left right addend : Model format) : Model format :=
  match left.toRat?, right.toRat?, addend.toRat? with
  | some leftValue, some rightValue, some addendValue =>
      roundRat format (leftValue * rightValue + addendValue)
  | _, _, _ =>
      nar format

/-- NaR propagates from the left operand of specified addition. -/
@[simp] theorem add_nar_left (right : Model format) :
    add (nar format) right = nar format := by
  simp [add]

/-- NaR propagates from the right operand of specified addition. -/
@[simp] theorem add_nar_right (left : Model format) :
    add left (nar format) = nar format := by
  simp [add]

/-- NaR propagates from the left operand of specified subtraction. -/
@[simp] theorem sub_nar_left (right : Model format) :
    sub (nar format) right = nar format := by
  simp [sub]

/-- NaR propagates from the right operand of specified subtraction. -/
@[simp] theorem sub_nar_right (left : Model format) :
    sub left (nar format) = nar format := by
  simp [sub]

/-- NaR propagates from the left operand of specified multiplication. -/
@[simp] theorem mul_nar_left (right : Model format) :
    mul (nar format) right = nar format := by
  simp [mul]

/-- NaR propagates from the right operand of specified multiplication. -/
@[simp] theorem mul_nar_right (left : Model format) :
    mul left (nar format) = nar format := by
  simp [mul]

/-- NaR propagates from the dividend of specified division. -/
@[simp] theorem div_nar_left (right : Model format) :
    div (nar format) right = nar format := by
  simp [div]

/-- NaR propagates from the divisor of specified division. -/
@[simp] theorem div_nar_right (left : Model format) :
    div left (nar format) = nar format := by
  simp [div]

/-- Specified posit division by zero produces NaR. -/
@[simp] theorem div_zero_right (left : Model format) :
    div left (zero format) = nar format := by
  cases hleft : left.toRat? <;> simp [div, hleft]

/-- The specified square root of NaR is NaR. -/
@[simp] theorem sqrt_nar :
    sqrt (nar format) = nar format := by
  simp [sqrt]

/-- The specified square root preserves the unique posit zero. -/
@[simp] theorem sqrt_zero :
    sqrt (zero format) = zero format := by
  simp [sqrt]

/-- NaR propagates from the left multiplicand of specified FMA. -/
@[simp] theorem fma_nar_left (right addend : Model format) :
    fma (nar format) right addend = nar format := by
  simp [fma]

/-- NaR propagates from the right multiplicand of specified FMA. -/
@[simp] theorem fma_nar_right (left addend : Model format) :
    fma left (nar format) addend = nar format := by
  simp [fma]

/-- NaR propagates from the addend of specified FMA. -/
@[simp] theorem fma_nar_addend (left right : Model format) :
    fma left right (nar format) = nar format := by
  simp [fma]

end FloatLib.Floats.Formats.Posit.Model.Spec
