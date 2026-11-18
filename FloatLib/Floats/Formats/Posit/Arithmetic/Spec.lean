/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof

/-!
# Exact reference arithmetic for standardized posits

Executable posit arithmetic refines the definitions in this file, so they are the mathematical
meaning of every posit operation. Each finite operand is decoded to an exact `Rat`, the arithmetic
happens exactly in the rationals, and one final rounding applies the Posit Standard rule. Square
root needs the boundary comparisons described below, because its exact result can be irrational.

Exceptional values follow three rules:

* NaR is never interpreted as infinity, and it propagates through the six core operations.
* Division by zero gives NaR, and so does the square root of a negative finite value.
* Fused multiply-addition computes the exact rational expression `left * right + addend` and rounds
  only the final result.

For square root the rounding decision is exact too. `roundSqrtRat` compares the rational radicand
against squared posit boundaries, so an irrational root never passes through an approximate
floating-point value.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Sections 4--5, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.Spec

variable {format : Format}

/-- Posit Standard (2022), §5.4: exact addition rounded once; NaR propagates. -/
@[inline] def addition (left right : Model format) : Model format :=
  match left.toRat?, right.toRat? with
  | some leftValue, some rightValue =>
      roundRat format (leftValue + rightValue)
  | _, _ =>
      nar format

/--
Posit Standard (2022), §5.4: exact subtraction rounded once; NaR propagates.
-/
@[inline] def subtraction (left right : Model format) : Model format :=
  match left.toRat?, right.toRat? with
  | some leftValue, some rightValue =>
      roundRat format (leftValue - rightValue)
  | _, _ =>
      nar format

/--
Posit Standard (2022), §5.4: exact multiplication rounded once; NaR propagates.
-/
@[inline] def multiplication (left right : Model format) : Model format :=
  match left.toRat?, right.toRat? with
  | some leftValue, some rightValue =>
      roundRat format (leftValue * rightValue)
  | _, _ =>
      nar format

/--
Posit Standard (2022), §5.4: exact division followed by one rounding.

The standard's real-number interpretation has no result for a zero divisor, so the operation
returns NaR in that case.
-/
@[inline] def division (left right : Model format) : Model format :=
  match left.toRat?, right.toRat? with
  | some leftValue, some rightValue =>
      if rightValue = 0 then
        nar format
      else
        roundRat format (leftValue / rightValue)
  | _, _ =>
      nar format

/--
Posit Standard (2022), §5.5: correctly rounded square root.

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

/--
FloatLib FMA extension with Posit Standard (2022), §4.1 rounding.
The exact fused multiply-addition rounds once, and NaR propagates.
-/
@[inline] def fma (left right addend : Model format) : Model format :=
  match left.toRat?, right.toRat?, addend.toRat? with
  | some leftValue, some rightValue, some addendValue =>
      roundRat format (leftValue * rightValue + addendValue)
  | _, _, _ =>
      nar format

/-- NaR propagates from the left operand of specified addition. -/
@[simp] theorem add_nar_left (right : Model format) :
    addition (nar format) right = nar format := by
  simp [addition]

/-- NaR propagates from the right operand of specified addition. -/
@[simp] theorem add_nar_right (left : Model format) :
    addition left (nar format) = nar format := by
  simp [addition]

/-- NaR propagates from the left operand of specified subtraction. -/
@[simp] theorem sub_nar_left (right : Model format) :
    subtraction (nar format) right = nar format := by
  simp [subtraction]

/-- NaR propagates from the right operand of specified subtraction. -/
@[simp] theorem sub_nar_right (left : Model format) :
    subtraction left (nar format) = nar format := by
  simp [subtraction]

/-- NaR propagates from the left operand of specified multiplication. -/
@[simp] theorem mul_nar_left (right : Model format) :
    multiplication (nar format) right = nar format := by
  simp [multiplication]

/-- NaR propagates from the right operand of specified multiplication. -/
@[simp] theorem mul_nar_right (left : Model format) :
    multiplication left (nar format) = nar format := by
  simp [multiplication]

/-- NaR propagates from the dividend of specified division. -/
@[simp] theorem div_nar_left (right : Model format) :
    division (nar format) right = nar format := by
  simp [division]

/-- NaR propagates from the divisor of specified division. -/
@[simp] theorem div_nar_right (left : Model format) :
    division left (nar format) = nar format := by
  simp [division]

/-- Specified posit division by zero produces NaR. -/
@[simp] theorem div_zero_right (left : Model format) :
    division left (zero format) = nar format := by
  cases hleft : left.toRat? <;> simp [division, hleft]

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
