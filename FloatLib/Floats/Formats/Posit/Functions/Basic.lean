/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Deterministic.Rational
public import FloatLib.Floats.Formats.Posit.Comparison
public import FloatLib.Floats.Formats.Posit.Rounding.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof

/-!
# Basic posit functions

Absolute value, sign, integer rounding, and representation successor/predecessor from Section 5.2
of the 2022 Posit Standard. Negation is defined with the model.

`next` and `prior` wrap over the complete bit vector, including NaR, as specified by the standard.
Other posit-valued functions preserve NaR. Integer rounding uses exact rational decoding,
`Rat.floor` or `Rat.ceil`, and the shared posit rounder.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Sections 5.1--5.2, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/--
Lexicographic successor of the complete representation, wrapping modulo `2 ^ format.bits`.

Unlike ordinary real-valued functions, `next` does not propagate NaR: it advances from the NaR
word to the following encoded word.
-/
@[inline] def next (value : Model format) : Model format :=
  ofBits (value.bits + 1)

/--
Lexicographic predecessor of the complete representation, wrapping modulo `2 ^ format.bits`.

As required by the standard, this is the exact inverse of `next`, including at zero, NaR, and the
unsigned wrap boundary.
-/
@[inline] def prior (value : Model format) : Model format :=
  ofBits (value.bits - 1)

/-- Taking the predecessor after the successor recovers every encoded word. -/
@[simp] theorem prior_next (value : Model format) :
    prior (next value) = value := by
  apply congrArg ofBits
  change value.bits + 1 - 1 = value.bits
  exact BitVec.add_sub_cancel value.bits (1 : BitVec format.bits)

/-- Taking the successor after the predecessor recovers every encoded word. -/
@[simp] theorem next_prior (value : Model format) :
    next (prior value) = value := by
  apply congrArg ofBits
  change value.bits - 1 + 1 = value.bits
  exact BitVec.sub_add_cancel value.bits (1 : BitVec format.bits)

/--
Standard absolute value.

The encoded order places NaR below zero, but whole-word negation fixes NaR, so this definition also
has the required NaR propagation without assigning NaR a numerical sign.
-/
@[inline] def abs (value : Model format) : Model format :=
  if compareLess value (zero format) then neg value else value

/-- Absolute value fixes zero. -/
@[simp] theorem abs_zero (format : Format) :
    abs (zero format) = zero format := by
  simp [abs]

/-- Absolute value propagates NaR. -/
@[simp] theorem abs_nar (format : Format) :
    abs (nar format) = nar format := by
  rw [abs]
  by_cases hless : compareLess (nar format) (zero format)
  · simp [hless]
  · simp [hless]

/--
Standard sign function.

NaR is checked before encoded comparisons because NaR is the least *word* but has no numerical
sign. Positive and negative results are created by exact rounding of `±1`.
-/
@[inline] def sign (value : Model format) : Model format :=
  if value.isNaR then
    nar format
  else if compareLess (zero format) value then
    roundRat format 1
  else if compareLess value (zero format) then
    roundRat format (-1)
  else
    zero format

/-- The standard sign function fixes the canonical zero word. -/
@[simp] theorem sign_zero (format : Format) :
    sign (zero format) = zero format := by
  simp [sign]

/-- The standard sign function propagates NaR. -/
@[simp] theorem sign_nar (format : Format) :
    sign (nar format) = nar format := by
  simp [sign]

/-- The shared exact nearest-even integer rounder, exposed through the posit API. -/
@[inline] abbrev nearestEvenInteger (value : Rat) : Int :=
  FloatLib.Numerics.roundRatEven value

/-- An exact integer is unchanged by nearest-even integer rounding. -/
theorem nearestEvenInteger_int (value : Int) :
    nearestEvenInteger (value : Rat) = value :=
  FloatLib.Numerics.roundRatEven_intCast value

/-- Nearest integer-valued posit, with an even-integer tie rule and NaR propagation. -/
@[inline] def nearestInt (value : Model format) : Model format :=
  match value.toRat? with
  | none => nar format
  | some rational => roundRat format (nearestEvenInteger rational : Rat)

/-- Smallest integer-valued posit greater than or equal to the input, with NaR propagation. -/
@[inline] def ceil (value : Model format) : Model format :=
  match value.toRat? with
  | none => nar format
  | some rational => roundRat format (rational.ceil : Rat)

/-- Largest integer-valued posit less than or equal to the input, with NaR propagation. -/
@[inline] def floor (value : Model format) : Model format :=
  match value.toRat? with
  | none => nar format
  | some rational => roundRat format (rational.floor : Rat)

/-- Nearest-integer rounding propagates NaR. -/
@[simp] theorem nearestInt_nar (format : Format) :
    nearestInt (nar format) = nar format := by
  simp [nearestInt]

/-- Ceiling propagates NaR. -/
@[simp] theorem ceil_nar (format : Format) :
    ceil (nar format) = nar format := by
  simp [ceil]

/-- Floor propagates NaR. -/
@[simp] theorem floor_nar (format : Format) :
    floor (nar format) = nar format := by
  simp [floor]

/-- Nearest-integer rounding fixes the canonical zero word. -/
@[simp] theorem nearestInt_zero (format : Format) :
    nearestInt (zero format) = zero format := by
  rw [nearestInt, toRat?_zero]
  change roundRat format (nearestEvenInteger 0 : Rat) = zero format
  rw [show nearestEvenInteger (0 : Rat) = (0 : Int) by
    simpa using nearestEvenInteger_int (0 : Int)]
  exact roundRat_zero format

/-- Ceiling fixes the canonical zero word. -/
@[simp] theorem ceil_zero (format : Format) :
    ceil (zero format) = zero format := by
  rw [ceil, toRat?_zero]
  change roundRat format ((0 : Rat).ceil : Rat) = zero format
  rw [show (0 : Rat).ceil = 0 by
    simpa using Rat.ceil_intCast (0 : Int)]
  exact roundRat_zero format

/-- Floor fixes the canonical zero word. -/
@[simp] theorem floor_zero (format : Format) :
    floor (zero format) = zero format := by
  rw [floor, toRat?_zero]
  change roundRat format ((0 : Rat).floor : Rat) = zero format
  rw [show (0 : Rat).floor = 0 by
    simpa using Rat.floor_intCast (0 : Int)]
  exact roundRat_zero format

end FloatLib.Floats.Formats.Posit.Model
