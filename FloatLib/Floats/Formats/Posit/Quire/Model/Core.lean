/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Descriptor
public import FloatLib.Numerics.Exact.Dyadic.Basic
public import FloatLib.Numerics.Representations.FixedInt.Core

/-!
# Executable standard posit quire model

Each `n`-bit posit gets one `16n`-bit quire in the Posit Standard (2022). It holds a signed
two's-complement coefficient whose least significant bit is worth `2^(16 - 8n)`, the square of the
smallest positive posit, and its most negative word is reserved for quire NaR. For `Posit32` that
means 512 bits at a scale of `2^(-240)`.

This module holds the representation, the executable constructors and classifiers, and the
integer and dyadic conversion kernels, and nothing more. Their range and denotational theorems are
in `Model.Proof`.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Sections 3.4 and 5.11, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Quire

open FloatLib.Numerics
open FloatLib.Numerics.Representations

/-- The standard quire width associated with an `n`-bit posit. -/
@[inline] def width (format : Format) : Nat :=
  16 * format.bits

/-- Binary scale of the quire's least-significant bit. -/
@[inline] def scaleExponent (format : Format) : Int :=
  16 - 8 * Int.ofNat format.bits

/-- Exact standard quire word for one posit descriptor. -/
structure Model (format : Format) where
  /-- Complete signed fixed-point word. -/
  word : FixedInt (width format)
  deriving DecidableEq, Repr

namespace Model

variable {format : Format}

/-- Construct a standard quire from its complete unsigned word. -/
@[inline] def ofNatBits (format : Format) (bits : Nat) : Model format :=
  ⟨FixedInt.ofNatBits bits⟩

/-- Read the standard quire's complete word as an unsigned natural number. -/
@[inline] def toNatBits (value : Model format) : Nat :=
  value.word.toNatBits

/-- Read the signed two's-complement coefficient stored by a quire. -/
@[inline] def coefficient (value : Model format) : Int :=
  value.word.toInt

/-- The all-zero standard quire. -/
@[inline] def zero (format : Format) : Model format :=
  ⟨FixedInt.ofInt 0⟩

/-- Quire NaR, encoded as the most-negative `16n`-bit two's-complement word. -/
@[inline] def nar (format : Format) : Model format :=
  ⟨FixedInt.minCode (width format)⟩

/-- Whether a quire contains the standard's reserved NaR word. -/
@[inline] def isNaR (value : Model format) : Bool :=
  value == nar format

/--
Signed coefficients available to ordinary quire values.

The lower inequality is strict because `FixedInt.minValue` is the reserved NaR encoding. The
greatest two's-complement integer remains an ordinary quire coefficient.
-/
def OrdinaryCoefficient (format : Format) (value : Int) : Prop :=
  FixedInt.minValue (width format) < value ∧
    value ≤ FixedInt.maxValue (width format)

instance (format : Format) (value : Int) :
    Decidable (OrdinaryCoefficient format value) :=
  inferInstanceAs
    (Decidable
      (FixedInt.minValue (width format) < value ∧
        value ≤ FixedInt.maxValue (width format)))

/--
Encode an exact quire coefficient, returning quire NaR on overflow or collision with the reserved
most-negative word.

This is the common overflow boundary used by every standard quire operation.
-/
@[inline] def ofCoefficient (format : Format) (value : Int) : Model format :=
  if OrdinaryCoefficient format value then
    ⟨FixedInt.ofInt value⟩
  else
    nar format

/--
Integer coefficient of a dyadic value at the quire's fixed binary scale.

When `scaleExponent format ≤ value.exponent`, as holds for every ordinary posit and every exact
product of two ordinary posits, this is an exact left shift of the signed significand and
`Model.coefficientOfDyadic_denotes` recovers `value.toRat`. When the stored exponent is below the
quire scale, the shift count clamps to zero and the result need not denote `value`.
`Model.addDyadic` rejects that case, and decoded posit inputs to `Model.pToQ` satisfy the bound.
-/
@[inline] def coefficientOfDyadic
    (format : Format) (value : FloatLib.Numerics.Dyadic) : Int :=
  value.signedSignificand *
    (2 : Int) ^ Int.toNat (value.exponent - scaleExponent format)

end Model
end FloatLib.Floats.Formats.Posit.Quire
