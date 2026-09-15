/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime
public import FloatLib.Floats.Formats.Posit.Quire.Arithmetic.Runtime
public import FloatLib.Floats.Formats.Posit.Quire.Semantics.Runtime
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Type -- shake: keep

/-!
# Runtime interface for configured posit quires

Configured posit quires support exact construction, decoding, accumulation, and final rounding.
The executable definitions lift the standard quire model through the configured posit carrier.
Quire arithmetic proofs and optional real/projective views are provided separately.

Accumulation returns NaR on exceptional input, overflow, or a result equal to the reserved NaR
coefficient. Ordinary results preserve the exact sum.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Section 5.11, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit.Quire

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Construct a configured quire from its complete unsigned word. -/
@[inline] def ofNatBits (bits : Nat) : Formats.Posit.Quire.Model format :=
  Formats.Posit.Quire.Model.ofNatBits format bits

/-- Read the configured quire's complete word as an unsigned natural number. -/
@[inline] def toNatBits (value : Formats.Posit.Quire.Model format) : Nat :=
  value.toNatBits

/-- All-zero configured quire. -/
@[inline] def zero : Formats.Posit.Quire.Model format :=
  Formats.Posit.Quire.Model.zero format

/-- Reserved configured quire NaR. -/
@[inline] def nar : Formats.Posit.Quire.Model format :=
  Formats.Posit.Quire.Model.nar format

/-- Complete exact rational quire semantics. -/
@[inline] def decode
    (value : Formats.Posit.Quire.Model format) :
    FloatLib.Numerics.NumericalValue Rat :=
  Formats.Posit.Quire.Model.decode value

/-- Ordinary exact rational quire value, or `none` precisely for quire NaR. -/
@[inline] def toRat?
    (value : Formats.Posit.Quire.Model format) : Option Rat :=
  Formats.Posit.Quire.Model.toRat? value

/-- Exact rational values of a list of configured posits, or `none` when some entry is NaR. -/
def exactValues? :
    List (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) →
      Option (List Rat)
  | [] => some []
  | addend :: rest => do
      let value ← ExecFloat.Posit.toRat? addend
      let values ← exactValues? rest
      pure (value :: values)

/-- Exact rational products of a list of configured posit pairs, or `none` when some entry is NaR. -/
def exactProducts? :
    List (FloatLib.Floats.ExecFloat (Configured.Family format code plan) ×
      FloatLib.Floats.ExecFloat (Configured.Family format code plan)) →
      Option (List Rat)
  | [] => some []
  | pair :: rest => do
      let left ← ExecFloat.Posit.toRat? pair.1
      let right ← ExecFloat.Posit.toRat? pair.2
      let products ← exactProducts? rest
      pure (left * right :: products)

/-- Convert one configured posit exactly into its associated quire. -/
@[inline] def pToQ
    (value : FloatLib.Floats.ExecFloat
      (Configured.Family format code plan)) :
    Formats.Posit.Quire.Model format :=
  Formats.Posit.Quire.Model.pToQ (ExecFloat.Posit.toModel value)

/-- Standard quire negation. -/
@[inline] def qNegate
    (value : Formats.Posit.Quire.Model format) :
    Formats.Posit.Quire.Model format :=
  Formats.Posit.Quire.Model.qNegate value

/-- Standard quire absolute value. -/
@[inline] def qAbs
    (value : Formats.Posit.Quire.Model format) :
    Formats.Posit.Quire.Model format :=
  Formats.Posit.Quire.Model.qAbs value

/-- Add a configured posit exactly to its associated quire. -/
@[inline] def qAddP
    (accumulator : Formats.Posit.Quire.Model format)
    (addend : FloatLib.Floats.ExecFloat
      (Configured.Family format code plan)) :
    Formats.Posit.Quire.Model format :=
  Formats.Posit.Quire.Model.qAddP accumulator
    (ExecFloat.Posit.toModel addend)

/-- Subtract a configured posit exactly from its associated quire. -/
@[inline] def qSubP
    (accumulator : Formats.Posit.Quire.Model format)
    (subtrahend : FloatLib.Floats.ExecFloat
      (Configured.Family format code plan)) :
    Formats.Posit.Quire.Model format :=
  Formats.Posit.Quire.Model.qSubP accumulator
    (ExecFloat.Posit.toModel subtrahend)

/-- Add two configured quires exactly. -/
@[inline] def qAddQ
    (left right : Formats.Posit.Quire.Model format) :
    Formats.Posit.Quire.Model format :=
  Formats.Posit.Quire.Model.qAddQ left right

/-- Subtract two configured quires exactly. -/
@[inline] def qSubQ
    (left right : Formats.Posit.Quire.Model format) :
    Formats.Posit.Quire.Model format :=
  Formats.Posit.Quire.Model.qSubQ left right

/-- Accumulate one exact configured-posit product with no intermediate rounding. -/
@[inline] def qMulAdd
    (accumulator : Formats.Posit.Quire.Model format)
    (left right : FloatLib.Floats.ExecFloat
      (Configured.Family format code plan)) :
    Formats.Posit.Quire.Model format :=
  Formats.Posit.Quire.Model.qMulAdd accumulator
    (ExecFloat.Posit.toModel left) (ExecFloat.Posit.toModel right)

/-- Subtract one exact configured-posit product with no intermediate rounding. -/
@[inline] def qMulSub
    (accumulator : Formats.Posit.Quire.Model format)
    (left right : FloatLib.Floats.ExecFloat
      (Configured.Family format code plan)) :
    Formats.Posit.Quire.Model format :=
  Formats.Posit.Quire.Model.qMulSub accumulator
    (ExecFloat.Posit.toModel left) (ExecFloat.Posit.toModel right)

/-- Round a configured quire once into its associated configured posit. -/
@[inline] def qToP
    (value : Formats.Posit.Quire.Model format) :
    FloatLib.Floats.ExecFloat (Configured.Family format code plan) :=
  ExecFloat.Posit.ofModel (Formats.Posit.Quire.Model.qToP value)

end ExecFloat.Posit.Quire
end FloatLib.Floats
