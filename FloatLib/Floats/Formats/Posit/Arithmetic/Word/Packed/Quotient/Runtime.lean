/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Elimination.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.GuardSticky.Runtime
public import FloatLib.Kernels.FixedWord.Quotient.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.WordLimb.Runtime
-- This focused certificate activates the optimized quotient loop without pulling the complete
-- rational-arithmetic proof development into a runtime module.
import FloatLib.Kernels.FixedWord.Quotient.Compiler

/-!
# Packed native-word Posit division

Packed operands are decoded directly to sign, significand, and exponent fields. Quotient rounding
normalizes them in one word, generates the destination-width quotient prefix with the shared
two-limb restoring recurrence, and feeds that exact prefix to the common guard/sticky packer.

The two-limb state is selected by intermediate capacity: a normalized one-word ratio can require
one additional quotient digit, while its doubled remainder must never wrap. Significands and
restoring-loop state stay in fixed-width carriers; exponents and digit counts use `Int` and `Nat`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedQuotient

open FloatLib.Numerics
open FloatLib.Numerics.FixedWord
open FloatLib.Numerics.FixedWord.RestoringQuotient

/-- One-word significands normalized to a common leading position. -/
structure NormalizedWords where
  /-- Numerator shifted so its leading bit reaches the common position. -/
  numerator : UInt64
  /-- Denominator shifted so its leading bit reaches the common position. -/
  denominator : UInt64
  /-- Leading-bit position of the original numerator. -/
  numeratorLeading : Nat
  /-- Leading-bit position of the original denominator. -/
  denominatorLeading : Nat

/--
Normalize two nonzero one-word significands to a common leading position.

Each shift raises the smaller leading position to the larger one. The result therefore still fits
in one word. The original leading positions are retained so the quotient exponent can compensate
for the different shifts.
-/
@[inline] def normalizeWords
    (numerator denominator : UInt64) : NormalizedWords :=
  let numeratorLeading := (FixedWord.log2Word numerator).toNat
  let denominatorLeading := (FixedWord.log2Word denominator).toNat
  let commonLeading := max numeratorLeading denominatorLeading
  { numerator :=
      numerator <<< UInt64.ofNat (commonLeading - numeratorLeading)
    denominator :=
      denominator <<< UInt64.ofNat (commonLeading - denominatorLeading)
    numeratorLeading
    denominatorLeading }

/-- Exact two-limb quotient prefix consumed by direct Posit rounding. -/
structure Prefix where
  /-- Generated quotient bits with every omitted nonzero bit jammed into the low bit. -/
  significand : UInt128
  /-- Dyadic exponent associated with the generated quotient prefix. -/
  exponent : Int

/-- Jam a nonzero restoring remainder into the quotient prefix's low bit. -/
@[inline] def jamState (state : QuotientState UInt128) : UInt128 :=
  if state.remainder.hi == 0 && state.remainder.lo == 0 then
    state.quotient
  else
    state.quotient.setLowBit

/--
Generate the normalized quotient prefix needed by the destination format.

Ratios below one consume one extra digit; ratios at least one begin with their known leading one.
The policy is identical for every one-word-eligible format and depends only on destination
precision.
-/
@[inline] def quotientPrefixWord
    (format : Format)
    (numeratorSignificand : UInt64) (numeratorExponent : Int)
    (denominatorSignificand : UInt64) (denominatorExponent : Int) : Prefix :=
  let normalized :=
    normalizeWords numeratorSignificand denominatorSignificand
  let steps :=
    if normalized.numerator < normalized.denominator then
      format.payloadBits + 1
  else
    format.payloadBits
  let initial : QuotientState UInt128 :=
    { quotient :=
        NativeWordLimb.widen
          (normalized.numerator / normalized.denominator)
      remainder :=
        NativeWordLimb.widen
          (normalized.numerator % normalized.denominator) }
  let state :=
    quotientSteps128
      (NativeWordLimb.widen normalized.denominator)
      steps initial
  { significand := jamState state
    exponent :=
      numeratorExponent - denominatorExponent +
        Int.ofNat normalized.numeratorLeading -
        Int.ofNat normalized.denominatorLeading -
        Int.ofNat steps }

/-- Round a positive quotient directly from native decoded fields. -/
@[inline] def roundPositiveCodeWord
    (format : Format)
    (numeratorSignificand : UInt64) (numeratorExponent : Int)
    (denominatorSignificand : UInt64) (denominatorExponent : Int) : UInt64 :=
  if numeratorSignificand == 0 || denominatorSignificand == 0 then
    0
  else
    let generated :=
      quotientPrefixWord format
        numeratorSignificand numeratorExponent
        denominatorSignificand denominatorExponent
    (NativeLimbRounding.GuardSticky.roundCodeWord
      format false generated.significand generated.exponent).lo

/-- Natural-number view of the native positive quotient code. -/
@[inline] def roundPositiveCode
    (format : Format)
    (numeratorSignificand : UInt64) (numeratorExponent : Int)
    (denominatorSignificand : UInt64) (denominatorExponent : Int) : Nat :=
  (roundPositiveCodeWord format
    numeratorSignificand numeratorExponent
    denominatorSignificand denominatorExponent).toNat

/-- Word-valued signed quotient encoding. -/
@[inline] def roundFieldsWord
    (format : Format)
    (numeratorNegative : Bool)
    (numeratorSignificand : UInt64) (numeratorExponent : Int)
    (denominatorNegative : Bool)
    (denominatorSignificand : UInt64) (denominatorExponent : Int) : UInt64 :=
  if denominatorSignificand == 0 then
    NativeWord.signMaskWord format
  else if numeratorSignificand == 0 then
    0
  else
    let generated :=
      quotientPrefixWord format
        numeratorSignificand numeratorExponent
        denominatorSignificand denominatorExponent
    (NativeLimbRounding.GuardSticky.roundCodeWord
      format (Bool.xor numeratorNegative denominatorNegative)
      generated.significand generated.exponent).lo

/--
Natural-number view of signed decoded-field division.

Division by zero emits NaR, zero divided by a finite nonzero value emits zero, and finite signs
are handled by the same direct guard/sticky call as the word-valued API.
-/
@[inline] def roundFields
    (format : Format)
    (numeratorNegative : Bool)
    (numeratorSignificand : UInt64) (numeratorExponent : Int)
    (denominatorNegative : Bool)
    (denominatorSignificand : UInt64) (denominatorExponent : Int) : Nat :=
  (roundFieldsWord format
    numeratorNegative numeratorSignificand numeratorExponent
    denominatorNegative denominatorSignificand denominatorExponent).toNat

/-- Divide two proved-valid packed Posit words. -/
@[inline] def divWordsCodeValid
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : Nat :=
  NativeWord.withTwoDyadicWordFieldsValid format
      heligible
      left hleft right hright format.signMaskNat
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      roundFields format
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent

/-- Divide two proved-valid packed Posit words and retain the result in `UInt64`. -/
@[inline] def divWordsCodeWordValid
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt64 :=
  NativeWord.withTwoDyadicWordFieldsValid format
      heligible
      left hleft right hright (NativeWord.signMaskWord format)
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      roundFieldsWord format
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent

end FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedQuotient
