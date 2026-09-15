/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Bounded.Core
public import FloatLib.Floats.Formats.FixedPoint.Exact.Runtime
public import FloatLib.Numerics.Quantization.Deterministic
public import FloatLib.Numerics.Core.Proof

/-!
# Rational contracts for bounded fixed point

The bounded carrier denotes the subset of the unbounded fixed-point grid whose coefficients
fit the signed storage width. This module defines the mathematical contract for three
overflow policies:

* wrapping operations use centered reduction of the exact coefficient;
* checked operations are exact when the destination coefficient fits;
* saturating operations clamp the exact coefficient to the signed destination range.

The executable `BitVec` kernels live in `Bounded.Core`. Their refinement proofs are isolated in
`Semantics.Proof`, keeping the contract reusable without importing the proof implementation.
-/

@[expose] public section

open FloatLib.Numerics
open FloatLib.Numerics.Representations

namespace FloatLib.Floats.Formats.FixedPoint.Bounded

/-- Rational value represented by an integer coefficient at one fixed scale. -/
def valueOfCoefficient (radix : Radix) (fractionalDigits : Nat) (value : Int) : ℚ :=
  value / (scale radix fractionalDigits : Nat)

/--
Recover the nearest integer coefficient of a rational scalar at one fixed scale.

This is exact on every scalar represented by the bounded fixed-point system.
-/
def coefficientOf (radix : Radix) (fractionalDigits : Nat) (value : ℚ) : Int :=
  roundRatEven (value * (scale radix fractionalDigits : Nat))

/-- Wrapping same-scale addition on scalar values. -/
def wrapAddValue (radix : Radix) (fractionalDigits width : Nat)
    (left right : ℚ) : ℚ :=
  valueOfCoefficient radix fractionalDigits
    ((coefficientOf radix fractionalDigits left +
      coefficientOf radix fractionalDigits right).bmod (2 ^ width))

/-- Wrapping same-scale subtraction on scalar values. -/
def wrapSubValue (radix : Radix) (fractionalDigits width : Nat)
    (left right : ℚ) : ℚ :=
  valueOfCoefficient radix fractionalDigits
    ((coefficientOf radix fractionalDigits left -
      coefficientOf radix fractionalDigits right).bmod (2 ^ width))

/-- Wrapping multiplication on scalar values at the composed output scale. -/
def wrapMulValue (radix : Radix) (p q outWidth : Nat)
    (left right : ℚ) : ℚ :=
  valueOfCoefficient radix (p + q)
    ((coefficientOf radix p left * coefficientOf radix q right).bmod (2 ^ outWidth))

/-- Saturating same-scale addition on scalar values. -/
def saturatingAddValue (radix : Radix) (fractionalDigits width : Nat)
    (left right : ℚ) : ℚ :=
  valueOfCoefficient radix fractionalDigits
    (FixedInt.clamp width
      (coefficientOf radix fractionalDigits left +
        coefficientOf radix fractionalDigits right))

/-- Saturating same-scale subtraction on scalar values. -/
def saturatingSubValue (radix : Radix) (fractionalDigits width : Nat)
    (left right : ℚ) : ℚ :=
  valueOfCoefficient radix fractionalDigits
    (FixedInt.clamp width
      (coefficientOf radix fractionalDigits left -
        coefficientOf radix fractionalDigits right))

/-- Saturating multiplication on scalar values at the composed output scale. -/
def saturatingMulValue (radix : Radix) (p q outWidth : Nat)
    (left right : ℚ) : ℚ :=
  valueOfCoefficient radix (p + q)
    (FixedInt.clamp outWidth
      (coefficientOf radix p left * coefficientOf radix q right))

/-- Forgetting the coefficient bound yields the corresponding exact fixed-point code. -/
@[inline] def toUnbounded {radix : Radix} {fractionalDigits width : Nat}
    (code : Code radix fractionalDigits width) :
    FixedPoint.Code radix fractionalDigits :=
  ⟨coefficient code⟩

/-- Bounded fixed point interpreted as an exact rational numerical system. -/
def numericalSystem (radix : Radix) (fractionalDigits width : Nat) :
    NumericalSystem :=
  NumericalSystem.ofFinite
    (fun code : Code radix fractionalDigits width ↦
      toRat radix fractionalDigits code)

/-- A bounded code with an erased proof of its complete denotation. -/
abbrev At (radix : Radix) (fractionalDigits width : Nat)
    (value : NumericalValue ℚ) :=
  (numericalSystem radix fractionalDigits width).At value

/-- A bounded code with an erased proof of its exact rational value. -/
abbrev AtFinite (radix : Radix) (fractionalDigits width : Nat) (value : ℚ) :=
  (numericalSystem radix fractionalDigits width).AtFinite value

end FloatLib.Floats.Formats.FixedPoint.Bounded
