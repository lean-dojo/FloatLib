/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Conversion
public import FloatLib.Floats.Formats.BinaryInterchange.Status
public import FloatLibTests.Accounting
public import FloatLibTests.Regression.BinaryInterchange.Harness

/-!
# Scaled-rational regression checks for `Model`

These checks exercise normalized-rational conversion, exponent-aware nearest and directed rounding,
IEEE status classification, and division across binary16, bfloat16, binary32, binary64, binary128,
and a custom wide-exponent format. The scaled inputs deliberately sit far outside the finite range
so regressions that materialize the full external exponent become visible.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.ExecFloatScaledRationals

open Harness
open FloatLibTests.Accounting

def scaledResultIs (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (expected : Model fmt) : Bool :=
  sameBits (Model.roundRatWithRoundingScaled fmt mode sign numerator denominator exponent)
    expected

def scaledStatusIs (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (expected : Model fmt)
    (overflow underflow inexact : Bool) : Bool :=
  let rounded :=
    Model.roundRatWithRoundingScaled fmt mode sign numerator denominator exponent
  sameBits rounded expected &&
  statusIs
    (Model.rationalRoundingStatusScaled fmt mode sign numerator denominator exponent rounded)
    false false overflow underflow inexact

def rationalSamples : List Rat :=
  [ -355 / 113
  , -3 / 2
  , -1 / 3
  , 0
  , 1 / 3
  , 3 / 2
  , 355 / 113
  ]

def rationalWrapperAgrees (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (q : Rat) : Bool :=
  sameBits
    (Model.roundRatQWithRounding fmt mode q)
    (Model.roundRatWithRounding fmt mode (q.num < 0) q.num.natAbs q.den)

def rationalBracketed (fmt : FloatFormat) (q : Rat) : Bool :=
  let lower := Model.roundRatQDown fmt q
  let upper := Model.roundRatQUp fmt q
  match Model.toRat? lower, Model.toRat? upper with
  | some lowerQ, some upperQ => lowerQ ≤ q && q ≤ upperQ
  | _, _ => false

/-- Exact normalized-rational conversion checks for one format. -/
def rationalConversionFailures (fmt : FloatFormat) : Nat :=
  let wrapperChecks :=
    Model.IEEERoundingMode.all.flatMap fun mode =>
      rationalSamples.map (rationalWrapperAgrees fmt mode)
  let bracketChecks := rationalSamples.map (rationalBracketed fmt)
  let exactChecks :=
    [ Model.toRat? (Model.roundRatQ fmt (3 / 2)) == some (3 / 2)
    , Model.toRat? (Model.roundRatQ fmt (-3 / 2)) == some (-3 / 2)
    ]
  let positiveThird : Rat := 1 / 3
  let negativeThird : Rat := -1 / 3
  let directionChecks :=
    [ sameBits
        (Model.roundRatQWithRounding fmt .towardZero positiveThird)
        (Model.roundRatQDown fmt positiveThird)
    , sameBits
        (Model.roundRatQWithRounding fmt .towardPositiveInfinity positiveThird)
        (Model.roundRatQUp fmt positiveThird)
    , sameBits
        (Model.roundRatQWithRounding fmt .towardZero negativeThird)
        (Model.roundRatQUp fmt negativeThird)
    , sameBits
        (Model.roundRatQWithRounding fmt .towardNegativeInfinity negativeThird)
        (Model.roundRatQDown fmt negativeThird)
    ]
  countFailures (wrapperChecks ++ bracketChecks ++ exactChecks ++ directionChecks)

/-- Extreme scaled-rational rounding checks for one format. -/
def scaledRoundingFailures (fmt : FloatFormat) : Nat :=
  let overflowExponent := Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) + 1
  let halfMinSubnormalExponent := FloatFormat.ieeeMinSubnormalExponent fmt - 1
  let farTinyExponent := FloatFormat.ieeeMinSubnormalExponent fmt - 1000000
  countFailures
    [ scaledResultIs fmt .nearestEven false 3 2 overflowExponent (Model.posInf fmt)
    , scaledResultIs fmt .nearestEven true 3 2 overflowExponent (Model.negInf fmt)
    , scaledResultIs fmt .towardZero false 3 2 overflowExponent
        (Model.posMaxFinite fmt)
    , scaledResultIs fmt .towardZero true 3 2 overflowExponent
        (Model.negMaxFinite fmt)
    , scaledResultIs fmt .towardPositiveInfinity false 3 2 overflowExponent (Model.posInf fmt)
    , scaledResultIs fmt .towardNegativeInfinity false 3 2 overflowExponent
        (Model.posMaxFinite fmt)
    , scaledResultIs fmt .towardPositiveInfinity true 3 2 overflowExponent
        (Model.negMaxFinite fmt)
    , scaledResultIs fmt .towardNegativeInfinity true 3 2 overflowExponent (Model.negInf fmt)
    , scaledResultIs fmt .nearestEven false 1 1 halfMinSubnormalExponent
        (Model.posZero fmt)
    , scaledResultIs fmt .nearestEven true 1 1 halfMinSubnormalExponent
        (Model.negZero fmt)
    , scaledResultIs fmt .towardPositiveInfinity false 1 3 farTinyExponent
        (Model.posMinSubnormal fmt)
    , scaledResultIs fmt .towardNegativeInfinity false 1 3 farTinyExponent
        (Model.posZero fmt)
    , scaledResultIs fmt .towardPositiveInfinity true 1 3 farTinyExponent
        (Model.negZero fmt)
    , scaledResultIs fmt .towardNegativeInfinity true 1 3 farTinyExponent
        (Model.negMinSubnormal fmt)
    , scaledResultIs fmt .nearestEven false 1 1 (FloatFormat.ieeeMinSubnormalExponent fmt)
        (Model.posMinSubnormal fmt)
    ]

/-- Extreme scaled-rational status checks for one format. -/
def scaledStatusFailures (fmt : FloatFormat) : Nat :=
  let overflowExponent := Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) + 1
  let farTinyExponent := FloatFormat.ieeeMinSubnormalExponent fmt - 1000000
  countFailures
    [ scaledStatusIs fmt .nearestEven false 3 2 overflowExponent (Model.posInf fmt)
        true false true
    , scaledStatusIs fmt .towardZero false 3 2 overflowExponent
        (Model.posMaxFinite fmt) true false true
    , scaledStatusIs fmt .towardNegativeInfinity true 3 2 overflowExponent (Model.negInf fmt)
        true false true
    , scaledStatusIs fmt .nearestEven false 1 3 farTinyExponent (Model.posZero fmt)
        false true true
    , scaledStatusIs fmt .towardPositiveInfinity false 1 3 farTinyExponent
        (Model.posMinSubnormal fmt) false true true
    , scaledStatusIs fmt .towardNegativeInfinity true 1 3 farTinyExponent
        (Model.negMinSubnormal fmt) false true true
    , scaledStatusIs fmt .nearestEven false 1 1 (FloatFormat.ieeeMinSubnormalExponent fmt)
        (Model.posMinSubnormal fmt) false false false
    ]

/-- Division and status checks whose decoded exponent differences span the full format range. -/
def divisionStatusFailures (fmt : FloatFormat) : Nat :=
  let maximum := Model.posMaxFinite fmt
  let negativeMaximum := Model.negMaxFinite fmt
  let minimum := Model.posMinSubnormal fmt
  let negativeMinimum := Model.negMinSubnormal fmt
  countFailures
    [ outcomeIs (Model.divWithStatus maximum minimum .nearestEven)
        (Model.posInf fmt) false false true false true
    , outcomeIs (Model.divWithStatus maximum minimum .towardZero)
        maximum false false true false true
    , outcomeIs (Model.divWithStatus maximum minimum .towardPositiveInfinity)
        (Model.posInf fmt) false false true false true
    , outcomeIs (Model.divWithStatus maximum minimum .towardNegativeInfinity)
        maximum false false true false true
    , outcomeIs (Model.divWithStatus negativeMaximum minimum .nearestEven)
        (Model.negInf fmt) false false true false true
    , outcomeIs (Model.divWithStatus negativeMaximum minimum .towardPositiveInfinity)
        negativeMaximum false false true false true
    , outcomeIs (Model.divWithStatus negativeMaximum minimum .towardNegativeInfinity)
        (Model.negInf fmt) false false true false true
    , outcomeIs (Model.divWithStatus minimum maximum .nearestEven)
        (Model.posZero fmt) false false false true true
    , outcomeIs (Model.divWithStatus minimum maximum .towardPositiveInfinity)
        minimum false false false true true
    , outcomeIs (Model.divWithStatus minimum maximum .towardNegativeInfinity)
        (Model.posZero fmt) false false false true true
    , outcomeIs (Model.divWithStatus negativeMinimum maximum .towardPositiveInfinity)
        (Model.negZero fmt) false false false true true
    , outcomeIs (Model.divWithStatus negativeMinimum maximum .towardNegativeInfinity)
        negativeMinimum false false false true true
    , outcomeIs (Model.divWithStatus maximum maximum .nearestEven)
        (Model.posOne fmt) false false false false false
    ]

def formatFailures (fmt : FloatFormat) : Nat :=
  rationalConversionFailures fmt +
  scaledRoundingFailures fmt +
  scaledStatusFailures fmt +
  divisionStatusFailures fmt

def standardFormats : List FloatFormat :=
  [ FloatFormat.binary16
  , FloatFormat.bfloat16
  , FloatFormat.binary32
  , FloatFormat.binary64
  , FloatFormat.binary128
  ]

/-- A nonstandard layout with a substantially wider exponent field than binary128. -/
def customWideFormat : FloatFormat :=
  FloatFormat.ieee 20 37

def failStandardFormats : Thunk Nat := ⟨fun _ =>
  (standardFormats.map formatFailures).sum⟩

def failCustomWideFormat : Thunk Nat := ⟨fun _ =>
  formatFailures customWideFormat⟩

end FloatLibTests.Regression.BinaryInterchange.ExecFloatScaledRationals
