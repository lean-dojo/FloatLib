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
-- This affects native code generation only. Elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.ExecFloatScaledRationals

open Harness
open FloatLibTests.Accounting

def scaledResultIs (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (expected : Model fmt) : Bool :=
  sameBits (Model.Internal.Directed.roundRatScaled fmt mode sign numerator denominator exponent)
    expected

def scaledStatusIs (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (expected : Model fmt)
    (overflow underflow inexact : Bool) (ternary : Ordering) : Bool :=
  let rounded :=
    Model.Internal.Directed.roundRatScaled fmt mode sign numerator denominator exponent
  sameBits rounded expected &&
  statusIs
    (Model.rationalRoundingStatusScaled fmt mode sign numerator denominator exponent rounded)
    false false overflow underflow inexact &&
  Model.rationalTernaryScaled sign numerator denominator exponent rounded == ternary

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
    (Model.ofRat fmt q (mode := mode))
    (Model.Internal.Directed.roundRat fmt mode (q.num < 0) q.num.natAbs q.den)

def rationalBracketed (fmt : FloatFormat) (q : Rat) : Bool :=
  let lower := Model.ofRat fmt q (mode := .down)
  let upper := Model.ofRat fmt q (mode := .up)
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
    [ Model.toRat? (Model.ofRat fmt (3 / 2)) == some (3 / 2)
    , Model.toRat? (Model.ofRat fmt (-3 / 2)) == some (-3 / 2)
    ]
  let positiveThird : Rat := 1 / 3
  let negativeThird : Rat := -1 / 3
  let directionChecks :=
    [ sameBits
        (Model.ofRat fmt positiveThird (mode := .towardZero))
        (Model.ofRat fmt positiveThird (mode := .down))
    , sameBits
        (Model.ofRat fmt negativeThird (mode := .towardZero))
        (Model.ofRat fmt negativeThird (mode := .up))
    , sameBits
        (Model.ofRat fmt positiveThird (mode := .away))
        (Model.ofRat fmt positiveThird (mode := .up))
    , sameBits
        (Model.ofRat fmt negativeThird (mode := .away))
        (Model.ofRat fmt negativeThird (mode := .down))
    ]
  countFailures (wrapperChecks ++ bracketChecks ++ exactChecks ++ directionChecks)

/-- Extreme scaled-rational rounding checks for one format. -/
def scaledRoundingFailures (fmt : FloatFormat) : Nat :=
  let overflowExponent := Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) + 1
  let halfMinSubnormalExponent := FloatFormat.ieeeMinSubnormalExponent fmt - 1
  let farTinyExponent := FloatFormat.ieeeMinSubnormalExponent fmt - 1000000
  countFailures
    [ scaledResultIs fmt .nearest false 3 2 overflowExponent (Model.posInf fmt)
    , scaledResultIs fmt .nearest true 3 2 overflowExponent (Model.negInf fmt)
    , scaledResultIs fmt .towardZero false 3 2 overflowExponent
        (Model.posMaxFinite fmt)
    , scaledResultIs fmt .towardZero true 3 2 overflowExponent
        (Model.negMaxFinite fmt)
    , scaledResultIs fmt .up false 3 2 overflowExponent (Model.posInf fmt)
    , scaledResultIs fmt .down false 3 2 overflowExponent
        (Model.posMaxFinite fmt)
    , scaledResultIs fmt .up true 3 2 overflowExponent
        (Model.negMaxFinite fmt)
    , scaledResultIs fmt .down true 3 2 overflowExponent (Model.negInf fmt)
    , scaledResultIs fmt .nearest false 1 1 halfMinSubnormalExponent
        (Model.posZero fmt)
    , scaledResultIs fmt .nearest true 1 1 halfMinSubnormalExponent
        (Model.negZero fmt)
    , scaledResultIs fmt .up false 1 3 farTinyExponent
        (Model.posMinSubnormal fmt)
    , scaledResultIs fmt .down false 1 3 farTinyExponent
        (Model.posZero fmt)
    , scaledResultIs fmt .up true 1 3 farTinyExponent
        (Model.negZero fmt)
    , scaledResultIs fmt .down true 1 3 farTinyExponent
        (Model.negMinSubnormal fmt)
    , scaledResultIs fmt .nearest false 1 1 (FloatFormat.ieeeMinSubnormalExponent fmt)
        (Model.posMinSubnormal fmt)
    ]

/-- Extreme scaled-rational status checks for one format. -/
def scaledStatusFailures (fmt : FloatFormat) : Nat :=
  let overflowExponent := Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) + 1
  let farTinyExponent := FloatFormat.ieeeMinSubnormalExponent fmt - 1000000
  countFailures
    [ scaledStatusIs fmt .nearest false 3 2 overflowExponent (Model.posInf fmt)
        true false true .gt
    , scaledStatusIs fmt .towardZero false 3 2 overflowExponent
        (Model.posMaxFinite fmt) true false true .lt
    , scaledStatusIs fmt .down true 3 2 overflowExponent (Model.negInf fmt)
        true false true .lt
    , scaledStatusIs fmt .nearest false 1 3 farTinyExponent (Model.posZero fmt)
        false true true .lt
    , scaledStatusIs fmt .up false 1 3 farTinyExponent
        (Model.posMinSubnormal fmt) false true true .gt
    , scaledStatusIs fmt .down true 1 3 farTinyExponent
        (Model.negMinSubnormal fmt) false true true .lt
    , scaledStatusIs fmt .nearest false 1 1 (FloatFormat.ieeeMinSubnormalExponent fmt)
        (Model.posMinSubnormal fmt) false false false .eq
    ]

/-- Division and status checks whose decoded exponent differences span the full format range. -/
def divisionStatusFailures (fmt : FloatFormat) : Nat :=
  let maximum := Model.posMaxFinite fmt
  let negativeMaximum := Model.negMaxFinite fmt
  let minimum := Model.posMinSubnormal fmt
  let negativeMinimum := Model.negMinSubnormal fmt
  countFailures
    [ outcomeIs (Model.div maximum minimum (mode := .nearest) (status := true))
        (Model.posInf fmt) false false true false true .gt
    , outcomeIs (Model.div maximum minimum (mode := .towardZero) (status := true))
        maximum false false true false true .lt
    , outcomeIs (Model.div maximum minimum (mode := .up) (status := true))
        (Model.posInf fmt) false false true false true .gt
    , outcomeIs (Model.div maximum minimum (mode := .down) (status := true))
        maximum false false true false true .lt
    , outcomeIs (Model.div negativeMaximum minimum (mode := .nearest) (status := true))
        (Model.negInf fmt) false false true false true .lt
    , outcomeIs (Model.div negativeMaximum minimum (mode := .up) (status := true))
        negativeMaximum false false true false true .gt
    , outcomeIs (Model.div negativeMaximum minimum (mode := .down) (status := true))
        (Model.negInf fmt) false false true false true .lt
    , outcomeIs (Model.div minimum maximum (mode := .nearest) (status := true))
        (Model.posZero fmt) false false false true true .lt
    , outcomeIs (Model.div minimum maximum (mode := .up) (status := true))
        minimum false false false true true .gt
    , outcomeIs (Model.div minimum maximum (mode := .down) (status := true))
        (Model.posZero fmt) false false false true true .lt
    , outcomeIs (Model.div negativeMinimum maximum (mode := .up) (status := true))
        (Model.negZero fmt) false false false true true .gt
    , outcomeIs (Model.div negativeMinimum maximum (mode := .down) (status := true))
        negativeMinimum false false false true true .lt
    , outcomeIs (Model.div maximum maximum (mode := .nearest) (status := true))
        (Model.posOne fmt) false false false false false .eq
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
