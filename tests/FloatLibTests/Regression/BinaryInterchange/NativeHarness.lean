/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLibTests.Regression.BinaryInterchange.Harness

/-!
# Shared native-kernel regression harness

Native regression suites differ in their fixtures and optimized kernels, but use the same
bit-for-bit comparison and route-coverage accounting. This module shares that comparison loop
while leaving each operation's cases and acceptance predicate explicit.
-/

@[expose] public section

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.NativeHarness

open Model
open FloatLibTests.Accounting

universe u v w x

/-- The common outcome of checking one optimized route against its exact reference operation. -/
structure RoutedResult where
  cases : Nat
  accepted : Nat
  mismatches : Nat

/-- Inputs deliberately handled by the exact baseline. -/
def RoutedResult.baselineCases (result : RoutedResult) : Nat :=
  result.cases - result.accepted

/-- Require both the optimized route and exact baseline to be exercised. -/
def RoutedResult.coverageFailures (result : RoutedResult) : Nat :=
  failureCount (result.accepted != 0) +
    failureCount (result.baselineCases != 0)

/-- Aggregate semantic mismatches and missing route coverage. -/
def RoutedResult.totalFailures (result : RoutedResult) : Nat :=
  result.mismatches + result.coverageFailures

/-- Render the standard native-route regression report. -/
def RoutedResult.report (result : RoutedResult) (suite inputLabel acceptedLabel baselineLabel :
    String) : String :=
  String.intercalate "\n"
    [ s!"{suite} {inputLabel}: {result.cases}"
    , s!"{suite} {acceptedLabel}: {result.accepted}"
    , s!"{suite} {baselineLabel}: {result.baselineCases}"
    , s!"{suite} mismatches: {result.mismatches}"
    , s!"{suite} TOTAL: {result.totalFailures}"
    ]

/--
Compare an operation with its exact reference while counting acceptance by one optimized route.

The inputs are traversed once, so consolidating the harness also avoids separate mismatch and
route-count passes in every regression suite.
-/
@[inline] def checkRouted
    {ρ : Type u} {α : Type v} {β : Type w} {γ : Type x} [ForIn Id ρ α]
    (inputs : ρ)
    (operation reference : α → β)
    (same : β → β → Bool)
    (candidate : α → Option γ) :
    RoutedResult := Id.run do
  let mut result : RoutedResult := { cases := 0, accepted := 0, mismatches := 0 }
  for input in inputs do
    result :=
      { cases := result.cases + 1
        accepted :=
          if (candidate input).isSome then result.accepted + 1 else result.accepted
        mismatches :=
          if same (operation input) (reference input) then
            result.mismatches
          else
            result.mismatches + 1 }
  return result

namespace Binary64

abbrev Value := NativeBinary64.Value

@[inline] def fromBits (bits : UInt64) : Value :=
  NativeBinary64.ofUInt64 bits

@[inline] def sameBits (x y : Value) : Bool :=
  NativeBinary64.toUInt64 x == NativeBinary64.toUInt64 y

@[inline] def signMask (sign : Bool) : UInt64 :=
  if sign then 0x8000000000000000 else 0

@[inline] def normalBits
    (sign : Bool) (exponent fraction : UInt64) : UInt64 :=
  signMask sign ||| (exponent <<< 52) |||
    (fraction &&& 0x000fffffffffffff)

end Binary64

namespace Pair

/-- Compare two values of one format by their complete stored encoding. -/
@[inline] def sameBits {fmt : FloatFormat} (x y : Model fmt) : Bool :=
  x.toNatBits == y.toNatBits

/-- Build a value of a two-word format from its sign, biased exponent, and fraction. -/
@[inline] def value (fmt : FloatFormat)
    (sign : Bool) (exponent fraction : Nat) : Model fmt :=
  Model.ofFields fmt sign exponent fraction

end Pair

end FloatLibTests.Regression.BinaryInterchange.NativeHarness
