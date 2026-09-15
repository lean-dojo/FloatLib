/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Status
public import FloatLibTests.Accounting

/-!
# Shared binary-interchange regression checks

Regression modules supply the numerical operation and fixture corpus. This module supplies the
binary-format checks they share: bitwise comparison, IEEE-status matching, route coverage, and
exhaustive traversal of a format's encodings. Format-independent failure counting lives in
`FloatLibTests.Accounting`.
-/

@[expose] public section

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLibTests.Accounting

namespace FloatLibTests.Regression.BinaryInterchange.Harness

universe u v w

/-- Compare two values by their complete stored encoding. -/
@[inline] def sameBits {fmt : FloatFormat} (left right : Model fmt) : Bool :=
  left.toNatBits == right.toNatBits

/-- Check every IEEE exception-status flag. -/
@[inline] def statusIs (status : Model.IEEEStatus)
    (invalid divideByZero overflow underflow inexact : Bool) : Bool :=
  status.invalid == invalid &&
  status.divideByZero == divideByZero &&
  status.overflow == overflow &&
  status.underflow == underflow &&
  status.inexact == inexact

/-- Check both the stored result and every IEEE exception-status flag. -/
@[inline] def outcomeIs {fmt : FloatFormat} (outcome : Model.IEEEOutcome fmt)
    (expected : Model fmt) (invalid divideByZero overflow underflow inexact : Bool) : Bool :=
  sameBits outcome.value expected &&
  statusIs outcome.status invalid divideByZero overflow underflow inexact

/-- Count disagreements between an operation and its reference over any iterable corpus. -/
@[inline] def mismatchCount
    {ρ : Type u} {α : Type v} {β : Type w} [ForIn Id ρ α]
    (inputs : ρ)
    (operation reference : α → β)
    (same : β → β → Bool) :
    Nat :=
  countWhereFailures inputs fun input =>
    same (operation input) (reference input)

/-- Count inputs accepted by an optional optimized route. -/
@[inline] def acceptedCount
    {ρ : Type u} {α : Type v} {β : Type w} [ForIn Id ρ α]
    (inputs : ρ) (candidate : α → Option β) : Nat := Id.run do
  let mut accepted := 0
  for input in inputs do
    if (candidate input).isSome then
      accepted := accepted + 1
  return accepted

/-- Count route-coverage requirements that were never exercised. -/
@[inline] def missingCoverage (counts : List Nat) : Nat :=
  countWhereFailures counts fun count => count != 0

/-- Check whether one optional binary route and its compiled operation behave as expected. -/
@[inline] def binaryRouteFailures {fmt : FloatFormat}
    {ρ : Type u} {α : Type v} [ForIn Id ρ (Model fmt × Model fmt)]
    (inputs : ρ)
    (candidate : Model fmt → Model fmt → Option α)
    (operation reference : Model fmt → Model fmt → Model fmt)
    (expectAccepted : Bool) :
    Nat :=
  countWhereFailures inputs fun input =>
    let routeMatches := (candidate input.1 input.2).isSome == expectAccepted
    routeMatches && sameBits (operation input.1 input.2) (reference input.1 input.2)

/--
Exceptional and out-of-range products that every finite normal-product route must reject.
-/
def productBaselinePairs (fmt : FloatFormat) : Array (Model fmt × Model fmt) :=
  #[
    (Model.posZero fmt, Model.posOne fmt),
    (Model.posMinSubnormal fmt, Model.posOne fmt),
    (Model.ofFields fmt false 1 0, Model.ofFields fmt false (fmt.bias - 1) 0),
    (Model.maxFinite fmt false, Model.ofFields fmt false (fmt.bias + 1) 0),
    (Model.posInf fmt, Model.posOne fmt),
    (Model.canonicalNaN fmt, Model.posOne fmt)
  ]

/-- Count failures over every stored encoding of a format. -/
@[inline] def exhaustiveUnaryFailures (fmt : FloatFormat)
    (passes : Model fmt → Bool) : Nat :=
  countWhereFailures (List.range (2 ^ fmt.bitWidth)) fun bits =>
    passes (Model.ofNatBits (fmt := fmt) bits)

/-- Count failures over every ordered pair of stored encodings. -/
@[inline] def exhaustiveBinaryFailures (fmt : FloatFormat)
    (passes : Model fmt → Model fmt → Bool) : Nat :=
  let words := List.range (2 ^ fmt.bitWidth)
  countPairFailures words words fun leftBits rightBits =>
    passes
      (Model.ofNatBits (fmt := fmt) leftBits)
      (Model.ofNatBits (fmt := fmt) rightBits)

/-- Count failures over every ordered triple of stored encodings. -/
@[inline] def exhaustiveTernaryFailures (fmt : FloatFormat)
    (passes : Model fmt → Model fmt → Model fmt → Bool) : Nat :=
  let words := List.range (2 ^ fmt.bitWidth)
  countTripleFailures words words words fun leftBits rightBits addendBits =>
    passes
      (Model.ofNatBits (fmt := fmt) leftBits)
      (Model.ofNatBits (fmt := fmt) rightBits)
      (Model.ofNatBits (fmt := fmt) addendBits)

/-- Render a regression report that checks semantics without requiring a specialized route. -/
def mismatchReport (suite inputLabel : String) (cases mismatches : Nat) : String :=
  String.intercalate "\n"
    [s!"{suite} {inputLabel}: {cases}", s!"{suite} TOTAL: {mismatches}"]

end FloatLibTests.Regression.BinaryInterchange.Harness
