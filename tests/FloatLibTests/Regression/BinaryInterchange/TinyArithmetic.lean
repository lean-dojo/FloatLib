/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Finite
public import FloatLibTests.Accounting
public import FloatLibTests.Regression.BinaryInterchange.Harness

/-!
# Exhaustive tiny-format arithmetic checks

These executable checks compare the compiled tiny-format arithmetic paths against their
format-generic specifications for every stored-word input. Keeping them in a focused module avoids
recompiling the unrelated fixed-limb and complex regression suite when a tiny kernel changes.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.TinyArithmetic

open FloatLib.Numerics
open FloatLibTests.Accounting
open Model

def namedTinyFormats : List FloatFormat :=
  [ FloatFormat.e2m1
  , FloatFormat.e2m3
  , FloatFormat.e3m2
  , FloatFormat.e4m3fn
  , FloatFormat.e5m2
  , FloatFormat.e4m3fnuz
  , FloatFormat.e5m2fnuz
  ]

def practicalFmaFormats : List FloatFormat :=
  [FloatFormat.e2m1, FloatFormat.e2m3, FloatFormat.e3m2]

/--
Count compiled nearest-even checked multiplication results that differ from the exact policy
specification over every pair of stored words.
-/
def compiledFiniteMulFailures (fmt : FloatFormat) : Nat :=
  Harness.exhaustiveBinaryFailures fmt fun left right =>
    Model.mulFinite? fmt QuantizationPolicy.nearestEven 17 left right ==
      Model.mulFiniteSpec? fmt QuantizationPolicy.nearestEven 17 left right

/-- Count compiled additions that differ from the table-free generic implementation. -/
def compiledAddFailures (fmt : FloatFormat) : Nat :=
  Harness.exhaustiveBinaryFailures fmt fun left right =>
    Harness.sameBits (Model.add left right) (Model.AddBackend.generic left right)

/-- Count compiled subtractions that differ from generic addition of the negated right operand. -/
def compiledSubFailures (fmt : FloatFormat) : Nat :=
  Harness.exhaustiveBinaryFailures fmt fun left right =>
    Harness.sameBits (Model.sub left right)
      (Model.AddBackend.generic left (Model.neg right))

/--
Count canonical compiled multiplication results that differ from the generic exact implementation
over every pair of stored words.
-/
def compiledTotalMulFailures (fmt : FloatFormat) : Nat :=
  Harness.exhaustiveBinaryFailures fmt fun left right =>
    Harness.sameBits (Model.mul left right) (Model.MulBackend.generic left right)

/-- Count compiled divisions that differ from the table-free generic implementation. -/
def compiledDivFailures (fmt : FloatFormat) : Nat :=
  Harness.exhaustiveBinaryFailures fmt fun left right =>
    Harness.sameBits (Model.div left right) (Model.DivBackend.generic left right)

/-- Count compiled fused multiply-adds that differ from the generic implementation. -/
def compiledFmaFailures (fmt : FloatFormat) : Nat :=
  Harness.exhaustiveTernaryFailures fmt fun left right addend =>
    Harness.sameBits (Model.fma left right addend)
      (Model.FmaBackend.generic left right addend)

/-- Count canonical compiled square roots that differ from the generic implementation. -/
def compiledSqrtFailures (fmt : FloatFormat) : Nat :=
  Harness.exhaustiveUnaryFailures fmt fun value =>
    Harness.sameBits (Model.sqrt value) (Model.SqrtBackend.generic value)

/-- Run the exhaustive checks when the kernel suite requests its report. -/
def report : Thunk ReportSection := ⟨fun _ =>
  ReportSection.ofRows "exhaustive tiny formats"
    [ ("finiteMultiplication", (namedTinyFormats.map compiledFiniteMulFailures).sum)
    , ("addition", (namedTinyFormats.map compiledAddFailures).sum)
    , ("subtraction", (namedTinyFormats.map compiledSubFailures).sum)
    , ("totalMultiplication", (namedTinyFormats.map compiledTotalMulFailures).sum)
    , ("division", (namedTinyFormats.map compiledDivFailures).sum)
    , ("fusedMultiplyAdd", (practicalFmaFormats.map compiledFmaFailures).sum)
    , ("squareRoot", (namedTinyFormats.map compiledSqrtFailures).sum)
    ]⟩

end FloatLibTests.Regression.BinaryInterchange.TinyArithmetic
