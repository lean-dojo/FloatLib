/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLibTests.Regression.BinaryInterchange.Harness
public import FloatLibTests.Regression.BinaryInterchange.NativePair

/-!
# Two-word multiplication regression checks

These checks exercise the reusable `UInt128` product path at both ends of its one-storage-word
capacity tier. They verify successful normal products, both possible product-leading positions,
and every input class handled by the exact baseline against the generic implementation. The
two-word addition and subtraction suites run here for the binary128 and 96-bit layouts.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.TwoWordMul

open Model
open Harness

abbrev custom41 : FloatFormat :=
  FloatFormat.ieee 8 32

abbrev custom64 : FloatFormat :=
  FloatFormat.ieee 2 61

def ordinaryNormals (fmt : FloatFormat) :
    Array (Model fmt × Model fmt) :=
  #[
    (posOne fmt, posOne fmt),
    (negOne fmt, posOne fmt),
    (ofFields fmt false fmt.bias (2 ^ (fmt.fracWidth - 1)),
      ofFields fmt false fmt.bias (2 ^ (fmt.fracWidth - 2))),
    (ofFields fmt false fmt.bias fmt.fracMaskNat,
      ofFields fmt false fmt.bias fmt.fracMaskNat),
    (ofFields fmt true (fmt.bias + 1) (fmt.fracMaskNat / 3),
      ofFields fmt false fmt.bias (fmt.fracMaskNat / 5))
  ]

def normalFailures (fmt : FloatFormat) : Nat :=
  binaryRouteFailures (ordinaryNormals fmt)
    NativeTwoWordMul.mulNormal? MulBackend.word MulBackend.generic true

def baselineFailures (fmt : FloatFormat) : Nat :=
  binaryRouteFailures (productBaselinePairs fmt)
    NativeTwoWordMul.mulNormal? MulBackend.word MulBackend.generic false

def formatFailures (fmt : FloatFormat) : Nat :=
  normalFailures fmt + baselineFailures fmt

def custom41Failures : Thunk Nat := ⟨fun _ =>
  formatFailures custom41⟩

def binary64Failures : Thunk Nat := ⟨fun _ =>
  formatFailures FloatFormat.binary64⟩

def custom64Failures : Thunk Nat := ⟨fun _ =>
  formatFailures custom64⟩

def totalFailures : Thunk Nat := ⟨fun _ =>
  custom41Failures.get + binary64Failures.get + custom64Failures.get +
    NativePair.Addition.totalFailures FloatFormat.binary128 +
    NativePair.Subtraction.totalFailures FloatFormat.binary128 +
    NativePair.Addition.totalFailures NativePair.binary96 +
    NativePair.Subtraction.totalFailures NativePair.binary96⟩

def report : Thunk String := ⟨fun _ =>
  String.intercalate "\n"
    [ s!"custom41: {custom41Failures.get}"
    , s!"binary64: {binary64Failures.get}"
    , s!"custom64: {custom64Failures.get}"
    , NativePair.Addition.report FloatFormat.binary128 "binary128"
    , NativePair.Subtraction.report FloatFormat.binary128 "binary128"
    , NativePair.Addition.report NativePair.binary96 "binary96"
    , NativePair.Subtraction.report NativePair.binary96 "binary96"
    , s!"TOTAL: {totalFailures.get}"
    ]⟩

end FloatLibTests.Regression.BinaryInterchange.TwoWordMul
