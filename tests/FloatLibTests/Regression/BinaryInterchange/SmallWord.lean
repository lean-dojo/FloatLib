/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLibTests.Regression.BinaryInterchange.Harness
public import FloatLibTests.Regression.BinaryInterchange.NativeBinary64

/-!
# Reusable one-word regression checks

These checks exercise the shared native-storage decoder and the one-word add, subtract,
multiplication, division, FMA, and square-root paths. The tested formats span binary16, bfloat16,
the small-arithmetic precision boundary, and a custom 64-bit encoding.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.SmallWordFinite

open Model
open Harness
open FloatLibTests.Accounting

abbrev custom37 : FloatFormat :=
  FloatFormat.ieee 6 30

abbrev custom64 : FloatFormat :=
  FloatFormat.ieee 2 61

def samples (fmt : FloatFormat) : Array (Model fmt) :=
  #[
    posZero fmt,
    negZero fmt,
    posMinSubnormal fmt,
    neg (posMinSubnormal fmt),
    ofFields fmt false 0 (fmt.fracMaskNat / 2 + 1),
    ofFields fmt true 1 0,
    posOne fmt,
    negOne fmt,
    ofFields fmt false fmt.bias (fmt.fracMaskNat / 3),
    ofFields fmt true (fmt.bias + 1) (fmt.fracMaskNat / 5),
    maxFinite fmt false,
    maxFinite fmt true,
    posInf fmt,
    negInf fmt,
    canonicalNaN fmt
  ]

def decoderFailures (fmt : FloatFormat) : Nat :=
  countWhereFailures (samples fmt) fun x =>
    NativeSmallWordFinite.decode? x == FiniteKernel.decode? x

def addFailures (fmt : FloatFormat) : Nat :=
  countPairFailures (samples fmt) (samples fmt) fun x y =>
    sameBits (AddBackend.word x y) (AddBackend.generic x y)

def subFailures (fmt : FloatFormat) : Nat :=
  countPairFailures (samples fmt) (samples fmt) fun x y =>
    sameBits (AddBackend.subWord x y) (AddBackend.generic x (neg y))

def fmaSamples (fmt : FloatFormat) : Array (Model fmt) :=
  #[
    posZero fmt,
    negZero fmt,
    posMinSubnormal fmt,
    neg (posMinSubnormal fmt),
    posOne fmt,
    negOne fmt,
    ofFields fmt false fmt.bias (fmt.fracMaskNat / 3),
    ofFields fmt true (fmt.bias + 1) (fmt.fracMaskNat / 5),
    maxFinite fmt false,
    posInf fmt,
    canonicalNaN fmt
  ]

def fmaFailures (fmt : FloatFormat) : Nat :=
  countTripleFailures (fmaSamples fmt) (fmaSamples fmt) (fmaSamples fmt) fun x y z =>
    sameBits (FmaBackend.word x y z) (FmaBackend.generic x y z)

def sqrtFailures (fmt : FloatFormat) : Nat :=
  countWhereFailures (samples fmt) fun x =>
    sameBits (SqrtBackend.word x) (SqrtBackend.generic x)

def formatFailures (fmt : FloatFormat) : Nat :=
  decoderFailures fmt +
    addFailures fmt +
    subFailures fmt +
    fmaFailures fmt +
    sqrtFailures fmt

def binary16Failures : Thunk Nat := ⟨fun _ =>
  formatFailures FloatFormat.binary16⟩

def bfloat16Failures : Thunk Nat := ⟨fun _ =>
  formatFailures FloatFormat.bfloat16⟩

def custom37Failures : Thunk Nat := ⟨fun _ =>
  formatFailures custom37⟩

def custom64Failures : Thunk Nat := ⟨fun _ =>
  formatFailures custom64⟩

def totalFailures : Thunk Nat := ⟨fun _ =>
  binary16Failures.get + bfloat16Failures.get + custom37Failures.get + custom64Failures.get +
    NativeBinary64Addition.totalFailures.get⟩

def report : Thunk String := ⟨fun _ =>
  String.intercalate "\n"
    [ s!"binary16: {binary16Failures.get}"
    , s!"bfloat16: {bfloat16Failures.get}"
    , s!"custom37: {custom37Failures.get}"
    , s!"custom64: {custom64Failures.get}"
    , NativeBinary64Addition.report.get
    , s!"TOTAL: {totalFailures.get}"
    ]⟩

end FloatLibTests.Regression.BinaryInterchange.SmallWordFinite

/-! ## Multiplication -/

namespace FloatLibTests.Regression.BinaryInterchange.SmallWordMul

open Model

abbrev custom37 : FloatFormat :=
  FloatFormat.ieee 6 30

abbrev custom40 : FloatFormat :=
  FloatFormat.ieee 8 31

def ordinaryNormals (fmt : FloatFormat) : Array (Model fmt × Model fmt) :=
  #[
    (posOne fmt, posOne fmt),
    (negOne fmt, posOne fmt),
    (ofFields fmt false fmt.bias (2 ^ (fmt.fracWidth - 1)),
      ofFields fmt false fmt.bias (2 ^ (fmt.fracWidth - 2))),
    (ofFields fmt true (fmt.bias + 1) (fmt.fracMaskNat / 3),
      ofFields fmt false (fmt.bias - 1) (fmt.fracMaskNat / 5))
  ]

def normalFailures (fmt : FloatFormat) : Nat :=
  Harness.binaryRouteFailures (ordinaryNormals fmt)
    NativeSmallWordMul.mulNormal? MulBackend.word MulBackend.generic true

def baselineFailures (fmt : FloatFormat) : Nat :=
  Harness.binaryRouteFailures (Harness.productBaselinePairs fmt)
    NativeSmallWordMul.mulNormal? MulBackend.word MulBackend.generic false

def formatFailures (fmt : FloatFormat) : Nat :=
  normalFailures fmt + baselineFailures fmt

def binary16Failures : Thunk Nat := ⟨fun _ =>
  formatFailures FloatFormat.binary16⟩

def bfloat16Failures : Thunk Nat := ⟨fun _ =>
  formatFailures FloatFormat.bfloat16⟩

def custom37Failures : Thunk Nat := ⟨fun _ =>
  formatFailures custom37⟩

def custom40Failures : Thunk Nat := ⟨fun _ =>
  formatFailures custom40⟩

def totalFailures : Thunk Nat := ⟨fun _ =>
  binary16Failures.get + bfloat16Failures.get + custom37Failures.get + custom40Failures.get⟩

def report : Thunk String := ⟨fun _ =>
  String.intercalate "\n"
    [ s!"binary16: {binary16Failures.get}"
    , s!"bfloat16: {bfloat16Failures.get}"
    , s!"custom37: {custom37Failures.get}"
    , s!"custom40: {custom40Failures.get}"
    , s!"TOTAL: {totalFailures.get}"
    ]⟩

end FloatLibTests.Regression.BinaryInterchange.SmallWordMul

/-! ## Division -/

namespace FloatLibTests.Regression.BinaryInterchange.SmallWordDiv

open Model

abbrev custom37 : FloatFormat :=
  FloatFormat.ieee 6 30

/-- The first fraction width beyond the old small-arithmetic capacity. -/
abbrev custom40 : FloatFormat :=
  FloatFormat.ieee 8 31

/-- A wider custom significand that still fits a single stored word. -/
abbrev custom49 : FloatFormat :=
  FloatFormat.ieee 8 40

/-- The largest fraction possible in a one-word IEEE layout. -/
abbrev custom64 : FloatFormat :=
  FloatFormat.ieee 2 61

/-- The largest exponent field possible in a one-word layout. -/
abbrev wideExponent : FloatFormat :=
  FloatFormat.ieee 62 1

def ordinaryNormals (fmt : FloatFormat) : Array (Model fmt × Model fmt) :=
  #[
    (posOne fmt, posOne fmt),
    (negOne fmt, posOne fmt),
    (ofFields fmt false fmt.bias (2 ^ (fmt.fracWidth - 1)),
      ofFields fmt false fmt.bias (2 ^ (fmt.fracWidth - 2))),
    (ofFields fmt true (fmt.bias + 1) (fmt.fracMaskNat / 3),
      ofFields fmt false fmt.bias (fmt.fracMaskNat / 5))
  ]

def baselinePairs (fmt : FloatFormat) : Array (Model fmt × Model fmt) :=
  #[
    (posZero fmt, posOne fmt),
    (posOne fmt, posZero fmt),
    (posMinSubnormal fmt, posOne fmt),
    (posOne fmt, posMinSubnormal fmt),
    (ofFields fmt false 1 0, ofFields fmt false (fmt.bias + 1) 0),
    (maxFinite fmt false, ofFields fmt false (fmt.bias - 1) 0),
    (posInf fmt, posOne fmt),
    (canonicalNaN fmt, posOne fmt)
  ]

def normalFailures (fmt : FloatFormat) : Nat :=
  Harness.binaryRouteFailures (ordinaryNormals fmt)
    NativeSmallWordDiv.divNormal? DivBackend.word DivBackend.generic true

def baselineFailures (fmt : FloatFormat) : Nat :=
  Harness.binaryRouteFailures (baselinePairs fmt)
    NativeSmallWordDiv.divNormal? DivBackend.word DivBackend.generic false

/-- Compare every pair of value classes, including negative zero and both infinities. -/
def classFailures (fmt : FloatFormat) : Nat :=
  FloatLibTests.Accounting.countPairFailures
    (SmallWordFinite.samples fmt) (SmallWordFinite.samples fmt) fun x y =>
      Harness.sameBits (DivBackend.word x y) (DivBackend.generic x y)

def formatFailures (fmt : FloatFormat) : Nat :=
  normalFailures fmt + baselineFailures fmt + classFailures fmt

def binary16Failures : Thunk Nat := ⟨fun _ =>
  formatFailures FloatFormat.binary16⟩

def bfloat16Failures : Thunk Nat := ⟨fun _ =>
  formatFailures FloatFormat.bfloat16⟩

def custom37Failures : Thunk Nat := ⟨fun _ =>
  formatFailures custom37⟩

def custom40Failures : Thunk Nat := ⟨fun _ => formatFailures custom40⟩

def custom49Failures : Thunk Nat := ⟨fun _ => formatFailures custom49⟩

def custom64Failures : Thunk Nat := ⟨fun _ => formatFailures custom64⟩

/-- Check inexact quotients and both exponent-field endpoints at the widest exponent capacity. -/
def wideExponentFailures : Thunk Nat := ⟨fun _ =>
  let fmt := wideExponent
  let threeHalves := ofFields fmt false fmt.bias 1
  let minimumNormal := ofFields fmt false 1 0
  let maximum := maxFinite fmt false
  let roundedPairs := #[
    (posOne fmt, threeHalves, ofFields fmt false (fmt.bias - 1) 1),
    (negOne fmt, threeHalves, ofFields fmt true (fmt.bias - 1) 1),
    (ofFields fmt false (2 * fmt.bias) 0, threeHalves,
      ofFields fmt false (2 * fmt.bias - 1) 1),
    (minimumNormal, ofFields fmt false (fmt.bias - 1) 1, ofFields fmt false 1 1),
    (minimumNormal, minimumNormal, posOne fmt),
    (maximum, maximum, posOne fmt)
  ]
  formatFailures fmt +
    FloatLibTests.Accounting.countWhereFailures roundedPairs fun (x, y, expected) =>
      match NativeSmallWordDiv.divNormal? x y with
      | none => false
      | some result =>
          Harness.sameBits result expected &&
            Harness.sameBits (DivBackend.word x y) expected &&
            Harness.sameBits (DivBackend.generic x y) expected⟩

def totalFailures : Thunk Nat := ⟨fun _ =>
  binary16Failures.get + bfloat16Failures.get + custom37Failures.get +
    custom40Failures.get + custom49Failures.get + custom64Failures.get + wideExponentFailures.get⟩

def report : Thunk String := ⟨fun _ =>
  String.intercalate "\n"
    [ s!"binary16: {binary16Failures.get}"
    , s!"bfloat16: {bfloat16Failures.get}"
    , s!"custom37: {custom37Failures.get}"
    , s!"custom40: {custom40Failures.get}"
    , s!"custom49: {custom49Failures.get}"
    , s!"custom64: {custom64Failures.get}"
    , s!"wide exponent: {wideExponentFailures.get}"
    , s!"TOTAL: {totalFailures.get}"
    ]⟩

end FloatLibTests.Regression.BinaryInterchange.SmallWordDiv
