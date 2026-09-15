/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Core
public import FloatLibTests.Regression.BinaryInterchange.Harness
public import FloatLibTests.Regression.BinaryInterchange.NativeBinary64
public import FloatLibTests.Regression.BinaryInterchange.NativePair
import FloatLib.Kernels.FixedWord.Product.Runtime

/-!
# Multi-width regression checks for verified arithmetic backends

These executable checks exercise each product-capacity tier through public arithmetic:

* one-limb multiplication used by binary64 and smaller formats;
* two-limb multiplication used by suitable one-word encodings;
* four-limb two-word multiplication for the binary128 and 96-bit layouts, and the general
  arbitrary-precision route for wider formats;
* fixed-word two-word restoring square root against the exact general semantics;
* scalar fused multiply-add and complex multiplication;
* policy-aware FP4, FP6, FP8, FNUZ, TF32, and mixed-precision accumulation.

Expected products use ordinary natural-number multiplication.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.NativeProduct

open FloatLib

open Model
open Harness
open FloatLibTests.Accounting

/-- A custom format whose 161-bit significand exceeds the two-limb backend. -/
abbrev wide160 : FloatFormat :=
  FloatFormat.ieee 19 160

/-- A custom 512-bit format with a 493-bit significand. -/
abbrev wide512 : FloatFormat :=
  FloatFormat.ieee 19 492

def productBackendFailures : Thunk Nat := ⟨fun _ =>
  let cases : List (Nat × Nat) :=
    [ (2 ^ 53 - 1, 2 ^ 52 + 17)
    , (2 ^ 64 - 1, 2 ^ 64 - 3)
    , (2 ^ 64, 2 ^ 64 + 1)
    , (2 ^ 113 - 1, 2 ^ 112 + 37)
    , (2 ^ 128 - 1, 2 ^ 127 + 41)
    ]
  countWhereFailures cases fun operands =>
    let actual :=
      if operands.1 < 2 ^ 64 && operands.2 < 2 ^ 64 then
        (FloatLib.Numerics.FixedWord.mul64
          (UInt64.ofNat operands.1) (UInt64.ofNat operands.2)).toNat
      else
        (FloatLib.Numerics.FixedWord.mul128
          (FloatLib.Numerics.FixedWord.UInt128.ofNat operands.1)
          (FloatLib.Numerics.FixedWord.UInt128.ofNat operands.2)).toNat
    actual == operands.1 * operands.2⟩

def roundingBackendFailures : Thunk Nat := ⟨fun _ =>
  let cases : List (Nat × Nat) :=
    [ (0, 0)
    , (1, 1)
    , (3, 1)
    , (5, 1)
    , (2 ^ 53 + 12345, 29)
    , (2 ^ 64 - 1, 64)
    , (2 ^ 64, 64)
    , (2 ^ 112 + 987654321, 73)
    , (2 ^ 160 + 123456789, 117)
    ]
  countWhereFailures cases fun input =>
    FloatLib.Numerics.FixedWord.roundShiftRightEvenNat input.1 input.2 ==
      Numerics.roundShiftRightEven input.1 input.2⟩

def mulMatches (fmt : FloatFormat) (left right : Numerics.Dyadic) : Bool :=
  let x := Model.roundDyadic fmt left
  let y := Model.roundDyadic fmt right
  match Model.toDyadic? x, Model.toDyadic? y with
  | some dx, some dy =>
      let expected := Model.roundDyadic fmt
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      sameBits (Model.mul x y) expected
  | _, _ => false

def fmaMatches (fmt : FloatFormat) (left right addend : Numerics.Dyadic) : Bool :=
  let x := Model.roundDyadic fmt left
  let y := Model.roundDyadic fmt right
  let z := Model.roundDyadic fmt addend
  match Model.toDyadic? x, Model.toDyadic? y, Model.toDyadic? z with
  | some dx, some dy, some dz =>
      let product : Numerics.Dyadic :=
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      let expected := Model.roundDyadic fmt (Model.addDyadic product dz)
      sameBits (Model.fma x y z) expected
  | _, _, _ => false

def scalarArithmeticFailures : Thunk Nat := ⟨fun _ =>
  failureCount (mulMatches FloatFormat.binary64
    { negative := false, significand := 2 ^ 52 + 12345, exponent := -(52 : Int) }
    { negative := true, significand := 2 ^ 52 + 54321, exponent := -(53 : Int) }) +
  failureCount (fmaMatches FloatFormat.binary64
    { negative := false, significand := 2 ^ 52 + 12345, exponent := -(52 : Int) }
    { negative := true, significand := 2 ^ 52 + 54321, exponent := -(53 : Int) }
    { negative := false, significand := 2 ^ 51 + 333, exponent := -(51 : Int) }) +
  failureCount (mulMatches FloatFormat.binary128
    { negative := false, significand := 2 ^ 112 + 123456789, exponent := -(112 : Int) }
    { negative := true, significand := 2 ^ 112 + 987654321, exponent := -(113 : Int) }) +
  failureCount (fmaMatches FloatFormat.binary128
    { negative := false, significand := 2 ^ 112 + 123456789, exponent := -(112 : Int) }
    { negative := true, significand := 2 ^ 112 + 987654321, exponent := -(113 : Int) }
    { negative := false, significand := 2 ^ 111 + 777, exponent := -(111 : Int) }) +
  failureCount (mulMatches FloatFormat.binary256
    { negative := false, significand := 2 ^ 236 + 123456789, exponent := -(236 : Int) }
    { negative := true, significand := 2 ^ 236 + 987654321, exponent := -(237 : Int) }) +
  failureCount (fmaMatches FloatFormat.binary256
    { negative := false, significand := 2 ^ 236 + 123456789, exponent := -(236 : Int) }
    { negative := true, significand := 2 ^ 236 + 987654321, exponent := -(237 : Int) }
    { negative := false, significand := 2 ^ 235 + 777, exponent := -(235 : Int) }) +
  failureCount (mulMatches wide160
    { negative := false, significand := 2 ^ 160 + 123456789, exponent := -(160 : Int) }
    { negative := true, significand := 2 ^ 160 + 987654321, exponent := -(161 : Int) }) +
  failureCount (fmaMatches wide160
    { negative := false, significand := 2 ^ 160 + 123456789, exponent := -(160 : Int) }
    { negative := true, significand := 2 ^ 160 + 987654321, exponent := -(161 : Int) }
    { negative := false, significand := 2 ^ 159 + 777, exponent := -(159 : Int) }) +
  failureCount (mulMatches wide512
    { negative := false, significand := 2 ^ 492 + 123456789, exponent := -(492 : Int) }
    { negative := true, significand := 2 ^ 492 + 987654321, exponent := -(493 : Int) }) +
  failureCount (fmaMatches wide512
    { negative := false, significand := 2 ^ 492 + 123456789, exponent := -(492 : Int) }
    { negative := true, significand := 2 ^ 492 + 987654321, exponent := -(493 : Int) }
    { negative := false, significand := 2 ^ 491 + 777, exponent := -(491 : Int) })⟩

@[noinline] def roundedProduct (fmt : FloatFormat) (x y : Model fmt) : Model fmt :=
  match Model.toDyadic? x, Model.toDyadic? y with
  | some dx, some dy =>
      Model.roundDyadic fmt
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
  | _, _ => Model.canonicalNaN fmt

/-- Compute the expected rounded complex product without duplicating scalar product decoding. -/
@[noinline] def expectedComplexProduct {fmt : FloatFormat}
    (x y : ExecComplex fmt) : ExecComplex fmt :=
  { re := Model.sub (roundedProduct fmt x.re y.re) (roundedProduct fmt x.im y.im)
    im := Model.add (roundedProduct fmt x.re y.im) (roundedProduct fmt x.im y.re) }

/-- Compare executable complex multiplication with its independently rounded specification. -/
@[noinline] def encodedComplexMulMatches {fmt : FloatFormat}
    (x y : ExecComplex fmt) : Bool :=
  ExecComplex.mul x y == expectedComplexProduct x y

def complexMulMatches (fmt : FloatFormat)
    (a b c d : Numerics.Dyadic) : Bool :=
  let x : ExecComplex fmt :=
    { re := Model.roundDyadic fmt a
      im := Model.roundDyadic fmt b }
  let y : ExecComplex fmt :=
    { re := Model.roundDyadic fmt c
      im := Model.roundDyadic fmt d }
  encodedComplexMulMatches x y

def complexArithmeticFailures : Thunk Nat := ⟨fun _ =>
  failureCount (complexMulMatches FloatFormat.binary128
    { negative := false, significand := 2 ^ 112 + 11, exponent := 0 }
    { negative := true, significand := 2 ^ 111 + 13, exponent := 0 }
    { negative := false, significand := 2 ^ 110 + 17, exponent := 0 }
    { negative := false, significand := 2 ^ 109 + 19, exponent := 0 }) +
  failureCount (complexMulMatches FloatFormat.binary256
    { negative := false, significand := 2 ^ 236 + 11, exponent := 0 }
    { negative := true, significand := 2 ^ 235 + 13, exponent := 0 }
    { negative := false, significand := 2 ^ 234 + 17, exponent := 0 }
    { negative := false, significand := 2 ^ 233 + 19, exponent := 0 }) +
  failureCount (complexMulMatches wide160
    { negative := false, significand := 2 ^ 160 + 11, exponent := 0 }
    { negative := true, significand := 2 ^ 159 + 13, exponent := 0 }
    { negative := false, significand := 2 ^ 158 + 17, exponent := 0 }
    { negative := false, significand := 2 ^ 157 + 19, exponent := 0 }) +
  failureCount (complexMulMatches wide512
    { negative := false, significand := 2 ^ 492 + 11, exponent := 0 }
    { negative := true, significand := 2 ^ 491 + 13, exponent := 0 }
    { negative := false, significand := 2 ^ 490 + 17, exponent := 0 }
    { negative := false, significand := 2 ^ 489 + 19, exponent := 0 })⟩

namespace PolicyAware

open FloatLib.Numerics

def mulMatches (fmt : FloatFormat) (policy : QuantizationPolicy)
    (left right : Numerics.Dyadic) : Bool :=
  let x := Model.Policy.roundDyadic fmt policy 17 left
  let y := Model.Policy.roundDyadic fmt policy 17 right
  match Model.toDyadic? x, Model.toDyadic? y with
  | some dx, some dy =>
      let expected := Model.Policy.roundDyadic fmt policy 17
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      Model.mulFinite? fmt policy 17 x y == some expected
  | _, _ => false

def fmaMatches (fmt : FloatFormat) (policy : QuantizationPolicy)
    (left right addend : Numerics.Dyadic) : Bool :=
  let x := Model.Policy.roundDyadic fmt policy 23 left
  let y := Model.Policy.roundDyadic fmt policy 23 right
  let z := Model.Policy.roundDyadic fmt policy 23 addend
  match Model.toDyadic? x, Model.toDyadic? y,
      Model.toDyadic? z with
  | some dx, some dy, some dz =>
      let product : Numerics.Dyadic :=
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      let expected := Model.Policy.roundDyadic fmt policy 23
        (Model.addDyadic product dz)
      Model.fmaFinite? fmt policy 23 x y z == some expected
  | _, _, _ => false

def formatMatches (fmt : FloatFormat) : Bool :=
  let left : Numerics.Dyadic := { negative := false, significand := 3, exponent := -1 }
  let right : Numerics.Dyadic := { negative := true, significand := 5, exponent := -2 }
  let addend : Numerics.Dyadic := { negative := false, significand := 1, exponent := -1 }
  mulMatches fmt QuantizationPolicy.nearestEven left right &&
  fmaMatches fmt QuantizationPolicy.nearestEven left right addend &&
  mulMatches fmt QuantizationPolicy.saturating left right &&
  fmaMatches fmt QuantizationPolicy.flushToZero left right addend

def mixedAccumulationMatches : Thunk Bool := ⟨fun _ =>
  let storage := FloatFormat.e4m3fn
  let accumulator := FloatFormat.binary128
  let policy := QuantizationPolicy.nearestEven
  let x := Model.Policy.roundDyadic storage policy 0
    { negative := false, significand := 7, exponent := -2 }
  let y := Model.Policy.roundDyadic storage policy 0
    { negative := true, significand := 9, exponent := -3 }
  let acc := Model.Policy.roundDyadic accumulator policy 0
    { negative := false, significand := 2 ^ 112 + 29, exponent := -(112 : Int) }
  match Model.toDyadic? x, Model.toDyadic? y,
      Model.toDyadic? acc with
  | some dx, some dy, some da =>
      let product : Numerics.Dyadic :=
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      let expected := Model.Policy.roundDyadic accumulator policy 0
        (Model.addDyadic product da)
      Model.mulAddFinite? storage accumulator policy 0 x y acc == some expected
  | _, _, _ => false⟩

def failures : Thunk Nat := ⟨fun _ =>
  failureCount (formatMatches FloatFormat.e2m1) +
  failureCount (formatMatches FloatFormat.e2m3) +
  failureCount (formatMatches FloatFormat.e3m2) +
  failureCount (formatMatches FloatFormat.e4m3fn) +
  failureCount (formatMatches FloatFormat.e4m3fnuz) +
  failureCount (formatMatches FloatFormat.e5m2) +
  failureCount (formatMatches FloatFormat.e5m2fnuz) +
  failureCount (formatMatches FloatFormat.tf32) +
  failureCount (formatMatches FloatFormat.binary256) +
  failureCount (formatMatches wide512) +
  failureCount mixedAccumulationMatches.get⟩

end PolicyAware

def totalFailures : Thunk Nat := ⟨fun _ =>
  roundingBackendFailures.get +
  productBackendFailures.get +
  scalarArithmeticFailures.get +
  complexArithmeticFailures.get +
  PolicyAware.failures.get +
  NativeBinary64Fma.totalFailures.get +
  NativePair.Multiplication.totalFailures FloatFormat.binary128 +
  NativePair.Division.totalFailures FloatFormat.binary128 +
  NativePair.Fma.totalFailures FloatFormat.binary128 +
  NativePair.Sqrt.totalFailures FloatFormat.binary128 +
  NativePair.Multiplication.totalFailures NativePair.binary96 +
  NativePair.Division.totalFailures NativePair.binary96 +
  NativePair.Fma.totalFailures NativePair.binary96 +
  NativePair.Sqrt.totalFailures NativePair.binary96⟩

def report : Thunk String := ⟨fun _ =>
  String.intercalate "\n"
    [ s!"roundingBackends: {roundingBackendFailures.get}"
    , s!"productBackends: {productBackendFailures.get}"
    , s!"scalarArithmetic: {scalarArithmeticFailures.get}"
    , s!"complexArithmetic: {complexArithmeticFailures.get}"
    , s!"policyAwareArithmetic: {PolicyAware.failures.get}"
    , NativeBinary64Fma.report.get
    , NativePair.Multiplication.report FloatFormat.binary128 "binary128"
    , NativePair.Division.report FloatFormat.binary128 "binary128"
    , NativePair.Fma.report FloatFormat.binary128 "binary128"
    , NativePair.Sqrt.report FloatFormat.binary128 "binary128"
    , NativePair.Multiplication.report NativePair.binary96 "binary96"
    , NativePair.Division.report NativePair.binary96 "binary96"
    , NativePair.Fma.report NativePair.binary96 "binary96"
    , NativePair.Sqrt.report NativePair.binary96 "binary96"
    , s!"TOTAL: {totalFailures.get}"
    ]⟩

end FloatLibTests.Regression.BinaryInterchange.NativeProduct
