/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibTests.Regression.BinaryInterchange.NativeHarness

/-!
# Native binary64 regression checks

This module validates the certified binary64 addition, subtraction, division, fused
multiply-add, and square-root paths against their general semantic implementations. Each suite
also checks that both specialized and baseline routes are exercised where applicable.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.NativeBinary64Addition

open Model
open NativeHarness.Binary64

/-- Same-sign normal pairs accepted by the native equal-exponent path. -/
def acceptedPairs : Array (UInt64 × UInt64) :=
  #[
    (0x3ff0000000000000, 0x3ff0000000000000),
    (0x3ff0000000000001, 0x3ff0000000000000),
    (0x3ff0000000000001, 0x3ff0000000000002),
    (0x400fffffffffffff, 0x4000000000000001),
    (0xbff0000000000000, 0xbff0000000000000),
    (0xbff0000000000001, 0xbff0000000000002),
    (0x0010000000000000, 0x001fffffffffffff),
    (0x7fd0000000000000, 0x7fdfffffffffffff)
  ]

/-- Values deliberately handled by the exact baseline. -/
def baselinePairs : Array (UInt64 × UInt64) :=
  #[
    (0x3ff0000000000000, 0xbff0000000000000),
    (0x3ff0000000000000, 0x4000000000000000),
    (0x0000000000000001, 0x0000000000000002),
    (0x0000000000000000, 0x8000000000000000),
    (0x7fe0000000000000, 0x7fe0000000000000),
    (0x7ff0000000000000, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x7ff0000000000000),
    (0x7ff8000000000001, 0x3ff0000000000000)
  ]

/-- Deterministic normal pairs spanning sign, exponent, and fraction fields. -/
def generatedPairs : Thunk (Array (UInt64 × UInt64)) := ⟨fun _ =>
  (Array.range 4096).map fun i =>
    let index := UInt64.ofNat i
    let exponent := (index % 2045) + 1
    let sign : UInt64 :=
      if i % 4 < 2 then 0 else 0x8000000000000000
    let xFraction :=
      (index * 0x9e3779b97f4a7c15) &&& 0x000fffffffffffff
    let yFraction :=
      (index * 0xbf58476d1ce4e5b9 + 0x123456789abcdef) &&&
        0x000fffffffffffff
    let yExponent :=
      if i % 3 = 0 then exponent else (exponent % 2045) + 1
    (sign ||| (exponent <<< 52) ||| xFraction,
      sign ||| (yExponent <<< 52) ||| yFraction)⟩

def allPairs : Thunk (Array (UInt64 × UInt64)) := ⟨fun _ =>
  acceptedPairs ++ baselinePairs ++ generatedPairs.get⟩

/-- Bit mismatches between public addition and the exact generic backend. -/
def result : Thunk NativeHarness.RoutedResult := ⟨fun _ =>
  NativeHarness.checkRouted allPairs.get
    (fun pair =>
      Model.add (fromBits pair.1) (fromBits pair.2))
    (fun pair =>
      Model.AddBackend.generic (fromBits pair.1) (fromBits pair.2))
    sameBits
    fun pair =>
    let x := fromBits pair.1
    let y := fromBits pair.2
    NativeBinary64.addNormalSameExponent? x y⟩

def totalFailures : Thunk Nat := ⟨fun _ =>
  result.get.totalFailures⟩

/-- Executable fixture report consumed by the one-word finite runner. -/
def report : Thunk String := ⟨fun _ =>
  result.get.report "binary64 add" "pairs" "native accepted" "exact baseline"⟩

end FloatLibTests.Regression.BinaryInterchange.NativeBinary64Addition

/-! ## Subtraction -/

namespace FloatLibTests.Regression.BinaryInterchange.NativeBinary64Subtraction

open Model
open NativeHarness.Binary64

/-- Normal pairs exercising signed Sterbenz and native-addition routes. -/
def acceptedPairs : Array (UInt64 × UInt64) :=
  #[
    (0x3ff8000000000000, 0x3ff0000000000000),
    (0x4004000000000000, 0x4000000000000000),
    (0x40123456789abcde, 0x4010000000000000),
    (0x402fffffffffffff, 0x4028000000000000),
    (0x3ff0000000000000, 0x3ff8000000000000),
    (0x0018000000000000, 0x0010000000000000),
    (0x4000000000000000, 0x3ff8000000000000),
    (0x3ff8000000000000, 0x4000000000000000),
    (0x0020000000000000, 0x0018000000000000),
    (0x0018000000000000, 0x0020000000000000),
    (0xbff8000000000000, 0xbff0000000000000),
    (0xc004000000000000, 0xc000000000000000),
    (0xbff0000000000000, 0xbff8000000000000),
    (0xc000000000000000, 0xbff8000000000000),
    (0x3ff8000000000000, 0xbff0000000000000),
    (0xbff8000000000000, 0x3ff0000000000000)
  ]

/-- Signed, subnormal, distant-exponent, infinity, and NaN pairs handled by the exact baseline. -/
def baselinePairs : Array (UInt64 × UInt64) :=
  #[
    (0xbff8000000000000, 0x3ff0000000000000),
    (0x3ff8000000000000, 0xbff0000000000000),
    (0x0000000000000001, 0x0010000000000000),
    (0x0010000000000000, 0x0000000000000001),
    (0x3ff0000000000000, 0x4020000000000000),
    (0x7ff0000000000000, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x7ff0000000000000),
    (0x7ff8000000000001, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x7ff0000000000001),
    (0x0000000000000000, 0x8000000000000000)
  ]

/-- Deterministic signed normal pairs spanning exponent and fraction fields. -/
def generatedPairs : Thunk (Array (UInt64 × UInt64)) := ⟨fun _ =>
  (Array.range 4096).map fun i =>
    let index := UInt64.ofNat i
    let exponent := (index % 2046) + 1
    let xFraction :=
      (index * 0x9e3779b97f4a7c15) &&& 0x000fffffffffffff
    let yFraction :=
      (index * 0xbf58476d1ce4e5b9 + 0x123456789abcdef) &&&
        0x000fffffffffffff
    let xMagnitude := (exponent <<< 52) ||| xFraction
    let yMagnitude :=
      if i % 3 = 0 then
        (exponent <<< 52) ||| yFraction
      else
        (((exponent + 17) % 2046 + 1) <<< 52) ||| yFraction
    let xBits :=
      if i % 4 = 1 || i % 4 = 3 then
        xMagnitude ||| 0x8000000000000000
      else
        xMagnitude
    let yBits :=
      if i % 4 = 1 || i % 4 = 2 then
        yMagnitude ||| 0x8000000000000000
      else
        yMagnitude
    (xBits, yBits)⟩

def allPairs : Thunk (Array (UInt64 × UInt64)) := ⟨fun _ =>
  acceptedPairs ++ baselinePairs ++ generatedPairs.get⟩

/-- Bit mismatches between production subtraction and its exact generic specification. -/
def mismatches : Thunk Nat := ⟨fun _ =>
  Harness.mismatchCount allPairs.get
    (fun pair => Model.sub (fromBits pair.1) (fromBits pair.2))
    (fun pair =>
      let x := fromBits pair.1
      let y := fromBits pair.2
      Model.AddBackend.generic x (Model.neg y))
    sameBits⟩

def signedSterbenzAccepted : Thunk Nat := ⟨fun _ =>
  Harness.acceptedCount allPairs.get fun pair =>
    let x := fromBits pair.1
    let y := fromBits pair.2
    NativeBinary64.subSignedSterbenz? x y⟩

def positiveSterbenzAccepted : Thunk Nat := ⟨fun _ =>
  allPairs.get.foldl (init := 0) fun count pair =>
    let x := fromBits pair.1
    let y := fromBits pair.2
    match NativeBinary64.subSignedSterbenz? x y with
    | none => count
    | some _ =>
        if !NativeBinary64.signBit pair.1 then count + 1 else count⟩

def negativeSterbenzAccepted : Thunk Nat := ⟨fun _ =>
  signedSterbenzAccepted.get - positiveSterbenzAccepted.get⟩

def nativeAdditionAccepted : Thunk Nat := ⟨fun _ =>
  Harness.acceptedCount allPairs.get fun pair =>
    let x := fromBits pair.1
    let y := fromBits pair.2
    match NativeBinary64.subSignedSterbenz? x y with
    | some _ => none
    | none => NativeBinary64.addNormalSameExponent? x (NativeBinary64.negate y)⟩

def baselineCases : Thunk Nat := ⟨fun _ =>
  allPairs.get.size - signedSterbenzAccepted.get - nativeAdditionAccepted.get⟩

def sameExponentAccepted : Thunk Nat := ⟨fun _ =>
  allPairs.get.foldl (init := 0) fun count pair =>
    let x := fromBits pair.1
    let y := fromBits pair.2
    match NativeBinary64.subSignedSterbenz? x y with
    | none => count
    | some _ =>
        if NativeBinary64.expField pair.1 ==
            NativeBinary64.expField pair.2 then
          count + 1
        else
          count⟩

def adjacentExponentAccepted : Thunk Nat := ⟨fun _ =>
  signedSterbenzAccepted.get - sameExponentAccepted.get⟩

def coverageFailures : Thunk Nat := ⟨fun _ =>
  Harness.missingCoverage
    [ positiveSterbenzAccepted.get
    , negativeSterbenzAccepted.get
    , nativeAdditionAccepted.get
    , baselineCases.get
    , sameExponentAccepted.get
    , adjacentExponentAccepted.get
    ]⟩

/-- Aggregate mismatch and route-coverage failures. -/
def totalFailures : Thunk Nat := ⟨fun _ =>
  mismatches.get + coverageFailures.get⟩

/-- Executable fixture report consumed by CI. -/
def report : Thunk String := ⟨fun _ =>
  String.intercalate "\n"
    [ s!"pairs: {allPairs.get.size}",
      s!"signed Sterbenz accepted: {signedSterbenzAccepted.get}",
      s!"positive Sterbenz accepted: {positiveSterbenzAccepted.get}",
      s!"negative Sterbenz accepted: {negativeSterbenzAccepted.get}",
      s!"native-addition accepted: {nativeAdditionAccepted.get}",
      s!"same-exponent accepted: {sameExponentAccepted.get}",
      s!"adjacent-exponent accepted: {adjacentExponentAccepted.get}",
      s!"exact baseline: {baselineCases.get}",
      s!"mismatches: {mismatches.get}",
      s!"TOTAL: {totalFailures.get}" ]⟩

end FloatLibTests.Regression.BinaryInterchange.NativeBinary64Subtraction

/-! ## Division -/

namespace FloatLibTests.Regression.BinaryInterchange.NativeBinary64Division

open Model
open NativeHarness.Binary64

/-- Pairs covering signed zero, subnormals, overflow, infinities, and NaN policy. -/
def boundaryPairs : Array (UInt64 × UInt64) :=
  #[
    (0x0000000000000000, 0x0000000000000000),
    (0x8000000000000000, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x0000000000000000),
    (0xbff0000000000000, 0x8000000000000000),
    (0x0000000000000001, 0x7fefffffffffffff),
    (0x7fefffffffffffff, 0x0000000000000001),
    (0x0010000000000000, 0x7fefffffffffffff),
    (0x7fefffffffffffff, 0x0010000000000000),
    (0x7ff0000000000000, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x7ff0000000000000),
    (0x7ff0000000000000, 0x7ff0000000000000),
    (0x7ff0000000000001, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x7ff8000000000001),
    (0x3ff0000000000000, 0x4000000000000000),
    (0xbff0000000000000, 0x4008000000000000)
  ]

/-- Deterministic finite pairs spanning signs, exponents, and fraction fields. -/
def generatedPairs : Thunk (Array (UInt64 × UInt64)) := ⟨fun _ =>
  (Array.range 4096).map fun i =>
    let index := UInt64.ofNat i
    let xState :=
      index * (0x9e3779b97f4a7c15 : UInt64) + 0x243f6a8885a308d3
    let yState :=
      index * (0xbf58476d1ce4e5b9 : UInt64) + 0x13198a2e03707344
    let xBits :=
      (xState &&& 0x7fefffffffffffff) ||| 0x0010000000000000
    let yBits :=
      (yState &&& 0x7fefffffffffffff) ||| 0x0010000000000000
    (xBits, yBits)⟩

def allPairs : Thunk (Array (UInt64 × UInt64)) := ⟨fun _ =>
  boundaryPairs ++ generatedPairs.get⟩

/-- Bit mismatches between the production dispatcher and its proved generic specification. -/
def result : Thunk NativeHarness.RoutedResult := ⟨fun _ =>
  NativeHarness.checkRouted allPairs.get
    (fun pair => Model.div (fromBits pair.1) (fromBits pair.2))
    (fun pair =>
      Model.DivBackend.generic (fromBits pair.1) (fromBits pair.2))
    sameBits
    fun pair =>
    let x := fromBits pair.1
    let y := fromBits pair.2
    NativeBinary64.divNormal? x y⟩

/-- Aggregate mismatch and route-coverage failures. -/
def totalFailures : Thunk Nat := ⟨fun _ =>
  result.get.totalFailures⟩

/-- Executable fixture report consumed by CI. -/
def report : Thunk String := ⟨fun _ =>
  result.get.report "binary64 div" "pairs" "native accepted" "exact baseline"⟩

end FloatLibTests.Regression.BinaryInterchange.NativeBinary64Division

/-! ## Fused multiply-add -/

namespace FloatLibTests.Regression.BinaryInterchange.NativeBinary64Fma

open Model
open NativeHarness.Binary64

@[noinline] def sameSignCandidate (x y z : Value) : Option Value :=
  NativeBinary64.fmaNormalSameSignAligned? x y z

@[noinline] def oppositeSignCandidate (x y z : Value) : Option Value :=
  NativeBinary64.fmaNormalOppositeSignAligned? x y z

@[noinline] def publicFma (x y z : Value) : Value :=
  Model.fma x y z

@[noinline] def genericFma (x y z : Value) : Value :=
  Model.FmaBackend.generic x y z

/-- Cases accepted by the native route alongside exceptional and differently aligned baseline cases. -/
def fixtures : Array (UInt64 × UInt64 × UInt64) :=
  #[
    ⟨0x3ff0000000000000, 0x3ff0000000000000, 0x3ff0000000000000⟩,
    ⟨0x3ff0000000000001, 0x3ff0000000000002, 0x3ff0000000000003⟩,
    ⟨0xbff0000000000001, 0x3ff0000000000002, 0xbff0000000000003⟩,
    ⟨0xbff0000000000001, 0xbff0000000000002, 0x3ff0000000000003⟩,
    ⟨0x3ff0000000000000, 0x3ff0000000000000, 0xbff0000000000000⟩,
    ⟨0x3ff0000000000000, 0x3ff0000000000000, 0x4000000000000000⟩,
    ⟨0x0000000000000001, 0x3ff0000000000000, 0x0000000000000001⟩,
    ⟨0x7ff0000000000000, 0x3ff0000000000000, 0x3ff0000000000000⟩,
    ⟨0x3ff0000000000000, 0x7ff8000000000001, 0x3ff0000000000000⟩,
    ⟨0x3ff0000000000000, 0x3ff0000000000000, 0x7ff0000000000000⟩
  ]

/-- Deterministic normal triples spanning signs, exponents, fractions, and baseline routes. -/
def generated : Thunk (Array (UInt64 × UInt64 × UInt64)) := ⟨fun _ =>
  (Array.range 4096).map fun i =>
    let index := UInt64.ofNat i
    let xExponent := (index % 127) + 960
    let yExponent := ((index * 73 + 19) % 127) + 960
    let alignedZExponent := xExponent + yExponent - 1023
    let xSign := i % 4 == 2 || i % 4 == 3
    let ySign := i % 2 == 1
    let productSign := Bool.xor xSign ySign
    let zSign := if i % 4 == 0 then !productSign else productSign
    let aligned := i % 3 != 0
    let zExponent :=
      if aligned then alignedZExponent else alignedZExponent + 1
    let xFraction :=
      (index * 0x9e3779b97f4a7c15) &&& 0x000fffffffffffff
    let yFraction :=
      (index * 0xbf58476d1ce4e5b9 + 0x123456789abcdef) &&&
        0x000fffffffffffff
    let zFraction :=
      (index * 0x94d049bb133111eb + 0x0fedcba98765432) &&&
        0x000fffffffffffff
    ⟨normalBits xSign xExponent xFraction,
      normalBits ySign yExponent yFraction,
      normalBits zSign zExponent zFraction⟩⟩

def allTriples : Thunk (Array (UInt64 × UInt64 × UInt64)) := ⟨fun _ =>
  fixtures ++ generated.get⟩

/-- Bit mismatches between public FMA and the exact generic backend. -/
def mismatches : Thunk Nat := ⟨fun _ =>
  Harness.mismatchCount allTriples.get
    (fun ⟨xBits, yBits, zBits⟩ =>
      publicFma (fromBits xBits) (fromBits yBits) (fromBits zBits))
    (fun ⟨xBits, yBits, zBits⟩ =>
      genericFma (fromBits xBits) (fromBits yBits) (fromBits zBits))
    sameBits⟩

def sameSignAccepted : Thunk Nat := ⟨fun _ =>
  Harness.acceptedCount allTriples.get fun ⟨xBits, yBits, zBits⟩ =>
    sameSignCandidate (fromBits xBits) (fromBits yBits) (fromBits zBits)⟩

def oppositeSignAccepted : Thunk Nat := ⟨fun _ =>
  Harness.acceptedCount allTriples.get fun ⟨xBits, yBits, zBits⟩ =>
    oppositeSignCandidate (fromBits xBits) (fromBits yBits) (fromBits zBits)⟩

def baselineCases : Thunk Nat := ⟨fun _ =>
  allTriples.get.size - sameSignAccepted.get - oppositeSignAccepted.get⟩

def coverageFailures : Thunk Nat := ⟨fun _ =>
  Harness.missingCoverage
    [sameSignAccepted.get, oppositeSignAccepted.get, baselineCases.get]⟩

def totalFailures : Thunk Nat := ⟨fun _ =>
  mismatches.get + coverageFailures.get⟩

/-- Executable fixture report consumed by the native-product runner. -/
def report : Thunk String := ⟨fun _ =>
  String.intercalate "\n"
    [ s!"binary64 FMA triples: {allTriples.get.size}"
    , s!"binary64 FMA same-sign accepted: {sameSignAccepted.get}"
    , s!"binary64 FMA opposite-sign accepted: {oppositeSignAccepted.get}"
    , s!"binary64 FMA exact baseline: {baselineCases.get}"
    , s!"binary64 FMA mismatches: {mismatches.get}"
    , s!"binary64 FMA TOTAL: {totalFailures.get}"
    ]⟩

end FloatLibTests.Regression.BinaryInterchange.NativeBinary64Fma

/-! ## Square root -/

namespace FloatLibTests.Regression.BinaryInterchange.NativeBinary64Sqrt

open Model
open NativeHarness.Binary64

/-- Exceptional, boundary, normal, and subnormal binary64 fixtures. -/
def fixtures : Array UInt64 :=
  #[
    0x0000000000000000, 0x8000000000000000,
    0x7ff0000000000000, 0xfff0000000000000,
    0x7ff0000000000001, 0x7ff8000000000001,
    0x0000000000000001, 0x0000000000000002,
    0x000fffffffffffff, 0x0010000000000000,
    0x0010000000000001, 0x3ca0000000000000,
    0x3fd0000000000000, 0x3fe0000000000000,
    0x3ff0000000000000, 0x4000000000000000,
    0x4008000000000000, 0x4010000000000000,
    0x4022000000000000, 0x4330000000000000,
    0x5fefffffffffffff, 0x7fefffffffffffff,
    0xbff0000000000000, 0xc000000000000000
  ]

/-- Deterministic samples spanning exponent and fraction fields. -/
def generatedFixtures : Thunk (Array UInt64) := ⟨fun _ =>
  (Array.range 1024).map fun i =>
    let exponent := (i * 811 + 1) % 0x800
    let fraction :=
      ((UInt64.ofNat i * (0x9e3779b97f4a7c15 : UInt64)) ^^^
        (UInt64.ofNat i <<< 29)) &&& 0x000fffffffffffff
    (UInt64.ofNat exponent <<< 52) ||| fraction⟩

def allFixtures : Thunk (Array UInt64) := ⟨fun _ =>
  fixtures ++ generatedFixtures.get⟩

/-- Bit mismatches between the native and compact generic dispatchers. -/
def mismatches : Thunk Nat := ⟨fun _ =>
  Harness.mismatchCount allFixtures.get
    (fun bits => NativeBinary64.sqrt (fromBits bits))
    (fun bits => Model.SqrtBackend.generic (fromBits bits))
    sameBits⟩

/-- Aggregate bit-for-bit regression failures. -/
def totalFailures : Thunk Nat := ⟨fun _ =>
  mismatches.get⟩

/-- Executable fixture report consumed by CI. -/
def report : Thunk String := ⟨fun _ =>
  Harness.mismatchReport "binary64 sqrt" "fixtures" allFixtures.get.size totalFailures.get⟩

end FloatLibTests.Regression.BinaryInterchange.NativeBinary64Sqrt
