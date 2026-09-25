/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibTests.Regression.BinaryInterchange.NativeHarness
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Division.Runtime
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Fma.Runtime
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Multiplication.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Add.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Mul.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.FmaWord.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Type
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances

/-!
# Wide-limb regression checks

This module compares the wide-limb addition, subtraction, multiplication, and fused multiply-add
kernels with the exact baseline on 192-, 256-, and 1024-bit IEEE layouts. Every suite mixes
structured operands (zeros, subnormals, the smallest and largest normals, infinities, NaN) with
deterministic pseudo-random normal operands at chosen exponent distances, including the
cancellation, sticky-bit, carry, overflow, and underflow boundaries, and checks that both the limb
kernel and the exact baseline route are exercised. A separate set of explicit 256-bit fixtures
checks the public `ExecFloat.BinaryLimbs` carrier, its planner selections, and all six operations.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.WideLimb

open Model
open FloatLibTests.Regression.BinaryInterchange.NativeHarness
open FloatLib.Floats
open FloatLibTests.Accounting

/-- A 192-bit IEEE layout with 176 fraction bits. -/
abbrev wide192 : FloatFormat := FloatFormat.ieee 15 176

/-- The 256-bit layout with 236 fraction bits. -/
abbrev wide256 : FloatFormat := FloatFormat.ieee 19 236

/-- A 1024-bit IEEE layout with 1004 fraction bits. -/
abbrev wide1024 : FloatFormat := FloatFormat.ieee 19 1004

/-- Compare two values of one format by their complete stored encoding. -/
@[inline] def sameBits {fmt : FloatFormat} (x y : Model fmt) : Bool :=
  x.toNatBits == y.toNatBits

/-- One SplitMix64 output step, for deterministic operand vectors. -/
def mix64 (x : UInt64) : UInt64 :=
  let z := x + 0x9e3779b97f4a7c15
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

/-- A deterministic pseudo-random natural number below `2 ^ bits`. -/
def randomBits (bits seed : Nat) : Nat :=
  let words := (bits + 63) / 64
  ((List.range words).foldl
    (fun acc k => acc + (mix64 (UInt64.ofNat (seed * 1000003 + k))).toNat * 2 ^ (64 * k)) 0) %
    2 ^ bits

/-- A value from its sign, biased exponent, and fraction. -/
@[inline] def value (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat) : Model fmt :=
  Model.ofFields fmt sign exponent fraction

/-- Clamp an exponent field into the normal range `[1, allOnes - 1]`. -/
def clampNormal (fmt : FloatFormat) (exponent : Nat) : Nat :=
  max 1 (min exponent (fmt.expAllOnesNat - 1))

/-- Structured operands covering every encoding class of the format. -/
def structured (fmt : FloatFormat) : Array (Model fmt) :=
  let f := fmt.fracWidth
  let allOnes := fmt.expAllOnesNat
  let top := 2 ^ f - 1
  #[ posZero fmt, negZero fmt, posInf fmt, negInf fmt, canonicalNaN fmt
   , value fmt false 0 1, value fmt true 0 top
   , value fmt false 1 0, value fmt true 1 top, value fmt false 1 1
   , value fmt false fmt.bias 0, value fmt true fmt.bias 1, value fmt false fmt.bias top
   , value fmt false (fmt.bias + 1) 0, value fmt true (fmt.bias - 1) (2 ^ (f - 1))
   , value fmt false (allOnes - 1) top, value fmt true (allOnes - 1) 0
   , value fmt false (allOnes - 2) top, value fmt false 2 (2 ^ (f - 1) + 1) ]

/-- All ordered pairs of structured operands. -/
def structuredPairs (fmt : FloatFormat) : Array (Model fmt × Model fmt) :=
  (structured fmt).flatMap fun x => (structured fmt).map fun y => (x, y)

/-- Exponent distances that reach the exact, sticky, and negligible alignment regimes. -/
def distances (fmt : FloatFormat) : Array Nat :=
  let f := fmt.fracWidth
  #[0, 1, 2, 3, 4, 5, 31, 32, 33, 63, 64, 65, f - 1, f, f + 1, f + 2, f + 3, f + 10, 2 * f]

/-- Deterministic normal pairs for addition and subtraction across signs and distances. -/
def additionPairs (fmt : FloatFormat) (count : Nat) : Array (Model fmt × Model fmt) :=
  let f := fmt.fracWidth
  let allOnes := fmt.expAllOnesNat
  (Array.range count).map fun i =>
    let distance := (distances fmt)[i % (distances fmt).size]!
    let xExponent := clampNormal fmt (randomBits 62 (7 * i + 1) % (allOnes - 2) + 1)
    let yExponent := clampNormal fmt (if i % 2 = 0 then xExponent + distance else xExponent - distance)
    let xFraction := randomBits f (7 * i + 2)
    let yFraction :=
      match i % 5 with
      | 0 => xFraction
      | 1 => (xFraction + 1) % 2 ^ f
      | 2 => 2 ^ f - 1
      | 3 => 0
      | _ => randomBits f (7 * i + 3)
    (value fmt (i % 4 ≥ 2) xExponent xFraction, value fmt (i % 3 = 0) yExponent yFraction)

/-- Deterministic normal pairs for multiplication, including overflow and underflow products. -/
def multiplicationPairs (fmt : FloatFormat) (count : Nat) : Array (Model fmt × Model fmt) :=
  let f := fmt.fracWidth
  let allOnes := fmt.expAllOnesNat
  (Array.range count).map fun i =>
    let xExponent := clampNormal fmt (randomBits 62 (11 * i + 1) % (allOnes - 2) + 1)
    let yExponent :=
      match i % 6 with
      | 0 => clampNormal fmt (2 * fmt.bias - xExponent)
      | 1 => clampNormal fmt (2 * fmt.bias - xExponent + 1)
      | 2 => allOnes - 1
      | 3 => 1
      | _ => clampNormal fmt (randomBits 62 (11 * i + 2) % (allOnes - 2) + 1)
    let xFraction := if i % 7 = 0 then 2 ^ f - 1 else randomBits f (11 * i + 3)
    let yFraction := if i % 7 = 1 then 0 else randomBits f (11 * i + 4)
    (value fmt (i % 4 ≥ 2) xExponent xFraction, value fmt (i % 3 = 0) yExponent yFraction)

/--
Deterministic triples for fused multiply-add across product and addend alignments.

Most triples are normal operands with a normal result, which the wide-limb kernel accepts. Every
eighth triple has an infinite or NaN first operand (exponent field all ones), which the kernel
declines, so the exact baseline route is exercised as well and the report can confirm both routes
ran. Exceptional operands are used rather than overflowing products because the exact baseline
resolves them immediately, whereas an exact product with an exponent near the format maximum
makes the baseline manipulate integers of hundreds of thousands of bits.
-/
def fmaTriples (fmt : FloatFormat) (count : Nat) : Array (Model fmt × Model fmt × Model fmt) :=
  let f := fmt.fracWidth
  let allOnes := fmt.expAllOnesNat
  (Array.range count).map fun i =>
    let xExponent :=
      if i % 8 = 0 then allOnes
      else clampNormal fmt (fmt.bias - 200 + randomBits 62 (13 * i + 1) % 400)
    let yExponent := clampNormal fmt (fmt.bias - 200 + randomBits 62 (13 * i + 2) % 400)
    let productExponent := xExponent + yExponent - fmt.bias
    let distance := (distances fmt)[i % (distances fmt).size]!
    let zExponent := clampNormal fmt
      (if i % 2 = 0 then productExponent + distance else productExponent - distance)
    ⟨value fmt (i % 4 ≥ 2) xExponent (randomBits f (13 * i + 3)),
      value fmt (i % 5 = 0) yExponent (randomBits f (13 * i + 4)),
      value fmt (i % 3 = 0) zExponent (if i % 7 = 0 then 0 else randomBits f (13 * i + 5))⟩

/-- Check one binary operation of the wide-limb kernel against the exact baseline. -/
def checkBinary (fmt : FloatFormat)
    (kernel : Model.WideLimb.Value fmt → Model.WideLimb.Value fmt → Model.WideLimb.Value fmt)
    (fast : Model.WideLimb.Value fmt → Model.WideLimb.Value fmt → Option (Model.WideLimb.Value fmt))
    (reference : Model fmt → Model fmt → Model fmt)
    (pairs : Array (Model fmt × Model fmt)) : RoutedResult :=
  checkRouted pairs
    (fun pair => Model.WideLimb.toModel
      (kernel (Model.WideLimb.ofModel pair.1) (Model.WideLimb.ofModel pair.2)))
    (fun pair => reference pair.1 pair.2)
    sameBits
    (fun pair => fast (Model.WideLimb.ofModel pair.1) (Model.WideLimb.ofModel pair.2))

/-- Check the wide-limb fused multiply-add against the exact baseline. -/
def checkFma (fmt : FloatFormat) (triples : Array (Model fmt × Model fmt × Model fmt)) :
    RoutedResult :=
  checkRouted triples
    (fun ⟨x, y, z⟩ => Model.WideLimb.toModel
      (Model.WideLimb.fma fmt (Model.WideLimb.ofModel x) (Model.WideLimb.ofModel y)
        (Model.WideLimb.ofModel z)))
    (fun ⟨x, y, z⟩ => Model.FmaBackend.generic x y z)
    sameBits
    (fun ⟨x, y, z⟩ => Model.WideLimb.fmaNormal? fmt (Model.WideLimb.ofModel x)
      (Model.WideLimb.ofModel y) (Model.WideLimb.ofModel z))

/-- The four operation suites of one format. -/
structure FormatResult where
  label : String
  add : RoutedResult
  sub : RoutedResult
  mul : RoutedResult
  fma : RoutedResult

/-- Run every suite on one format with the given random-vector length. -/
def runFormat (fmt : FloatFormat) (label : String) (count : Nat) : FormatResult :=
  let addPairs := structuredPairs fmt ++ additionPairs fmt count
  let mulPairs := structuredPairs fmt ++ multiplicationPairs fmt count
  { label
    add := checkBinary fmt (Model.WideLimb.add fmt) (Model.WideLimb.addNormal? fmt false)
      Model.AddBackend.generic addPairs
    sub := checkBinary fmt (Model.WideLimb.sub fmt) (Model.WideLimb.addNormal? fmt true)
      (fun x y => Model.AddBackend.generic x (Model.neg y)) addPairs
    mul := checkBinary fmt (Model.WideLimb.mul fmt) (Model.WideLimb.mulNormal? fmt)
      Model.MulBackend.generic mulPairs
    fma := checkFma fmt (fmaTriples fmt count) }

def FormatResult.totalFailures (result : FormatResult) : Nat :=
  result.add.totalFailures + result.sub.totalFailures + result.mul.totalFailures +
    result.fma.totalFailures

def FormatResult.report (result : FormatResult) : String :=
  String.intercalate "\n"
    [ result.add.report s!"{result.label} add" "pairs" "wide-limb accepted" "exact baseline"
    , result.sub.report s!"{result.label} sub" "pairs" "wide-limb accepted" "exact baseline"
    , result.mul.report s!"{result.label} mul" "pairs" "wide-limb accepted" "exact baseline"
    , result.fma.report s!"{result.label} fma" "triples" "wide-limb accepted" "exact baseline" ]

/-- Results for the three widths. -/
def results : Thunk (Array FormatResult) := ⟨fun _ =>
  #[ runFormat wide192 "wide192" 4096
   , runFormat wide256 "wide256" 4096
   , runFormat wide1024 "wide1024" 1024 ]⟩

/-! ## Public limb carrier -/

/-- The public 256-bit IEEE type stored in eight 32-bit limbs. -/
abbrev Limb256 := ExecFloat.BinaryLimbs 19 236

private abbrev Limb256Family := ExecFloat.Binary.LimbFamily 19 236

/-- All six public operations select the certified limb-carrier candidates. -/
example :
    [ (ExecFloat.Add.selectedCandidate (F := Limb256Family)).kind
    , (ExecFloat.Sub.selectedCandidate (F := Limb256Family)).kind
    , (ExecFloat.Mul.selectedCandidate (F := Limb256Family)).kind
    , (ExecFloat.Div.selectedCandidate (F := Limb256Family)).kind
    , (ExecFloat.Sqrt.selectedCandidate (F := Limb256Family)).kind
    , (ExecFloat.Fma.selectedCandidate (F := Limb256Family)).kind
    ] = [.wideLimbs, .wideLimbs, .wideLimbs, .wideLimbs, .wideLimbs, .wideLimbs] := by
  rfl

/-- Construct a public limb value from explicit encoded fields. -/
def limbValue (sign : Bool) (exponent fraction : Nat) : Limb256 :=
  ExecFloat.Binary.ofModel (Model.ofFields wide256 sign exponent fraction)

/-- Compare every stored bit, including zero signs and NaN payloads. -/
def sameLimbBits (x y : Limb256) : Bool :=
  ExecFloat.Binary.toNatBits x == ExecFloat.Binary.toNatBits y

/--
Public operations checked against explicit expected encodings.

The carry fixtures cross each limb boundary. With `u = 2⁻²³⁶`, the FMA fixture must retain
`(1 + u) * (1 - u) - 1 = -u²`; separately rounded multiplication would lose that residual.
For `1 / 3`, the nearest 237-bit significand is `(2²³⁸ - 1) / 3`.
Directed checks select the adjacent significand explicitly for both signs. Subnormal division
checks both tie parities, and square roots just below a midpoint check the remainder comparison.
-/
def publicChecks : Thunk (List (String × Bool)) := ⟨fun _ =>
  let f := wide256.fracWidth
  let bias := wide256.bias
  let zero := limbValue false 0 0
  let negativeZero := limbValue true 0 0
  let one := limbValue false bias 0
  let two := limbValue false (bias + 1) 0
  let three := limbValue false (bias + 1) (2 ^ (f - 1))
  let four := limbValue false (bias + 2) 0
  let negativeOne := limbValue true bias 0
  let ulp := limbValue false (bias - f) 0
  let aboveOne := limbValue false bias 1
  let belowOne := limbValue false (bias - 1) (2 ^ f - 2)
  let subnormal := limbValue false 0 1
  let infinity := limbValue false wide256.expAllOnesNat 0
  let largest := limbValue false (wide256.expAllOnesNat - 1) (2 ^ f - 1)
  let nan : Limb256 := ExecFloat.Binary.ofModel (Model.canonicalNaN wide256)
  let signalingNaN := limbValue true wide256.expAllOnesNat 5
  let quietNaN := limbValue true wide256.expAllOnesNat (2 ^ (f - 1) + 5)
  let thirdFraction := (2 ^ (f + 2) - 1) / 3 - 2 ^ f
  let directedThird (mode : IEEERoundingMode) (negative : Bool) :=
    Model.WideLimb.toModel (Model.WideLimb.divWithRounding wide256 mode
      (Model.WideLimb.ofModel (Model.ofFields wide256 negative bias 0))
      (Model.WideLimb.ofModel (ExecFloat.Binary.toModel three)))
  [ ("codec",
      (structured wide256).all fun x =>
        ExecFloat.Binary.toNatBits (ExecFloat.Binary.ofModel x : Limb256) == x.toNatBits)
  , ("codecTruncation", ExecFloat.Binary.toNatBits
      (ExecFloat.Binary.ofNatBits (2 ^ 256 + 1) : Limb256) == 1)
  , ("literal", sameLimbBits (3 : Limb256) three)
  , ("addCarry64", sameLimbBits (limbValue false bias (2 ^ 64 - 1) + ulp)
      (limbValue false bias (2 ^ 64)))
  , ("addCarry128", sameLimbBits (limbValue false bias (2 ^ 128 - 1) + ulp)
      (limbValue false bias (2 ^ 128)))
  , ("addCarry192", sameLimbBits (limbValue false bias (2 ^ 192 - 1) + ulp)
      (limbValue false bias (2 ^ 192)))
  , ("addCarryExponent", sameLimbBits (limbValue false bias (2 ^ f - 1) + ulp) two)
  , ("addSubnormal", sameLimbBits (subnormal + subnormal) (limbValue false 0 2))
  , ("addOverflow", sameLimbBits (largest + largest) infinity)
  , ("subCancellation", sameLimbBits (aboveOne - one) ulp)
  , ("subSubnormal", sameLimbBits
      (limbValue false 1 0 - limbValue false 0 (2 ^ f - 1)) subnormal)
  , ("subSignedZero", sameLimbBits (negativeZero - zero) negativeZero)
  , ("mulRounding", sameLimbBits (aboveOne * aboveOne) (limbValue false bias 2))
  , ("mulSubnormal", sameLimbBits (subnormal * two) (limbValue false 0 2))
  , ("mulSignedZero", sameLimbBits (negativeZero * one) negativeZero)
  , ("mulOverflow", sameLimbBits (largest * two) infinity)
  , ("fmaResidual", sameLimbBits (ExecFloat.fma aboveOne belowOne negativeOne)
      (limbValue true (bias - 2 * f) 0))
  , ("fmaSignedZero",
      sameLimbBits (ExecFloat.fma negativeZero one negativeZero) negativeZero)
  , ("fmaInvalid", sameLimbBits (ExecFloat.fma infinity zero one) nan)
  , ("divExact", sameLimbBits (four / two) two)
  , ("divRounding", sameLimbBits (one / three)
      (limbValue false (bias - 2) thirdFraction))
  , ("divTowardZero", sameBits (directedThird .towardZero false)
      (Model.ofFields wide256 false (bias - 2) thirdFraction))
  , ("divTowardPositive", sameBits (directedThird .towardPositiveInfinity false)
      (Model.ofFields wide256 false (bias - 2) (thirdFraction + 1)))
  , ("divTowardNegative", sameBits (directedThird .towardNegativeInfinity false)
      (Model.ofFields wide256 false (bias - 2) thirdFraction))
  , ("divNegativeTowardPositive", sameBits (directedThird .towardPositiveInfinity true)
      (Model.ofFields wide256 true (bias - 2) thirdFraction))
  , ("divNegativeTowardNegative", sameBits (directedThird .towardNegativeInfinity true)
      (Model.ofFields wide256 true (bias - 2) (thirdFraction + 1)))
  , ("divSubnormalHalfEven", sameLimbBits (subnormal / two) zero)
  , ("divSubnormalHalfOdd", sameLimbBits (limbValue false 0 3 / two) (limbValue false 0 2))
  , ("divSubnormalSignedZero", sameLimbBits (limbValue true 0 1 / two) negativeZero)
  , ("divByZero", sameLimbBits (one / zero) infinity)
  , ("divInvalid", sameLimbBits (zero / zero) nan)
  , ("divNaNPayload", sameLimbBits (signalingNaN / one) quietNaN)
  , ("sqrtExact", sameLimbBits (ExecFloat.sqrt four) two)
  , ("sqrtBelowEvenMidpoint", sameLimbBits (ExecFloat.sqrt aboveOne) one)
  , ("sqrtBelowOddMidpoint", sameLimbBits (ExecFloat.sqrt (limbValue false bias 3)) aboveOne)
  , ("sqrtSignedZero", sameLimbBits (ExecFloat.sqrt negativeZero) negativeZero)
  , ("sqrtInvalid", sameLimbBits (ExecFloat.sqrt negativeOne) nan)
  , ("sqrtNaNPayload", sameLimbBits (ExecFloat.sqrt signalingNaN) quietNaN) ]⟩

def totalFailures : Thunk Nat := ⟨fun _ =>
  results.get.foldl (fun total result => total + result.totalFailures) 0 +
    countWhereFailures publicChecks.get (·.2)⟩

/-- Executable fixture report consumed by the regression runner. -/
def report : Thunk String := ⟨fun _ =>
  let publicRows := publicChecks.get.map fun (name, passes) =>
    (s!"wide256 public {name}", failureCount passes)
  String.intercalate "\n"
    ((results.get.map FormatResult.report).toList ++ [renderFailureReport publicRows])⟩

end FloatLibTests.Regression.BinaryInterchange.WideLimb
