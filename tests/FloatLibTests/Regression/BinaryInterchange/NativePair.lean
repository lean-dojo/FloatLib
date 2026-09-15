/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibTests.Regression.BinaryInterchange.NativeHarness

/-!
# Two-word pair-kernel regression checks

This module validates the certified two-word addition, subtraction, multiplication, division,
fused multiply-add, and square-root paths against their general semantic implementations. Every
fixture is a function of the format descriptor, so the same suites run on the binary128 layout and
on the 96-bit layout `FloatFormat.ieee 15 80`, which only the descriptor-generic pair kernel
serves. Each suite also checks that both specialized and baseline routes are exercised.
-/

@[expose] public section

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.NativePair

open Model
open NativeHarness.Pair

/-- A 96-bit IEEE layout with the binary128 exponent field and an 80-bit fraction. -/
abbrev binary96 : FloatFormat :=
  FloatFormat.ieee 15 80

/-- Spread a 64-bit hash over both fraction limbs of `fmt`. -/
@[inline] def fraction (fmt : FloatFormat) (high low : UInt64) : Nat :=
  (high.toNat % 2 ^ (fmt.fracWidth - 64)) * 2 ^ 64 + low.toNat

/-! ## Addition -/

namespace Addition

variable (fmt : FloatFormat)

/-- Same-sign normal pairs accepted by the native equal-exponent path. -/
def acceptedPairs : Array (Model fmt × Model fmt) :=
  #[
    (value fmt false fmt.bias 0, value fmt false fmt.bias 0),
    (value fmt false fmt.bias 1, value fmt false fmt.bias 0),
    (value fmt false fmt.bias 1, value fmt false fmt.bias 2),
    (value fmt false (fmt.bias + 1) fmt.fracMaskNat, value fmt false (fmt.bias + 1) 1),
    (value fmt true fmt.bias 0, value fmt true fmt.bias 0),
    (value fmt true fmt.bias 1, value fmt true fmt.bias 2),
    (value fmt false 1 0, value fmt false 1 fmt.fracMaskNat),
    (value fmt false (fmt.expAllOnesNat - 2) 0,
      value fmt false (fmt.expAllOnesNat - 2) fmt.fracMaskNat)
  ]

/-- Values deliberately handled by the exact baseline. -/
def baselinePairs : Array (Model fmt × Model fmt) :=
  #[
    (value fmt false fmt.bias 0, value fmt true fmt.bias 0),
    (value fmt false fmt.bias 0, value fmt false (fmt.bias + 1) 0),
    (value fmt false 0 1, value fmt false 0 2),
    (posZero fmt, negZero fmt),
    (value fmt false (fmt.expAllOnesNat - 1) 0, value fmt false (fmt.expAllOnesNat - 1) 0),
    (posInf fmt, posOne fmt),
    (posOne fmt, posInf fmt),
    (canonicalNaN fmt, posOne fmt)
  ]

/-- Deterministic pairs spanning sign, exponent, and both fraction words. -/
def generatedPairs : Array (Model fmt × Model fmt) :=
  (Array.range 4096).map fun i =>
    let index := UInt64.ofNat i
    let exponent := i % (fmt.expAllOnesNat - 2) + 1
    let sign := i % 4 ≥ 2
    let x := fraction fmt (index * 0x9e3779b97f4a7c15) (index * 0xbf58476d1ce4e5b9)
    let y :=
      fraction fmt (index * 0x94d049bb133111eb + 0x123456789abcdef)
        (index * 0xd6e8feb86659fd93 + 0xfedcba987654321)
    let yExponent :=
      if i % 3 = 0 then exponent else exponent % (fmt.expAllOnesNat - 2) + 1
    (value fmt sign exponent x, value fmt sign yExponent y)

def allPairs : Array (Model fmt × Model fmt) :=
  acceptedPairs fmt ++ baselinePairs fmt ++ generatedPairs fmt

/-- Bit mismatches between public addition and the exact generic backend. -/
def result : NativeHarness.RoutedResult :=
  NativeHarness.checkRouted (allPairs fmt)
    (fun pair => Model.add pair.1 pair.2)
    (fun pair => Model.AddBackend.generic pair.1 pair.2)
    sameBits
    (fun pair => NativePair.addNormalSameExponent? pair.1 pair.2)

def totalFailures : Nat :=
  (result fmt).totalFailures

/-- Executable fixture report consumed by the two-word regression runner. -/
def report (name : String) : String :=
  (result fmt).report s!"{name} add" "pairs" "native accepted" "exact baseline"

end Addition

/-! ## Subtraction -/

namespace Subtraction

variable (fmt : FloatFormat)

def allPairs : Array (Model fmt × Model fmt) :=
  Addition.allPairs fmt

/-- Bit mismatches between public subtraction and the exact generic backend. -/
def result : NativeHarness.RoutedResult :=
  NativeHarness.checkRouted (allPairs fmt)
    (fun pair => Model.sub pair.1 pair.2)
    (fun pair => Model.AddBackend.generic pair.1 (Model.neg pair.2))
    sameBits
    (fun pair => NativePair.subNormalSameExponent? pair.1 pair.2)

def totalFailures : Nat :=
  (result fmt).totalFailures

/-- Executable fixture report consumed by the two-word regression runner. -/
def report (name : String) : String :=
  (result fmt).report s!"{name} sub" "pairs" "native accepted" "exact baseline"

end Subtraction

/-! ## Multiplication -/

namespace Multiplication

variable (fmt : FloatFormat)

/-- Normal products whose rounded result remains finite and normal. -/
def acceptedPairs : Array (Model fmt × Model fmt) :=
  #[
    (value fmt false fmt.bias 0, value fmt false fmt.bias 0),
    (value fmt false fmt.bias 1, value fmt true fmt.bias 2),
    (value fmt true (fmt.bias + 1) fmt.fracMaskNat, value fmt true (fmt.bias - 1) 1),
    (value fmt true (fmt.bias - fmt.bias / 3) 17, value fmt false (fmt.bias + fmt.bias / 3) 29),
    (value fmt false 1 0, value fmt false (fmt.expAllOnesNat - 2) 0),
    (value fmt false (fmt.expAllOnesNat - 2) 0, value fmt true 1 fmt.fracMaskNat),
    (value fmt false (fmt.bias - fmt.bias / 4) (2 ^ (fmt.fracWidth - 1) + 7),
      value fmt false (fmt.bias + fmt.bias / 4) 31),
    (value fmt true (fmt.bias + fmt.bias / 5) 123456789,
      value fmt false (fmt.bias - fmt.bias / 5) 987654321)
  ]

/-- Values deliberately handled by the exact baseline. -/
def baselinePairs : Array (Model fmt × Model fmt) :=
  #[
    (value fmt false 0 1, value fmt false fmt.bias 0),
    (value fmt false 1 0, value fmt false 1 0),
    (value fmt false (fmt.expAllOnesNat - 1) 0, value fmt false (fmt.expAllOnesNat - 1) 0),
    (posZero fmt, posOne fmt),
    (negZero fmt, posInf fmt),
    (posInf fmt, posOne fmt),
    (canonicalNaN fmt, posOne fmt),
    (posOne fmt, canonicalNaN fmt)
  ]

/-- Deterministic normal pairs whose exponents sum to twice the bias. -/
def generatedPairs : Array (Model fmt × Model fmt) :=
  (Array.range 4096).map fun i =>
    let index := UInt64.ofNat i
    let xExponent := i % (2 * fmt.bias - 2) + 1
    let yExponent := 2 * fmt.bias - xExponent
    let x := fraction fmt (index * 0x9e3779b97f4a7c15) (index * 0xbf58476d1ce4e5b9)
    let y :=
      fraction fmt (index * 0x94d049bb133111eb + 0x123456789abcdef)
        (index * 0xd6e8feb86659fd93 + 0xfedcba987654321)
    (value fmt (i % 4 ≥ 2) xExponent x, value fmt (i % 3 = 0) yExponent y)

def allPairs : Array (Model fmt × Model fmt) :=
  acceptedPairs fmt ++ baselinePairs fmt ++ generatedPairs fmt

/-- Bit mismatches between public multiplication and the exact generic backend. -/
def result : NativeHarness.RoutedResult :=
  NativeHarness.checkRouted (allPairs fmt)
    (fun pair => Model.mul pair.1 pair.2)
    (fun pair => Model.MulBackend.generic pair.1 pair.2)
    sameBits
    (fun pair => NativePair.mulNormalLimb? pair.1 pair.2)

def totalFailures : Nat :=
  (result fmt).totalFailures

/-- Executable fixture report consumed by the native-product regression runner. -/
def report (name : String) : String :=
  (result fmt).report s!"{name} mul" "pairs" "native accepted" "exact baseline"

end Multiplication

/-! ## Division -/

namespace Division

open FloatLib.Numerics.FixedWord

variable (fmt : FloatFormat)

/-- Explicit certified normal results and exact-baseline cases. -/
def fixtures : Array (Model fmt × Model fmt) :=
  #[
    (value fmt false fmt.bias 0, value fmt false fmt.bias 0),
    (value fmt false fmt.bias 1, value fmt true fmt.bias 2),
    (value fmt true (fmt.bias + fmt.bias / 4) fmt.fracMaskNat,
      value fmt false (fmt.bias + fmt.bias / 8) 17),
    (value fmt false 1 0, value fmt true 1 fmt.fracMaskNat),
    (value fmt false (fmt.expAllOnesNat - 1) 29, value fmt false (fmt.expAllOnesNat - 1) 31),
    (value fmt false 0 1, value fmt false fmt.bias 0),
    (value fmt false 1 0, value fmt false (fmt.expAllOnesNat - 1) 0),
    (value fmt false (fmt.expAllOnesNat - 1) 0, value fmt false 1 0),
    (posZero fmt, posOne fmt),
    (posOne fmt, posZero fmt),
    (posInf fmt, posOne fmt),
    (posOne fmt, posInf fmt),
    (canonicalNaN fmt, posOne fmt),
    (posOne fmt, canonicalNaN fmt)
  ]

/-- Deterministic normal pairs whose quotient exponent stays normal. -/
def generated : Array (Model fmt × Model fmt) :=
  (Array.range 4096).map fun i =>
    let index := UInt64.ofNat i
    let span := fmt.bias / 2
    let xExponent := (i * 8191 + 101) % span + fmt.bias / 2
    let yExponent := (i * 4051 + 313) % span + fmt.bias / 2
    let x :=
      fraction fmt (index * 0x9e3779b97f4a7c15 + 0x123456789abcdef)
        (index * 0xbf58476d1ce4e5b9 + 0xfedcba987654321)
    let y :=
      fraction fmt (index * 0x94d049bb133111eb + 0xabcdef012345678)
        (index * 0xd6e8feb86659fd93 + 0x102030405060708)
    (value fmt (i % 4 ≥ 2) xExponent x, value fmt (i % 3 = 0) yExponent y)

def allPairs : Array (Model fmt × Model fmt) :=
  fixtures fmt ++ generated fmt

/-- Bit mismatches between public division and the exact generic backend. -/
def result : NativeHarness.RoutedResult :=
  NativeHarness.checkRouted (allPairs fmt)
    (fun pair => Model.div pair.1 pair.2)
    (fun pair => Model.DivBackend.generic pair.1 pair.2)
    sameBits
    (fun pair => NativePair.divNormal? pair.1 pair.2)

/--
Whether a routed normal division is accepted by the Algorithm D candidate itself.

`divNormal?` remains correct when this check fails because it selects the proved restoring repair.
Keeping this metric separate ensures a performance regression cannot silently turn every normal
division into the cold repair path.
-/
@[inline] def fastCandidateAccepted (pair : Model fmt × Model fmt) : Bool :=
  match NativePair.divNormal? pair.1 pair.2 with
  | none => false
  | some _ =>
      let xWords := NativePair.toWords pair.1
      let yWords := NativePair.toWords pair.2
      let num := NativePair.normalMantissa fmt (NativePair.fracHigh fmt xWords.hi) xWords.lo
      let den := NativePair.normalMantissa fmt (NativePair.fracHigh fmt yWords.hi) yWords.lo
      let shift : CertifiedDivision.CandidateShift :=
        if UInt128.less num den then .extra else .exact
      let fast := CertifiedDivision.candidate fmt.fracWidth num den shift
      CertifiedDivision.certificate fmt.fracWidth num den shift fast.1 fast.2

/-- Routed cases that stay on the fast Algorithm D path. -/
def fastAccepted : Nat :=
  (allPairs fmt).foldl (init := 0) fun count pair =>
    if fastCandidateAccepted fmt pair then count + 1 else count

/-- Routed cases repaired by the proved restoring divider. -/
def repairSelected : Nat :=
  (result fmt).accepted - fastAccepted fmt

/--
Reject a performance regression that makes the proved repair path routine.

The exact acceptance count can move when the deterministic corpus grows, so the regression checks
a ratio rather than freezing one implementation-specific number.
-/
def fastCoverageFailures : Nat :=
  FloatLibTests.Accounting.failureCount
    ((result fmt).accepted != 0 && (result fmt).accepted * 95 ≤ fastAccepted fmt * 100)

def totalFailures : Nat :=
  (result fmt).totalFailures + fastCoverageFailures fmt

/-- Executable fixture report consumed by the native-product regression runner. -/
def report (name : String) : String :=
  String.intercalate "\n"
    [ (result fmt).report s!"{name} div" "pairs" "native accepted" "exact baseline"
    , s!"{name} div fast candidate accepted: {fastAccepted fmt}"
    , s!"{name} div restoring repairs: {repairSelected fmt}"
    ]

end Division

/-! ## Fused multiply-add -/

namespace Fma

variable (fmt : FloatFormat)

/-- Cases accepted by the native route alongside exceptional and differently aligned baseline cases. -/
def fixtures : Array (Model fmt × Model fmt × Model fmt) :=
  #[
    ⟨value fmt false fmt.bias 0, value fmt false fmt.bias 0, value fmt false fmt.bias 0⟩,
    ⟨value fmt false fmt.bias 1, value fmt true fmt.bias 2, value fmt true fmt.bias 3⟩,
    ⟨value fmt true (fmt.bias + 1) fmt.fracMaskNat, value fmt true (fmt.bias - 1) 1,
      value fmt false fmt.bias 7⟩,
    ⟨value fmt false fmt.bias 0, value fmt false fmt.bias 0, value fmt true fmt.bias 0⟩,
    ⟨value fmt false fmt.bias 0, value fmt false fmt.bias 0, value fmt false (fmt.bias + 1) 0⟩,
    ⟨value fmt false 0 1, value fmt false fmt.bias 0, value fmt false 0 1⟩,
    ⟨posInf fmt, posOne fmt, posOne fmt⟩,
    ⟨posOne fmt, canonicalNaN fmt, posOne fmt⟩,
    ⟨posOne fmt, posOne fmt, canonicalNaN fmt⟩
  ]

/-- Deterministic normal triples spanning signs, exponents, fractions, and baseline routes. -/
def generated : Array (Model fmt × Model fmt × Model fmt) :=
  (Array.range 4096).map fun i =>
    let index := UInt64.ofNat i
    let span := fmt.bias / 32
    let xExponent := i % span + (fmt.bias - span)
    let yExponent := (i * 73 + 19) % span + (fmt.bias - span)
    let alignedZExponent := xExponent + yExponent - fmt.bias
    let xSign := i % 4 ≥ 2
    let ySign := i % 2 = 1
    let productSign := Bool.xor xSign ySign
    let zSign := if i % 4 = 0 then !productSign else productSign
    let zExponent :=
      if i % 3 = 0 then alignedZExponent + 1 else alignedZExponent
    let x := fraction fmt (index * 0x9e3779b97f4a7c15) (index * 0xbf58476d1ce4e5b9)
    let y :=
      fraction fmt (index * 0x94d049bb133111eb + 0x123456789abcdef)
        (index * 0xd6e8feb86659fd93 + 0xfedcba987654321)
    let z :=
      fraction fmt (index * 0xd1342543de82ef95 + 0xabcdef012345678)
        (index * 0xa24baed4963ee407 + 0x102030405060708)
    ⟨value fmt xSign xExponent x, value fmt ySign yExponent y, value fmt zSign zExponent z⟩

def allTriples : Array (Model fmt × Model fmt × Model fmt) :=
  fixtures fmt ++ generated fmt

/-- Bit mismatches between public FMA and the exact generic backend. -/
def result : NativeHarness.RoutedResult :=
  NativeHarness.checkRouted (allTriples fmt)
    (fun ⟨x, y, z⟩ => Model.fma x y z)
    (fun ⟨x, y, z⟩ => Model.FmaBackend.generic x y z)
    sameBits
    (fun ⟨x, y, z⟩ => NativePair.fmaNormalSameSignAligned? x y z)

def totalFailures : Nat :=
  (result fmt).totalFailures

/-- Executable fixture report consumed by the native-product regression runner. -/
def report (name : String) : String :=
  (result fmt).report s!"{name} FMA" "triples" "native accepted" "exact baseline"

end Fma

/-! ## Square root -/

namespace Sqrt

variable (fmt : FloatFormat)

/-- Positive-normal native cases plus every exceptional or signed semantic class. -/
def fixtures : Array (Model fmt) :=
  #[
    value fmt false 1 0,
    value fmt false fmt.bias 0,
    value fmt false fmt.bias fmt.fracMaskNat,
    value fmt false (fmt.expAllOnesNat - 1) (2 ^ (fmt.fracWidth - 1) + 17),
    value fmt true fmt.bias 0,
    value fmt true 1 fmt.fracMaskNat,
    posZero fmt,
    negZero fmt,
    value fmt false 0 1,
    posInf fmt,
    negInf fmt,
    canonicalNaN fmt
  ]

/-- Deterministic normal values spanning signs, exponents, and both fraction words. -/
def generated : Array (Model fmt) :=
  (Array.range 4096).map fun i =>
    let index := UInt64.ofNat i
    let exponent := (i * 8191 + 17) % (fmt.expAllOnesNat - 1) + 1
    let x :=
      fraction fmt (index * 0x9e3779b97f4a7c15 + 0x123456789abcdef)
        (index * 0xbf58476d1ce4e5b9 + 0xfedcba987654321)
    value fmt (i % 4 = 3) exponent x

def allInputs : Array (Model fmt) :=
  fixtures fmt ++ generated fmt

/-- Bit mismatches between public square root and the exact generic backend. -/
def result : NativeHarness.RoutedResult :=
  NativeHarness.checkRouted (allInputs fmt)
    Model.sqrt
    Model.SqrtBackend.generic
    sameBits
    NativePair.sqrtNormal?

def totalFailures : Nat :=
  (result fmt).totalFailures

/-- Executable fixture report consumed by the native-product regression runner. -/
def report (name : String) : String :=
  (result fmt).report s!"{name} sqrt" "inputs" "native accepted" "general semantic cases"

end Sqrt

end FloatLibTests.Regression.BinaryInterchange.NativePair
