/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Runtime
public import FloatLib.Floats.Formats.OCP.MX.Standard.DotProduct.Runtime
public import FloatLibTests.Accounting

/-!
# OCP MX 1.0 conversion and dot-product regressions

Fixed endpoint and midpoint expectations come from the OFP8 1.0 and MX 1.0 encodings.
Complete FP6 and asymmetric INT8 decoding checks use independent rational tables. Block checks
exercise the standard 32-lane representation, NaN scales, signed zero, mixed-profile dots,
and cancellation of products larger than binary32 before the single final rounding.

References:
<https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>,
<https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>.
-/

@[expose] public section

set_option compiler.extract_closed false

namespace FloatLibTests.Conformance.Formats.MXStandard

open FloatLib.Numerics
open FloatLib.Floats.Formats.OCP.MX
open Standard FloatLibTests.Accounting

/-- Quantize a rational scalar and expose its element code. -/
def scalar (profile : Profile) (mode : OverflowMode) (value : Rat) : Nat :=
  (Element.quantize profile mode (.finite (SignedRat.ofRat value))).toNat

/-- Normative scalar overflow, saturation, ties, signed zero, and E8M0 endpoints. -/
def scalarFailures : Thunk Nat := ⟨fun _ => countFailures
  [ scalar .e4m3 .overflow 464 == 126
  , scalar .e4m3 .overflow 465 == 127
  , scalar .e4m3 .saturate 1000 == 126
  , scalar .e4m3 .overflow (-464) == 254
  , scalar .e4m3 .overflow (-465) == 255
  , scalar .e4m3 .overflow (-896) == 255
  , (Element.quantize .e4m3 .overflow (.infinity true)).toNat == 255
  , scalar .e5m2 .overflow 61439 == 123
  , scalar .e5m2 .overflow 61440 == 124
  , scalar .e5m2 .saturate 61440 == 123
  , scalar .e5m2 .overflow (-61440) == 252
  , scalar .e2m1 .saturate 5 == 6
  , scalar .e2m1 .saturate 100 == 7
  , scalar .e2m3 .saturate 100 == 31
  , scalar .e3m2 .saturate 100 == 31
  , scalar .int8 .saturate (-2) == 128
  , scalar .int8 .saturate 2 == 127
  , (Element.quantize .e2m1 .saturate (.finite SignedRat.negZero)).toNat == 8
  , (Element.quantize .e5m2 .saturate (.infinity true)).toNat == 251
  , (Element.quantize .e5m2 .overflow (.infinity true)).toNat == 252
  , E8M0.exponent? (E8M0.ofNatBits 0) == some (-127)
  , E8M0.exponent? (E8M0.ofNatBits 254) == some 127
  , E8M0.exponent? (E8M0.ofNatBits 255) == none ]⟩

/-- Positive E2M3 values in units of 1/8; sign is bit 5. -/
def e2m3Numerators : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 60]

/-- Positive E3M2 values in units of 1/16; sign is bit 5. -/
def e3m2Numerators : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 28,
    32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320, 384, 448]

/-- Compare every FP6 code against an independent positive-magnitude table. -/
def fp6Failures (profile : Profile) (table : Array Nat) (denominator : Rat) : Nat :=
  countWhereFailures (List.range 64) fun code =>
    let magnitude : Rat := table[code % 32]! / denominator
    let expected := if code < 32 then magnitude else -magnitude
    decide (Element.toRat? (profile := profile) (BitVec.ofNat profile.width code) =
      some expected)

/-- Every FP6 and MX INT8 code has the independently tabulated numerical value. -/
def decodeFailures : Thunk Nat := ⟨fun _ =>
  fp6Failures .e2m3 e2m3Numerators 8 + fp6Failures .e3m2 e3m2Numerators 16 +
    countWhereFailures (List.range 256) fun (code : Nat) =>
      let integer : Int := if code < 128 then (code : Int) else (code : Int) - 256
      decide (Element.toRat? (profile := .int8) (BitVec.ofNat 8 code) =
        some ((integer : Rat) / 64))⟩

/-- Form a standard block with the same explicitly encoded element in every lane. -/
def constantBlock (profile : Profile) (scale code : Nat) : Block profile :=
  ⟨E8M0.ofNatBits scale, Vector.replicate 32 (BitVec.ofNat profile.width code)⟩

/-- Standard block conversion and one-rounding accumulation across lanes and blocks. -/
def blockFailures : Thunk Nat := ⟨fun _ =>
  let ones := constantBlock .int8 127 64
  let left := constantBlock .e2m1 128 2
  let right := constantBlock .int8 126 64
  let negativeZeros := constantBlock .e2m1 128 8
  let alternatingLeft : Block .e2m1 := ⟨E8M0.ofNatBits 128,
    Vector.ofFn fun lane => if lane.val % 2 = 0 then 2 else 4⟩
  let alternatingRight : Block .int8 := ⟨E8M0.ofNatBits 126,
    Vector.ofFn fun lane => if lane.val % 2 = 0 then 64 else 128⟩
  let largeLeft : Vector (Block .int8) 3 := Vector.ofFn fun lane =>
    if lane.val = 0 then constantBlock .int8 254 64
    else if lane.val = 1 then ones else constantBlock .int8 254 192
  let largeRight : Vector (Block .int8) 3 := Vector.ofFn fun lane =>
    if lane.val = 1 then ones else constantBlock .int8 254 64
  let input := Vector.replicate 32 (SignedRat.ofRat 1)
  let converted := quantizeFinite .e2m1 .saturate input
  countFailures
    [ decide (left.values.size = 32)
    , decide ((left.decodeLane 0).finite?.map SignedRat.value = some 2)
    , decide ((negativeZeros.decodeLane 0).finite? = some SignedRat.negZero)
    , decide ((Block.nan .e2m1).decodeLane 0 = .exceptional .nan)
    , decide (Block.ofArray? (profile := .e2m1) (E8M0.ofNatBits 127) #[] = none)
    , decide (converted.scale = E8M0.ofNatBits 125)
    , converted.values[0].toNat == 6
    , decide ((converted.decodeLane 0).finite?.map SignedRat.value = some 1)
    , (dot left right).toNatBits == 0x42000000
    , (dot alternatingLeft alternatingRight).toNatBits == 0xc2400000
    , (dotGeneral largeLeft largeRight).toNatBits == 0x42000000
    , (dot ones (Block.nan .int8)).isNaN
    , (dotGeneral (Vector.replicate 0 ones) (Vector.replicate 0 ones)).toNatBits == 0 ]⟩

/-- Conversion and dot-product failure count included in the core executable suite. -/
def totalFailures : Thunk Nat := ⟨fun _ =>
  scalarFailures.get + decodeFailures.get + blockFailures.get⟩

/-- Report the standard MX checks separately from nominal low-bit packaging. -/
def report : Thunk ReportSection := ⟨fun _ =>
  let failures := totalFailures.get
  { title := "OCP MX standard conversion and dots"
    body := s!"TOTAL: {failures}"
    failures }⟩

end FloatLibTests.Conformance.Formats.MXStandard
