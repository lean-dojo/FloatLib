/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.CodedDot
public import FloatLib.Floats.Formats.OCP.MX.Standard.ErrorBounds
public import FloatLibTests.Accounting

/-!
# OCP MX 1.0 conversion and dot-product regressions

Fixed endpoint and midpoint expectations come from the OFP8 1.0 and MX 1.0 encodings.
Complete FP6 and asymmetric INT8 decoding checks use independent rational tables. Block checks
exercise the standard 32-element blocks as stored tensors of the general block format: NaN scales,
signed zero, mixed-profile dots, and cancellation of products larger than binary32 before the
single final rounding.

References:
<https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>,
<https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>.

Reference: OCP 8-bit Floating Point Specification (OFP8), revision 1.0, §5.1; OCP Microscaling
Formats (MX) Specification v1.0, §§5.2–5.4 and 6.1–6.3.
-/

@[expose] public section

set_option compiler.extract_closed false

namespace FloatLibTests.Conformance.Formats.MXStandard

open FloatLib.Numerics
open FloatLib.Floats.Formats
open FloatLib.Floats.Formats.OCP.MX
open Standard FloatLibTests.Accounting

/-- Quantize a rational scalar and expose its element code. -/
def scalar (profile : Profile) (overflow : OverflowMode) (value : Rat) : Nat :=
  (Element.quantize profile (.finite (SignedRat.ofRat value)) overflow).toNat

/-- Normative scalar overflow, saturation, ties, signed zero, and E8M0 endpoints. -/
def scalarFailures : Thunk Nat := ⟨fun _ => countFailures
  [ scalar .e4m3 .native 464 == 126
  , scalar .e4m3 .native 465 == 127
  , scalar .e4m3 .saturate 1000 == 126
  , scalar .e4m3 .native (-464) == 254
  , scalar .e4m3 .native (-465) == 255
  , scalar .e4m3 .native (-896) == 255
  , (Element.quantize .e4m3 (.infinity true) (overflow := .native)).toNat == 255
  , scalar .e5m2 .native 61439 == 123
  , scalar .e5m2 .native 61440 == 124
  , scalar .e5m2 .saturate 61440 == 123
  , scalar .e5m2 .native (-61440) == 252
  , scalar .e2m1 .saturate 5 == 6
  , scalar .e2m1 .saturate 100 == 7
  , scalar .e2m3 .saturate 100 == 31
  , scalar .e3m2 .saturate 100 == 31
  , scalar .int8 .saturate (-2) == 128
  , scalar .int8 .saturate 2 == 127
  , (Element.quantize .e2m1 (.finite SignedRat.negZero)).toNat == 8
  , (Element.quantize .e5m2 (.infinity true)).toNat == 251
  , (Element.quantize .e5m2 (.infinity true) (overflow := .native)).toNat == 252
  , E8M0.exponent? (E8M0.ofNatBits 0) == some (-127)
  , E8M0.exponent? (E8M0.ofNatBits 254) == some 127
  , E8M0.exponent? (E8M0.ofNatBits 255) == none ]⟩

/-- Positive E2M3 values in units of 1/8. The sign is bit 5. -/
def e2m3Numerators : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 60]

/-- Positive E3M2 values in units of 1/16. The sign is bit 5. -/
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

/-- The block shape of one standard block: 32 elements in one group. -/
abbrev oneBlock : Fin 32 → Unit := fun _ => ()

/-- Form a standard 32-element block with the scale code and one element code in every lane. -/
def constantBlock (profile : Profile) (scale code : Nat) :
    Block.Tensor (format oneBlock profile) where
  scales := (fun _ => E8M0.ofNatBits scale, ())
  elements _ := BitVec.ofNat profile.width code

/-- Three standard blocks: positions are pairs of a block and a lane. -/
abbrev threeBlocks : Fin 3 × Fin 32 → Fin 3 := Prod.fst

/-- The positions of three blocks, block by block. -/
def threeBlockOrder : List (Fin 3 × Fin 32) :=
  (List.finRange 3).flatMap fun block => (List.finRange 32).map fun lane => (block, lane)

/-- Standard block conversion and one-rounding accumulation across lanes and blocks. -/
def blockFailures : Thunk Nat := ⟨fun _ =>
  let ones := constantBlock .int8 127 64
  let left := constantBlock .e2m1 128 2
  let right := constantBlock .int8 126 64
  let negativeZeros := constantBlock .e2m1 128 8
  let nanBlock := constantBlock .int8 255 0
  let alternatingLeft : Block.Tensor (format oneBlock .e2m1) :=
    { scales := (fun _ => E8M0.ofNatBits 128, ())
      elements := fun lane => if lane.val % 2 = 0 then 2 else 4 }
  let alternatingRight : Block.Tensor (format oneBlock .int8) :=
    { scales := (fun _ => E8M0.ofNatBits 126, ())
      elements := fun lane => if lane.val % 2 = 0 then 64 else 128 }
  let largeLeft : Block.Tensor (format threeBlocks .int8) :=
    { scales := (fun block => E8M0.ofNatBits (if block.val = 1 then 127 else 254), ())
      elements := fun position => if position.1.val = 2 then 192 else 64 }
  let largeRight : Block.Tensor (format threeBlocks .int8) :=
    { scales := (fun block => E8M0.ofNatBits (if block.val = 1 then 127 else 254), ())
      elements := fun _ => 64 }
  let lanes := List.finRange 32
  let input : Fin 32 → SignedRat := fun _ => SignedRat.ofRat 1
  let converted := (format oneBlock .e2m1).quantize (policy oneBlock .e2m1) input
  countFailures
    [ decide ((left.decode 0).finite?.map SignedRat.value = some 2)
    , decide ((negativeZeros.decode 0).finite? = some SignedRat.negZero)
    , decide ((constantBlock .e2m1 255 0).decode 0 = .exceptional .nan)
    , decide (converted.scales.1 () = E8M0.ofNatBits 125)
    , (converted.elements 0).toNat == 6
    , decide ((converted.decode 0).finite?.map SignedRat.value = some 1)
    , decide (converted.value 0 = 1)
    , (OCP.MX.Dot .binary32 left right lanes).toNatBits == 0x42000000
    , (OCP.MX.Dot .binary32 alternatingLeft alternatingRight lanes).toNatBits == 0xc2400000
    , (OCP.MX.Dot .binary32 largeLeft largeRight threeBlockOrder).toNatBits == 0x42000000
    , (OCP.MX.DotGeneral .binary32 largeLeft largeRight
        ((List.finRange 3).map fun block =>
          (List.finRange 32).map fun lane => (block, lane))).toNatBits == 0x42000000
    , (OCP.MX.Dot .binary32 ones nanBlock lanes).isNaN
    , (OCP.MX.Dot .binary32 ones ones []).toNatBits == 0 ]⟩

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
