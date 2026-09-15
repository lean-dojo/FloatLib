/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Runtime
public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.ExecFloat.Conversion.Core

/-!
# Configured standard OCP MX destinations

`ExecFloat.OCP.MX.Standard profile` is a constrained 32-lane destination on the common carrier.
It is separate from the existing arbitrary-length raw block family. Conversion selects the
recommended max-binade scale; explicit element SAT/OVF policy is the conversion context.

The generic exact domain is a vector of signed rationals. A stored block containing non-finite
lanes has no value in that domain and is summarized as NaN. The lane-wise `decode` accessor
retains all individual NaNs, infinities, and finite neighbors.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.OCP.MX

namespace Standard

open Formats.OCP.MX.Standard

/-- Identity of a standard MX block with one of the six concrete element profiles. -/
inductive Family (profile : Profile) where
  | format

instance (profile : Profile) : EncodedFormat (Family profile) where
  Code := Block profile
  Scalar := Vector SignedRat 32

instance (profile : Profile) : FormatSemantics (Family profile) where
  denote := Block.decodeFinite

end Standard

/-- One E8M0 scale and exactly 32 elements of a concrete OCP MX 1.0 profile. -/
abbrev Standard (profile : Formats.OCP.MX.Standard.Profile) :=
  FloatLib.Floats.ExecFloat (Standard.Family profile)

namespace Standard

open Formats.OCP.MX.Standard

variable {profile : Profile}

/-- Wrap a complete valid standard block without numerical conversion. -/
@[inline] def ofCode (block : Block profile) : Standard profile :=
  ExecFloat.ofRaw block

/-- Recover the complete scale and fixed-length element storage. -/
@[inline] def toCode (value : Standard profile) : Block profile :=
  value.raw

/-- Exact lane-wise observation, retaining element-local non-finite values. -/
@[inline] def decode (value : Standard profile) : Vector (NumericalValue SignedRat) 32 :=
  value.toCode.decode

/-- Direct quantization of finite exact inputs under the chosen FP8 overflow mode. -/
@[inline] def quantize (mode : OverflowMode) (input : Vector SignedRat 32) :
    Standard profile :=
  ofCode (Formats.OCP.MX.Standard.quantizeFinite profile mode input)

namespace Conversion

/--
Whether a normalized lane lies outside its signed finite endpoint. For these block conversions,
range flags use the exact endpoint test, not the binary scalar after-rounding convention.
-/
def outsideFinite (value : SignedRat) : Bool :=
  match Element.toRat? (Element.endpoint profile value.negative) with
  | none => true
  | some endpoint => |endpoint| < |value.value|

/--
Conversion flags. `overflow` includes an unrepresentable shared scale or a normalized lane
outside its exact finite range; `saturated` records such a lane stored at its finite endpoint.
`underflow` records a nonzero input lane becoming zero. `inexact` compares complete signed
finite observations, including zero signs.
-/
def status (input : Vector SignedRat 32) (rounded : Standard profile) :
    ExecFloat.ConversionStatus :=
  let block := rounded.toCode
  let inexact := decide (block.decode ≠ input.map NumericalValue.finite)
  match block.scale.exponent? with
  | none => { inexact, overflow := true }
  | some exponent =>
    let normalized := input.map (scaleFinite (-exponent))
    let outside := normalized.map (outsideFinite (profile := profile))
    { inexact
      overflow := outside.toList.any id
      saturated := (List.finRange 32).any fun lane =>
        outside[lane.val] &&
          decide (block.values[lane.val] = Element.endpoint profile normalized[lane.val].negative)
      underflow := (List.finRange 32).any fun lane =>
        decide (input[lane.val].value ≠ 0) &&
          decide (Element.toRat? block.values[lane.val] = some 0) }

/-- Convert one exact block observation, recording exceptional sources with a NaN scale. -/
def run (mode : OverflowMode) :
    NumericalValue (Vector SignedRat 32) → ExecFloat.ConversionOutcome (Standard profile)
  | .finite input =>
    let rounded := quantize mode input
    .success rounded (status input rounded)
  | .infinity _ | .exceptional _ =>
    .success (ofCode (Block.nan profile)) { mappedSpecial := true }

/-- Destination specification uses the numerical lane-rounding relation at the selected scale. -/
def spec (mode : OverflowMode) (input : NumericalValue (Vector SignedRat 32))
    (outcome : ExecFloat.ConversionOutcome (Standard profile)) : Prop :=
  match input with
  | .finite exact =>
    ∃ rounded, outcome = .success rounded (status exact rounded) ∧
      Formats.OCP.MX.Standard.Quantizes profile mode exact rounded.toCode
  | .infinity _ | .exceptional _ =>
    outcome = .success (ofCode (Block.nan profile)) { mappedSpecial := true }

/-- Finite block conversion exposes exact signed rationals through the shared source capability. -/
instance exactDecoder : ExecFloat.ExactDecoder (Standard profile) (Vector SignedRat 32) where
  decode value := value.toCode.decodeFinite

end Conversion
end Standard
end ExecFloat.OCP.MX
end FloatLib.Floats
