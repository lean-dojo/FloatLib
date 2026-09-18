/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.E8M0.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
public import FloatLib.Numerics.Core.Representation
public import FloatLib.Numerics.Exact.SignedRat
public import Init.Data.Vector.OfFn

/-!
# Concrete OCP MX block representations

`Profile` lists the six concrete element encodings in Table 1 of the OCP *Microscaling Formats
(MX) Specification*, version 1.0, September 2023. `Block` stores exactly 32 elements and an E8M0
scale. The existing arbitrary-length `MX.BlockCode` remains a separate raw interchange API.

INT8 uses two's complement with six fractional bits (§5.3.4). This profile uses the permitted
asymmetric range, including code `0x80`, which denotes `-2`. It does not reinterpret the bytes
as sign-magnitude integers. Physical placement of the scale and element words is unspecified
by the standard and by this structure.

Decoding follows §5.1: a NaN scale poisons every lane; otherwise element infinities and NaNs
survive unchanged. For finite products beyond binary32's range, this implementation retains
the exact rational product, one of the implementation choices left open by that section.

Reference:
<https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

/-- The six concrete element encodings specified by OCP MX 1.0, Table 1. -/
inductive Profile where
  | e5m2 | e4m3 | e3m2 | e2m3 | e2m1 | int8
  deriving DecidableEq, Repr

namespace Profile

/-- Number of stored bits per element. -/
def width : Profile → Nat
  | .e5m2 | .e4m3 | .int8 => 8
  | .e3m2 | .e2m3 => 6
  | .e2m1 => 4

/-- Binary descriptor for floating elements; INT8 is a fixed-point two's-complement encoding. -/
def floatFormat? : Profile → Option FloatFormat
  | .e5m2 => some .e5m2
  | .e4m3 => some .e4m3fn
  | .e3m2 => some .e3m2
  | .e2m3 => some .e2m3
  | .e2m1 => some .e2m1
  | .int8 => none

/-- Exponent of the largest positive power of two representable by an element (§6.3). -/
def maxPowerExponent : Profile → Int
  | .e5m2 => 15
  | .e4m3 => 8
  | .e3m2 => 4
  | .e2m3 | .e2m1 => 2
  | .int8 => 0

end Profile

/-- A complete element word, whose width is enforced by its profile. -/
abbrev Element (profile : Profile) := BitVec profile.width

namespace Element

/-- Decode a binary floating element, retaining signed zero, infinity, and canonical NaN. -/
def decodeFloat {fmt : FloatFormat} (word : Model fmt) : NumericalValue SignedRat :=
  match Model.toDyadic? word with
  | some value => .finite (SignedRat.ofDyadic value)
  | none =>
      if Model.isInf word then .infinity (Model.signBit word) else .exceptional .nan

/-- Exact scalar observation before applying the block scale. -/
def decode {profile : Profile} (word : Element profile) : NumericalValue SignedRat :=
  match profile with
  | .e5m2 => decodeFloat (Model.ofNatBits (fmt := .e5m2) word.toNat)
  | .e4m3 => decodeFloat (Model.ofNatBits (fmt := .e4m3fn) word.toNat)
  | .e3m2 => decodeFloat (Model.ofNatBits (fmt := .e3m2) word.toNat)
  | .e2m3 => decodeFloat (Model.ofNatBits (fmt := .e2m3) word.toNat)
  | .e2m1 => decodeFloat (Model.ofNatBits (fmt := .e2m1) word.toNat)
  | .int8 => .finite (SignedRat.ofRat ((word.toInt : Rat) / 64))

/-- Finite rational interpretation, forgetting only the sign of zero. -/
def toRat? {profile : Profile} (word : Element profile) : Option Rat :=
  (decode word).finite? |>.map SignedRat.value

/-- The stored sign bit, including the sign of floating zero. -/
def negative {profile : Profile} (word : Element profile) : Bool :=
  word.toNat.testBit (profile.width - 1)

end Element

/-- OCP MX 1.0 concrete blocks have one scale and exactly 32 elements of one profile. -/
structure Block (profile : Profile) where
  /-- Shared eight-bit E8M0 scale; every byte, including NaN, is an admissible encoding. -/
  scale : E8M0
  /-- Element count and storage width are part of the type. -/
  values : Vector (Element profile) 32
  deriving DecidableEq, Repr

/-- Exact multiplication by a positive binary scale, preserving a finite zero's sign. -/
def scaleFinite (exponent : Int) (value : SignedRat) : SignedRat :=
  value * SignedRat.ofRat ((2 : Rat) ^ exponent)

namespace Block

/-- Accept an array exactly when it has the standard lane count. -/
def ofArray? {profile : Profile} (scale : E8M0) (values : Array (Element profile)) :
    Option (Block profile) :=
  if h : values.size = 32 then some ⟨scale, ⟨values, h⟩⟩ else none

/-- Decode one lane according to the shared-scale and per-element rules of §5.1. -/
def decodeLane {profile : Profile} (block : Block profile) (lane : Fin 32) :
    NumericalValue SignedRat :=
  match block.scale.exponent? with
  | none => .exceptional .nan
  | some exponent => (Element.decode block.values[lane.val]).map (scaleFinite exponent)

/-- Complete lane-wise observation; exceptional elements do not erase their finite neighbors. -/
def decode {profile : Profile} (block : Block profile) :
    Vector (NumericalValue SignedRat) 32 :=
  Vector.ofFn (decodeLane block)

/--
Whole-block finite observation for generic conversion. A block with any non-finite lane is
reported as NaN here; `decode` retains each lane's individual classification and sign.
-/
def decodeFinite {profile : Profile} (block : Block profile) :
    NumericalValue (Vector SignedRat 32) :=
  match block.decode.mapM NumericalValue.finite? with
  | some values => .finite values
  | none => .exceptional .nan

/-- Canonical block NaN. Element bits are immaterial when the shared scale is NaN. -/
def nan (profile : Profile) : Block profile :=
  ⟨E8M0.ofNatBits 255, Vector.replicate 32 0⟩

end Block

end FloatLib.Floats.Formats.OCP.MX.Standard
