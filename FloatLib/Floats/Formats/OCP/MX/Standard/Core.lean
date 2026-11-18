/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Core
public import FloatLib.Numerics.Core.Representation
public import FloatLib.Numerics.Exact.SignedRat

/-!
# Element formats of OCP MX 1.0

`Profile` lists the six concrete element encodings in Table 1 of the OCP *Microscaling Formats
(MX) Specification*, version 1.0, September 2023, and `Element.decode` gives the exact value of an
element word before any block scale is applied. The block format of each profile, with its E8M0
scale and its scale rule, is `Standard.format`, an instance of the general block-scaled format
`Block.CodedFormat`.

INT8 is two's complement with six fractional bits (§5.3.4), so code `0x40` is `1` and code `0x80`
is `-2`. We use the permitted asymmetric range, which includes `0x80`, and never reinterpret the
bytes as sign-magnitude integers. This is the fixed-point format S2F6.

Reference:
<https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

/-- The six concrete element encodings specified by OCP MX 1.0, Table 1. -/
inductive Profile where
  /-- MXFP8 with E5M2 elements. -/
  | e5m2
  /-- MXFP8 with E4M3 elements. -/
  | e4m3
  /-- MXFP6 with E3M2 elements. -/
  | e3m2
  /-- MXFP6 with E2M3 elements. -/
  | e2m3
  /-- MXFP4, with E2M1 elements. -/
  | e2m1
  /-- MXINT8, with two's-complement 8-bit integer elements. -/
  | int8
  deriving DecidableEq, Repr

namespace Profile

/-- Number of stored bits per element. -/
def width : Profile → Nat
  | .e5m2 | .e4m3 | .int8 => 8
  | .e3m2 | .e2m3 => 6
  | .e2m1 => 4

/-- Binary descriptor for floating elements. INT8 has none, being a fixed-point two's-complement
encoding. -/
def floatFormat? : Profile → Option FloatFormat
  | .e5m2 => some .e5m2
  | .e4m3 => some .e4m3
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
      if Model.isInfinite word then .infinity (Model.signBit word) else .exceptional .nan

/-- Exact scalar observation before applying the block scale. -/
def decode {profile : Profile} (word : Element profile) : NumericalValue SignedRat :=
  match profile with
  | .e5m2 => decodeFloat (Model.ofNatBits (fmt := .e5m2) word.toNat)
  | .e4m3 => decodeFloat (Model.ofNatBits (fmt := .e4m3) word.toNat)
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

end FloatLib.Floats.Formats.OCP.MX.Standard

namespace FloatLib.Floats.Formats.OCP.MX.Standard.Profile

/-- Reconstruct a `Profile` constructor from its constructor index. -/
add_decl_doc ofNat_ctorIdx

end FloatLib.Floats.Formats.OCP.MX.Standard.Profile
