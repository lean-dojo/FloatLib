/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Core
public import FloatLib.Numerics.Exact.RationalBinary
public import FloatLib.Numerics.Operation.Context
public import Mathlib.Data.List.MinMax
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Element conversion of OCP MX 1.0

Element rounding searches at most 256 words with exact rational comparisons. One bounded reference
kernel covers floating and two's-complement elements under the same numerical contract, and its
cost depends on the size of the exact input rationals. No unbounded shift derived from an exponent
field ever comes into it. Signed floating zeros are kept.

FP8's required SAT and OVF element-conversion modes (§5.3.1, Table 3) are the `(overflow := ...)`
option, `.saturate` or `.native`, of `Numerics.OverflowMode`. SAT is the default, as §6.3
recommends. FP4, FP6, and INT8 always saturate. Their scalar NaN conversion maps to zero.

The block conversion of §6.3, which selects the shared scale and rounds each scaled input with
these element conversions, is `Standard.format` with the general `Block.CodedFormat.quantize`.

Reference: OCP, *Microscaling Formats (MX) Specification*, version 1.0, September 2023,
§§5.3 and 6.3,
<https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard

open FloatLib.Numerics

namespace Element

/-- All finite element words paired with their exact rational values. -/
def candidates (profile : Profile) : List (Element profile × Rat) :=
  (List.ofFn fun bits : Fin (2 ^ profile.width) => BitVec.ofFin bits).filterMap fun word =>
    (toRat? word).map fun value => (word, value)

/--
Nearest-even ordering key: distance first, then even least-significant bit, then zero sign.
The last component only resolves duplicate numerical encodings such as the two floating zeros.
-/
def roundingKey {profile : Profile} (input : SignedRat) (candidate : Element profile × Rat) :
    Rat ×ₗ Nat :=
  toLex (|candidate.2 - input.value|,
    2 * (candidate.1.toNat % 2) + if negative candidate.1 == input.negative then 0 else 1)

/--
Finite nearest-even conversion minimizes absolute error. Ties favor an even low bit and then
the input's zero sign. This relation is independent of how candidates are enumerated.
-/
def Quantizes {profile : Profile} (input : SignedRat) (word : Element profile) : Prop :=
  ∃ value, toRat? word = some value ∧
    ∀ (other : Element profile) (otherValue : Rat), toRat? other = some otherValue →
      roundingKey input (word, value) ≤ roundingKey input (other, otherValue)

/-- Saturating nearest-even element rounding, using only exact rational comparisons. -/
def quantizeFinite (profile : Profile) (input : SignedRat) : Element profile :=
  ((candidates profile).argmin (roundingKey input)).getD (0, 0) |>.1

/-- Signed finite endpoint, including the permitted `-2` endpoint of this INT8 profile. -/
def endpoint (profile : Profile) (negative : Bool) : Element profile :=
  let magnitude :=
    match profile with
    | .e5m2 => 123
    | .e4m3 => 126
    | .e3m2 | .e2m3 => 31
    | .e2m1 => 7
    | .int8 => if negative then 128 else 127
  BitVec.ofNat profile.width
    (if profile = .int8 then magnitude
     else magnitude + if negative then 2 ^ (profile.width - 1) else 0)

/-- Canonical scalar NaN when the element has one, and zero for the finite-only encodings. -/
def nan (profile : Profile) : Element profile :=
  BitVec.ofNat profile.width <|
    match profile with
    | .e5m2 | .e4m3 => 127
    | _ => 0

/-- Scalar FP8 OVF result, or the finite endpoint for a finite-only element encoding. -/
def overflow (profile : Profile) (negative : Bool) : Element profile :=
  match profile with
  | .e5m2 => BitVec.ofNat 8 (124 + if negative then 128 else 0)
  | .e4m3 => (BinaryInterchange.Model.propagatedNaN .e4m3 negative 0).bits
  | other => endpoint other negative

/--
FP8 overflow after nearest-even rounding.
The E4M3 midpoint 464 rounds to the even finite 448, and the E5M2 midpoint 61440 overflows.
-/
def roundsOut (profile : Profile) (input : Rat) : Bool :=
  match profile with
  | .e4m3 => 464 < |input|
  | .e5m2 => 61440 ≤ |input|
  | _ => false

/-- OCP MX v1.0, §5.3: exceptional-input and overflow dispatch with a supplied finite converter. -/
def quantizeWith (profile : Profile) (finite : SignedRat → Element profile)
    (value : NumericalValue SignedRat)
    (overflow : OverflowMode := .saturate) : Element profile :=
  match value with
  | .finite input =>
      if overflow = .native && roundsOut profile input.value then
        Element.overflow profile input.negative
      else finite input
  | .infinity negative =>
      if overflow = .native then Element.overflow profile negative else endpoint profile negative
  | .exceptional _ => nan profile

/--
Convert a scalar observation to an element, before applying any shared block scale.

`overflow := .saturate` (the default) is the SAT conversion mode of OCP MX v1.0, §5.3.1,
and `.native` the OVF mode, which only FP8 elements distinguish: other profiles saturate
under both. Finite nearest-even conversion uses `quantizeFinite`.
-/
def quantize (profile : Profile) (value : NumericalValue SignedRat)
    (overflow : OverflowMode := .saturate) : Element profile :=
  quantizeWith profile (quantizeFinite profile) value overflow

/-- Numerical element contract, with the FP8 after-rounding overflow alternative. -/
def QuantizesWith {profile : Profile} (overflow : OverflowMode) (input : SignedRat)
    (word : Element profile) : Prop :=
  if overflow = .native ∧ roundsOut profile input.value = true then
    word = Element.overflow profile input.negative
  else Quantizes input word

end Element

end FloatLib.Floats.Formats.OCP.MX.Standard
