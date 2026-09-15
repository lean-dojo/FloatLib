/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Core
public import FloatLib.Numerics.Exact.RationalBinary
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Prod.Lex

/-!
# Exact destination quantization for concrete OCP MX blocks

The default conversion implements the recommended algorithm of OCP MX 1.0 §6.3: select the
largest input binade, subtract the element's largest power-of-two exponent, and quantize each
scaled input with nearest-even rounding and saturation. The all-zero block uses scale `2^0`.
An exponent below `-127` is clamped to `-127`; one above `127` produces a NaN block.
Non-finite input lanes also produce a NaN block. These choices resolve cases for which §6.3
does not prescribe a scale. They are distinct from decoding existing non-finite element words.

Nearest rounding is relative to the selected scale, not to all possible block encodings.
For example, a constant E4M3 block with value `15/8` selects scale `2^-8` and saturates to `7/4`,
even though the input is representable using another scale.

Element rounding searches at most 256 words with exact rational comparisons. This bounded
reference kernel covers floating and two's-complement elements through the same numerical
contract. Its cost depends on the size of the exact input rationals, not on an unbounded shift
derived from an exponent field. Signed floating zeros are retained.

FP8's required SAT and OVF element-conversion modes (§5.3.1, Table 3) are explicit. The block
default is SAT as recommended in §6.3. FP4, FP6, and INT8 always saturate. Their scalar NaN
conversion maps to zero; block conversion instead records a NaN scale.

Reference: OCP, *Microscaling Formats (MX) Specification*, version 1.0, September 2023,
§§5.3 and 6.3,
<https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard

open FloatLib.Numerics

/-- FP8 element overflow choice. Other concrete element encodings use finite saturation. -/
inductive OverflowMode where
  | saturate | overflow
  deriving DecidableEq, Repr

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
Finite nearest-even conversion minimizes absolute error; ties favor an even low bit and then
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

/-- Canonical scalar NaN when supported; zero for the finite-only scalar encodings. -/
def nan (profile : Profile) : Element profile :=
  BitVec.ofNat profile.width <|
    match profile with
    | .e5m2 | .e4m3 => 127
    | _ => 0

/-- Scalar FP8 OVF result, or the finite endpoint for a finite-only element encoding. -/
def overflow (profile : Profile) (negative : Bool) : Element profile :=
  match profile with
  | .e5m2 => BitVec.ofNat 8 (124 + if negative then 128 else 0)
  | .e4m3 => nan .e4m3
  | other => endpoint other negative

/--
FP8 overflow after nearest-even rounding.
The E4M3 midpoint 464 rounds to the even finite 448; the E5M2 midpoint 61440 rounds to overflow.
-/
def roundsOut (profile : Profile) (input : Rat) : Bool :=
  match profile with
  | .e4m3 => 464 < |input|
  | .e5m2 => 61440 ≤ |input|
  | _ => false

/-- Convert a scalar observation to an element, before applying any shared block scale. -/
def quantize (profile : Profile) (mode : OverflowMode) :
    NumericalValue SignedRat → Element profile
  | .finite input =>
      if mode = .overflow && roundsOut profile input.value then
        overflow profile input.negative
      else quantizeFinite profile input
  | .infinity negative =>
      if mode = .overflow then overflow profile negative else endpoint profile negative
  | .exceptional _ => nan profile

/-- Numerical element contract with an explicit FP8 after-rounding overflow alternative. -/
def QuantizesWith {profile : Profile} (mode : OverflowMode) (input : SignedRat)
    (word : Element profile) : Prop :=
  if mode = .overflow ∧ roundsOut profile input.value = true then
    word = overflow profile input.negative
  else Quantizes input word

end Element

/-- Largest absolute finite input, computed before any element rounding. -/
def maxMagnitude (input : Vector SignedRat 32) : Rat :=
  input.toList.foldl (fun largest value => max largest |value.value|) 0

/-- Recommended shared exponent before handling the finite E8M0 range. -/
def requestedExponent (profile : Profile) (input : Vector SignedRat 32) : Int :=
  let largest := maxMagnitude input
  if largest = 0 then 0
  else RationalBinary.floorLog2 largest.num.natAbs largest.den - profile.maxPowerExponent

/--
Recommended max-binade scale, with explicit zero, underflow, and overflow policies.
Only finite E8M0 exponents reach rational scaling in the element kernel.
-/
def selectScale (profile : Profile) (input : Vector SignedRat 32) : E8M0 :=
  let exponent := requestedExponent profile input
  if 127 < exponent then E8M0.ofNatBits 255 else E8M0.ofExponentSaturating exponent

/-- Quantize an already finite vector at an explicit scale, or produce a canonical NaN block. -/
def quantizeAt (profile : Profile) (mode : OverflowMode) (scale : E8M0)
    (input : Vector SignedRat 32) : Block profile :=
  match scale.exponent? with
  | none => Block.nan profile
  | some exponent =>
      ⟨scale, input.map fun value =>
        Element.quantize profile mode (.finite (scaleFinite (-exponent) value))⟩

/-- Recommended scale selection followed by one rounding of each exact scaled lane. -/
def quantizeFinite (profile : Profile) (mode : OverflowMode)
    (input : Vector SignedRat 32) : Block profile :=
  quantizeAt profile mode (selectScale profile input) input

/--
Destination contract: use the chosen shared scale and round each normalized lane
according to the numerical element contract, or propagate an unrepresentable scale as NaN.
-/
def Quantizes (profile : Profile) (mode : OverflowMode) (input : Vector SignedRat 32)
    (block : Block profile) : Prop :=
  match (selectScale profile input).exponent? with
  | none => block = Block.nan profile
  | some exponent =>
    block.scale = selectScale profile input ∧
      ∀ lane : Fin 32, Element.QuantizesWith mode
        (scaleFinite (-exponent) input[lane.val]) block.values[lane.val]

/--
Convert a vector of scalar observations. Any non-finite lane produces a NaN shared scale.
Finite neighbors are preserved when decoding a stored block, but not during this scale selection.
-/
def quantize (profile : Profile) (mode : OverflowMode)
    (input : Vector (NumericalValue SignedRat) 32) : Block profile :=
  if input.toList.all NumericalValue.isFinite then
    quantizeFinite profile mode (input.map fun value => value.finite?.getD 0)
  else Block.nan profile

end FloatLib.Floats.Formats.OCP.MX.Standard
