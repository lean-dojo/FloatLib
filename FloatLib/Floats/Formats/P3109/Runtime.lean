/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Configured.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Basic

/-!
# P3109 formats

P3109 descriptors have four parameters from the interim report: bit width, precision,
signedness, and finite or extended domain. Every valid descriptor produces an exact-width
codebook and an `ExecFloat` carrier.

This module covers representation and exact decoding. The arithmetic and projection modules
supply operations and rounding policies.

The finite magnitude formula agrees with ordinary binary scientific notation after fields have
been extracted. Classification does not: P3109 unsigned formats omit the sign bit, while signed
formats use the midpoint code for their single NaN and mirror finite magnitudes across the upper
half of the code space. P3109 also admits field widths excluded by
`BinaryInterchange.FloatFormat`, so it needs its own field classification.

## Reference

* IEEE Working Group P3109, *Interim Report on Arithmetic Formats for Machine Learning*,
  version 4.0.3 (1 September 2026), Sections 3.1 and 4.7.2, repository revision `34f5964`,
  <https://github.com/P3109/Public/tree/34f5964d9bb2382b2665d15467fc3517b990b308>.
  `tests/oracles/format-standards.sh` compares decoding with the published value tables.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109

/-- Whether a P3109 format represents negative finite values. -/
inductive Signedness where
  | signed
  | unsigned
  deriving DecidableEq, Repr

/-- Whether a P3109 format represents infinities as well as finite values and NaN. -/
inductive Domain where
  | finite
  | extended
  deriving DecidableEq, Repr

/--
A validated descriptor for the complete four-parameter P3109 format family.

One value of this structure selects a profile; there is no separate Lean type or decoder for each
bit width. The proof fields rule out precisely the invalid `(K, P, signedness)` combinations from
the report before any value can be constructed.
-/
structure Format where
  /-- Total number of encoded bits (`K` in the report). -/
  bitWidth : Nat
  /-- Significand precision including the implicit leading bit (`P` in the report). -/
  precision : Nat
  /-- Signed or unsigned datum set. -/
  signedness : Signedness
  /-- Finite or extended datum set. -/
  domain : Domain
  /-- P3109 requires more than two encoded bits. -/
  bitWidth_gt_two : 2 < bitWidth
  /-- P3109 requires positive precision. -/
  precision_pos : 0 < precision
  /-- Signed formats require `P < K`; unsigned formats allow `P = K`. -/
  precision_bound :
    match signedness with
    | .signed => precision < bitWidth
    | .unsigned => precision ≤ bitWidth
  deriving Repr

namespace Format

/-- Number of explicitly stored trailing significand bits. -/
@[inline] def trailingBits (format : Format) : Nat :=
  format.precision - 1

/--
Width of the biased exponent field.

Unsigned formats gain the bit that a signed format uses to divide positive and negative codes.
-/
@[inline] def exponentBits (format : Format) : Nat :=
  match format.signedness with
  | .signed => format.bitWidth - format.precision
  | .unsigned => format.bitWidth - format.precision + 1

/-- P3109 exponent bias, derived from the exponent-field width. -/
@[inline] def exponentBias (format : Format) : Nat :=
  2 ^ (format.exponentBits - 1)

/-- Smallest leading exponent used by a normal finite value. -/
@[inline] def minimumNormalExponent (format : Format) : Int :=
  1 - Int.ofNat format.exponentBias

/-- Quantum exponent of the smallest positive finite value. -/
@[inline] def minimumQuantumExponent (format : Format) : Int :=
  2 - Int.ofNat format.precision - Int.ofNat format.exponentBias

/-- Number of code points in the format. -/
@[inline] def modulus (format : Format) : Nat :=
  2 ^ format.bitWidth

/-- First code in the negative half of a signed format. -/
@[inline] def signBoundary (format : Format) : Nat :=
  2 ^ (format.bitWidth - 1)

/-- Code point assigned to the format's single NaN. -/
@[inline] def nanBits (format : Format) : Nat :=
  match format.signedness with
  | .signed => format.signBoundary
  | .unsigned => format.modulus - 1

/-- Code point assigned to positive infinity when the domain is extended. -/
@[inline] def positiveInfinityBits (format : Format) : Nat :=
  match format.signedness with
  | .signed => format.signBoundary - 1
  | .unsigned => format.modulus - 2

/-- Code point assigned to negative infinity in a signed extended format. -/
@[inline] def negativeInfinityBits (format : Format) : Nat :=
  format.modulus - 1

/-- Construct a signed P3109 descriptor. -/
@[inline] def signed
    (bitWidth precision : Nat)
    (domain : Domain)
    (bitWidth_gt_two : 2 < bitWidth := by decide)
    (precision_pos : 0 < precision := by decide)
    (precision_lt_bitWidth : precision < bitWidth := by decide) :
    Format where
  bitWidth := bitWidth
  precision := precision
  signedness := .signed
  domain := domain
  bitWidth_gt_two := bitWidth_gt_two
  precision_pos := precision_pos
  precision_bound := precision_lt_bitWidth

/-- Construct an unsigned P3109 descriptor. -/
@[inline] def unsigned
    (bitWidth precision : Nat)
    (domain : Domain)
    (bitWidth_gt_two : 2 < bitWidth := by decide)
    (precision_pos : 0 < precision := by decide)
    (precision_le_bitWidth : precision ≤ bitWidth := by decide) :
    Format where
  bitWidth := bitWidth
  precision := precision
  signedness := .unsigned
  domain := domain
  bitWidth_gt_two := bitWidth_gt_two
  precision_pos := precision_pos
  precision_bound := precision_le_bitWidth

/--
Validate parameters supplied at runtime and construct the corresponding P3109 descriptor.

Use `signed` or `unsigned` when the parameters are fixed in Lean code and their constraints can
be discharged at elaboration time. This checked constructor is for parsers, generated format
matrices, and other callers whose parameters are ordinary runtime values.
-/
@[inline] def ofParameters?
    (bitWidth precision : Nat)
    (signedness : Signedness)
    (domain : Domain) :
    Option Format :=
  if hwidth : 2 < bitWidth then
    if hprecision : 0 < precision then
      match signedness with
      | .signed =>
          if hbound : precision < bitWidth then
            some (signed bitWidth precision domain hwidth hprecision hbound)
          else
            none
      | .unsigned =>
          if hbound : precision ≤ bitWidth then
            some (unsigned bitWidth precision domain hwidth hprecision hbound)
          else
            none
    else
      none
  else
    none

/--
Exact positive finite value decoded from one in-range magnitude.

Informally, row zero is subnormal and uses the stored trailing bits directly. Every other row
prepends the implicit leading bit and subtracts the descriptor's exponent bias. Exceptional-code
classification and negative mirroring happen in `decodeNat`, outside this shared mathematical
formula.
-/
@[inline] def decodePositiveFinite (format : Format) (bits : Nat) : Numerics.Dyadic :=
  if bits = 0 then
    .zero
  else
    let trailingUnit := 2 ^ format.trailingBits
    let trailing := bits % trailingUnit
    let biasedExponent := bits / trailingUnit
    if biasedExponent = 0 then
      {
        negative := false
        significand := trailing
        exponent := format.minimumQuantumExponent
      }
    else
      {
        negative := false
        significand := trailingUnit + trailing
        exponent :=
          Int.ofNat biasedExponent - Int.ofNat format.exponentBias +
            1 - Int.ofNat format.precision
      }

/--
Decode an in-range natural-number code point according to P3109 Section 4.7.2.

Callers with arbitrary natural numbers should first construct a `BitVec format.bitWidth`; the
public `decode` and `ExecFloat.P3109.ofNatBits` functions do this automatically.
-/
@[inline] def decodeNat (format : Format) (bits : Nat) :
    NumericalValue Numerics.Dyadic :=
  match format.signedness, format.domain with
  | .signed, .finite =>
      if bits = format.signBoundary then
        .exceptional (.nan)
      else if format.signBoundary < bits then
        .finite (format.decodePositiveFinite (bits - format.signBoundary)).neg
      else
        .finite (format.decodePositiveFinite bits)
  | .signed, .extended =>
      if bits = format.signBoundary then
        .exceptional (.nan)
      else if bits = format.positiveInfinityBits then
        .infinity false
      else if bits = format.negativeInfinityBits then
        .infinity true
      else if format.signBoundary < bits then
        .finite (format.decodePositiveFinite (bits - format.signBoundary)).neg
      else
        .finite (format.decodePositiveFinite bits)
  | .unsigned, .finite =>
      if bits = format.nanBits then
        .exceptional (.nan)
      else
        .finite (format.decodePositiveFinite bits)
  | .unsigned, .extended =>
      if bits = format.nanBits then
        .exceptional (.nan)
      else if bits = format.positiveInfinityBits then
        .infinity false
      else
        .finite (format.decodePositiveFinite bits)

/-- Exact P3109 denotation of one width-bounded code point. -/
@[inline] def decode (format : Format) (code : BitVec format.bitWidth) :
    NumericalValue Numerics.Dyadic :=
  format.decodeNat code.toNat

/-- Complete codebook induced by a P3109 descriptor. -/
def codebook (format : Format) :
    Formats.Codebook format.bitWidth Numerics.Dyadic where
  denote := format.decode

/-- P3109 as a family-independent exact numerical system. -/
def numericalSystem (format : Format) : NumericalSystem :=
  format.codebook.numericalSystem

end Format
end FloatLib.Floats.Formats.P3109

namespace FloatLib.Floats.ExecFloat

/--
Executable exact-width carrier for any valid P3109 descriptor.

Generic exact-expression operations can use this type as a destination through its conversion
capability. The representation layer does not install a separate arithmetic interface.
-/
abbrev P3109 (format : Formats.P3109.Format) :=
  ExecFloat.Codebook format.codebook

namespace P3109

variable {format : Formats.P3109.Format}

/-- Construct P3109's unique zero without exposing its stored word. -/
@[inline] def zero : ExecFloat.P3109 format :=
  ExecFloat.Codebook.ofNatBits 0

/-- Construct P3109's sole NaN without exposing its descriptor-dependent code point. -/
@[inline] def nan : ExecFloat.P3109 format :=
  ExecFloat.Codebook.ofNatBits format.nanBits

/--
Construct positive infinity when the descriptor has an extended domain.

Using this function with a statically finite-only descriptor fails during elaboration.
-/
@[inline] def positiveInfinity
    (_extended : format.domain = .extended := by decide) :
    ExecFloat.P3109 format :=
  ExecFloat.Codebook.ofNatBits format.positiveInfinityBits

/--
Construct negative infinity when the descriptor is both signed and extended.

Using this function with an unsigned or finite-only descriptor fails during elaboration.
-/
@[inline] def negativeInfinity
    (_signed : format.signedness = .signed := by decide)
    (_extended : format.domain = .extended := by decide) :
    ExecFloat.P3109 format :=
  ExecFloat.Codebook.ofNatBits format.negativeInfinityBits

/--
Construct a finite P3109 value from named representation fields.

`biasedExponent` and `trailing` are checked against the descriptor widths. The constructor also
rejects a negative request for an unsigned format and every field combination reserved for NaN or
infinity. It is the structured alternative to `ofNatBits` when an application already has decoded
P3109 fields; it does not perform numerical rounding.
-/
@[inline] def ofFiniteFields? (negative : Bool)
    (biasedExponent trailing : Nat) : Option (ExecFloat.P3109 format) :=
  if negative = true ∧ format.signedness = .unsigned then
    none
  else if biasedExponent < 2 ^ format.exponentBits ∧
      trailing < 2 ^ format.trailingBits then
    let magnitude := biasedExponent * 2 ^ format.trailingBits + trailing
    let bits := if negative then format.signBoundary + magnitude else magnitude
    let value : ExecFloat.P3109 format := ExecFloat.Codebook.ofNatBits bits
    match ExecFloat.Codebook.decode value with
    | .finite _ => some value
    | .infinity _ | .exceptional _ => none
  else
    none

/--
Construct a P3109 value from the low `K` bits of a serialized word.

Prefer the named semantic constructors or `ofFiniteFields?` in ordinary code.
-/
@[inline] def ofNatBits (bits : Nat) : ExecFloat.P3109 format :=
  ExecFloat.Codebook.ofNatBits bits

/-- Read a P3109 value as its natural-number code point. -/
@[inline] def toNatBits (value : ExecFloat.P3109 format) : Nat :=
  ExecFloat.Codebook.toNatBits value

/-- Decode a P3109 value to its exact finite, infinity, or NaN semantics. -/
@[inline] def decode (value : ExecFloat.P3109 format) :
    NumericalValue Numerics.Dyadic :=
  ExecFloat.Codebook.decode value

end P3109
end FloatLib.Floats.ExecFloat
