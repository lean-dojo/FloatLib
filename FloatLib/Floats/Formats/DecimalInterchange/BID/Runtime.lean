/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Codec.Runtime

/-!
# Binary integer decimal encoding

IEEE 754-2019 §3.5.2(c)(2) stores the decimal coefficient as a binary integer.
The `11` steering bits move the exponent field and imply coefficient prefix
`100`. A finite coefficient exceeding `10^precision - 1` denotes zero,
preserving its sign and quantum exponent. Excessive NaN payloads also denote zero.
The decoder implements these rules rather than reducing the coefficient modulo
a decimal power.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.BID

/-- Encode a finite coefficient and biased exponent using the BID steering bits. -/
def encodeFinite (f : Format) (c e : Nat) : Nat :=
  if c < 8 * f.trailingBase then
    e * (8 * f.trailingBase) + c
  else
    24 * (f.exponentBase * f.trailingBase) +
      e * (2 * f.trailingBase) + (c - 8 * f.trailingBase)

/-- Read the BID coefficient before checking its decimal precision bound. -/
def rawCoefficient (f : Format) (n : Nat) : Nat :=
  if n < 24 * (f.exponentBase * f.trailingBase) then
    n % (8 * f.trailingBase)
  else
    8 * f.trailingBase +
      (n - 24 * (f.exponentBase * f.trailingBase)) % (2 * f.trailingBase)

/-- Read the biased exponent; subtracting the steering prefix exposes its field. -/
def biasedExponent (f : Format) (n : Nat) : Nat :=
  if n < 24 * (f.exponentBase * f.trailingBase) then
    n / (8 * f.trailingBase)
  else
    (n - 24 * (f.exponentBase * f.trailingBase)) / (2 * f.trailingBase)

/-- Decode finite fields. Oversized binary coefficients denote decimal zero. -/
def decodeFinite (f : Format) (n : Nat) : Nat × Nat :=
  let c := rawCoefficient f n
  (if c < f.coefficientBound then c else 0, biasedExponent f n)

/-- A NaN payload outside the decimal payload range denotes zero (§3.5.2(a), (c)(2)). -/
def decodePayload (f : Format) (n : Nat) : Nat :=
  if n < f.payloadBound then n else 0

/-- The complete BID interchange codec. Its laws are proved in `BID.Proof`. -/
def codec : Codec where
  encodeFinite := encodeFinite
  decodeFinite := decodeFinite
  encodePayload := fun _ p => p
  decodePayload := decodePayload

/-- Decode a BID word at the selected interchange layout. -/
def decode (f : Format) (word : BitVec f.bitWidth) : Datum := codec.decode f word

/-- Encode a representable datum as BID, returning `none` instead of rounding
when the selected width cannot represent it. -/
def encode? (f : Format) (d : Datum) : Option (BitVec f.bitWidth) := codec.encode? f d

/-- Canonical BID encoding of the datum denoted by a word. -/
def canonicalize (f : Format) (word : BitVec f.bitWidth) : BitVec f.bitWidth :=
  codec.canonicalize f word

end FloatLib.Floats.Formats.DecimalInterchange.BID
