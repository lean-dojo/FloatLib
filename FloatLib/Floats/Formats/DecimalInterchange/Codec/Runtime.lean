/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Datum

/-!
# Decimal word assembly and special values

IEEE 754-2019 §3.5.2 reserves combination fields `11110` for infinity and
`11111` for NaN in both encodings. The next bit is **one for a signaling NaN**.
Canonical encodings clear unused bits. A decoder accepts every word, retaining
the sign and the NaN's signaling bit and decimal payload.

`Codec` separates these shared rules from BID/DPD coefficient encoding.
`encode?` rejects unrepresentable datums; it does not round them.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

namespace Bits

/-- Assemble a sign and the remaining bits into an exact-width interchange word. -/
def pack (f : Format) (negative : Bool) (payload : Nat) : BitVec f.bitWidth :=
  BitVec.ofNat f.bitWidth ((if negative then f.signBase else 0) + payload)

/-- Read the sign bit. -/
def negative (f : Format) (word : BitVec f.bitWidth) : Bool :=
  word.toNat / f.signBase != 0

/-- Read all bits below the sign. -/
def payload (f : Format) (word : BitVec f.bitWidth) : Nat :=
  word.toNat % f.signBase

end Bits

/-- Executable coefficient encodings, separated from their laws in `Codec.Proof`.
Finite decoding returns `(coefficient, biasedExponent)`. -/
structure Codec where
  /-- Pack a finite coefficient and biased exponent into the unsigned payload. -/
  encodeFinite : Format → Nat → Nat → Nat
  /-- Recover a finite coefficient and biased exponent from the unsigned payload. -/
  decodeFinite : Format → Nat → Nat × Nat
  /-- Encode the diagnostic payload of a NaN. -/
  encodePayload : Format → Nat → Nat
  /-- Decode the diagnostic payload of a NaN. -/
  decodePayload : Format → Nat → Nat

namespace Codec

/-- Assemble a datum without rounding. Correct round trips require `Datum.Valid`;
use `encode?` when representability has not already been established. -/
def encode (codec : Codec) (f : Format) : Datum → BitVec f.bitWidth
  | .finite s c q => Bits.pack f s (codec.encodeFinite f c (q + f.bias).toNat)
  | .infinity s => Bits.pack f s (30 * (f.exponentBase * f.trailingBase))
  | .nan s signaling p =>
      Bits.pack f s (31 * (f.exponentBase * f.trailingBase) +
        (if signaling then f.exponentBase * f.trailingBase / 2 else 0) +
        codec.encodePayload f p)

/-- Checked interchange encoding. `none` means that this width cannot represent
the supplied datum exactly, including its quantum exponent or NaN payload. -/
def encode? (codec : Codec) (f : Format) (d : Datum) : Option (BitVec f.bitWidth) :=
  if d.Valid f then some (codec.encode f d) else none

/-- Decode every interchange word, accepting the noncanonical encodings specified
by IEEE 754-2019 §3.5.2. -/
def decode (codec : Codec) (f : Format) (word : BitVec f.bitWidth) : Datum :=
  let s := Bits.negative f word
  let n := Bits.payload f word
  let combination := n / (f.exponentBase * f.trailingBase)
  if combination < 30 then
    let (c, e) := codec.decodeFinite f n
    Datum.ofBiased f s c e
  else if combination = 30 then
    .infinity s
  else
    .nan s (n / (f.exponentBase * f.trailingBase / 2) % 2 == 1)
      (codec.decodePayload f (n % f.trailingBase))

/-- Re-encode a decoded datum, clearing unused special-value bits and replacing
redundant significand encodings by their canonical representatives. -/
def canonicalize (codec : Codec) (f : Format) (word : BitVec f.bitWidth) :
    BitVec f.bitWidth :=
  codec.encode f (codec.decode f word)

end Codec

end FloatLib.Floats.Formats.DecimalInterchange
