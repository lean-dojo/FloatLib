/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.BID.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.DPD.Runtime

/-!
# Decimal interchange public runtime

An interchange word doesn't record whether it holds BID or DPD, so you pick both a `Format`, such
as `decimal32`, `decimal64`, or `decimal128`, and an encoding. `Encoding.encode?` keeps the datum
as it is or rejects it, and `Encoding.decode` accepts every word.

`transcode` is the same-width encoding conversion of IEEE 754-2019 §5.5.2. It keeps the sign, the
quantum exponent, and the NaN metadata, and it never does arithmetic or rounds. Converting to the
other encoding canonicalizes redundant words, while converting to the same encoding copies the word
bit for bit.

The codec and cohort proofs are in `DecimalInterchange.Basic`. For executable decimal arithmetic
with preferred-exponent selection, rounding modes, and exception flags, import
`Arithmetic.Operations`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- The two alternative decimal encodings specified by IEEE 754-2019 §3.5.2. -/
inductive Encoding where
  | bid
  | dpd
  deriving DecidableEq, Repr

namespace Encoding

/-- The coefficient codec of an encoding, which the interchange word itself doesn't record. -/
def codec : Encoding → Codec
  | .bid => BID.codec
  | .dpd => DPD.codec

/-- Decode any word, including its sign, quantum exponent, and special-value metadata. -/
def decode (encoding : Encoding) (f : Format) (word : BitVec f.bitWidth) : Datum :=
  encoding.codec.decode f word

/-- Encode the complete datum without loss, or reject it if it is invalid for the chosen format. -/
def encode? (encoding : Encoding) (f : Format) (datum : Datum) :
    Option (BitVec f.bitWidth) :=
  encoding.codec.encode? f datum

/-- Canonical representative of the datum denoted by a word. -/
def canonicalize (encoding : Encoding) (f : Format) (word : BitVec f.bitWidth) :
    BitVec f.bitWidth :=
  encoding.codec.canonicalize f word

end Encoding

/-- Convert between BID and DPD at the same width, preserving the complete datum.
Equal source and target encodings copy the word, following IEEE 754-2019 §5.5.2. -/
def transcode (source target : Encoding) (f : Format) (word : BitVec f.bitWidth) :
    BitVec f.bitWidth :=
  if source = target then word else target.codec.encode f (source.decode f word)

end FloatLib.Floats.Formats.DecimalInterchange
