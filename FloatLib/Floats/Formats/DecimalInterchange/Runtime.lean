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

Choose a `Format`, such as `decimal32`, `decimal64`, or `decimal128`, and explicitly
select BID or DPD: a word does not identify its own encoding. `Encoding.encode?` preserves
the exact datum or rejects it; `Encoding.decode` accepts every word.

`transcode` implements the same-width encoding conversion of IEEE 754-2019 §5.5.2,
preserving the sign, quantum exponent, and NaN metadata. Conversion between different
encodings canonicalizes redundant words; conversion to the same encoding copies the
word. Neither performs arithmetic or rounding.

Import `DecimalInterchange.Basic` for the codec and cohort proofs.
`Arithmetic.Operations` provides executable decimal arithmetic, preferred-exponent
selection, rounding modes, and exception flags.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- The two alternative decimal encodings specified by IEEE 754-2019 §3.5.2. -/
inductive Encoding where
  | bid
  | dpd
  deriving DecidableEq, Repr

namespace Encoding

/-- Coefficient codec selected externally to the interchange word. -/
def codec : Encoding → Codec
  | .bid => BID.codec
  | .dpd => DPD.codec

/-- Decode any word, including its sign, quantum exponent, and special-value metadata. -/
def decode (encoding : Encoding) (f : Format) (word : BitVec f.bitWidth) : Datum :=
  encoding.codec.decode f word

/-- Encode the complete datum exactly, or reject it if it is invalid for the chosen format. -/
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
