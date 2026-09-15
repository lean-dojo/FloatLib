/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Codec.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.DPD.Trailing

/-!
# Densely packed decimal interchange encoding

IEEE 754-2019 §3.5.2(c)(1) combines the leading decimal digit and the high exponent
bits in a five-bit combination field. The remaining digits use Cowlishaw declets.
All redundant declets decode; encoding chooses the canonical representation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.DPD

/-- Combine a leading digit with the high two exponent bits. -/
def combination (leading highExponent : Nat) : Nat :=
  if leading < 8 then 8 * highExponent + leading
  else 24 + 2 * highExponent + (leading - 8)

/-- Leading digit extracted from a finite combination field (`field < 30`). -/
def leadingDigit (field : Nat) : Nat :=
  if field < 24 then field % 8 else 8 + field % 2

/-- High exponent bits extracted from a finite combination field. -/
def highExponent (field : Nat) : Nat :=
  if field < 24 then field / 8 else (field - 24) / 2

/-- Assemble the leading digit, biased exponent, and already-packed trailing declets. -/
def encodeFields (f : Format) (leading exponent trailing : Nat) : Nat :=
  combination leading (exponent / f.exponentBase) * (f.exponentBase * f.trailingBase) +
    (exponent % f.exponentBase) * f.trailingBase + trailing

/-- Encode a finite decimal coefficient and biased exponent. -/
def encodeFinite (f : Format) (c e : Nat) : Nat :=
  encodeFields f (c / f.payloadBound) e
    (encodeTrailing f.declets (c % f.payloadBound))

/-- Decode a finite word, accepting every trailing declet. -/
def decodeFinite (f : Format) (n : Nat) : Nat × Nat :=
  let field := n / (f.exponentBase * f.trailingBase)
  (leadingDigit field * f.payloadBound + decodeTrailing f.declets (n % f.trailingBase),
    highExponent field * f.exponentBase + n / f.trailingBase % f.exponentBase)

/-- The complete DPD interchange codec. Its laws are proved in `DPD.Proof`. -/
def codec : Codec where
  encodeFinite := encodeFinite
  decodeFinite := decodeFinite
  encodePayload := fun f => encodeTrailing f.declets
  decodePayload := fun f => decodeTrailing f.declets

/-- Decode a DPD word at the selected interchange layout, including redundant declets. -/
def decode (f : Format) (word : BitVec f.bitWidth) : Datum := codec.decode f word

/-- Encode a datum exactly as DPD, rejecting unrepresentable inputs without rounding. -/
def encode? (f : Format) (d : Datum) : Option (BitVec f.bitWidth) := codec.encode? f d

/-- Replace redundant declets and unused special bits by their canonical encodings. -/
def canonicalize (f : Format) (word : BitVec f.bitWidth) : BitVec f.bitWidth :=
  codec.canonicalize f word

end FloatLib.Floats.Formats.DecimalInterchange.DPD
