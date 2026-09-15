/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Runtime

/-!
# Runtime interface for configured posit values

Configured posit values support packing, exact decoding, classification, and raw-word conversion
independently of storage choice.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/--
Decode the statically selected runtime carrier into the exact-width posit proof model.

This boundary does not expose whether the carrier is a byte, machine word, packed pair, or wide
bit vector.
-/
@[always_inline, inline] def toModel
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    Model format :=
  Configured.Family.toModel value

/-- Pack an exact-width posit model into the statically selected runtime carrier. -/
@[always_inline, inline] def ofModel
    (value : Model format) :
    FloatLib.Floats.ExecFloat (Configured.Family format code plan) :=
  Configured.Family.ofModel value

/--
Construct a configured posit from its complete unsigned word.

Inputs outside the configured width are reduced modulo `2 ^ format.bits`, matching
`Model.ofNatBits`.
-/
@[inline] def ofNatBits (bits : Nat) :
    FloatLib.Floats.ExecFloat (Configured.Family format code plan) :=
  ofModel (Model.ofNatBits bits)

/-- Read the complete posit word as an unsigned natural number. -/
@[inline] def toNatBits
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) : Nat :=
  (toModel value).toNatBits

/-- Decode the tapered fields, retaining zero and NaR as separate constructors. -/
@[inline] def exactValue
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    Model.ExactValue format :=
  (toModel value).decodeExact

/-- Complete rational denotation; NaR remains an exceptional Not-a-Real observation. -/
@[inline] def decode
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    FloatLib.Numerics.NumericalValue Rat :=
  Model.decode (toModel value)

/-- Exact rational value of an ordinary configured posit, or `none` exactly for NaR. -/
@[inline] def toRat?
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    Option Rat :=
  Model.toRat? (toModel value)

/-- Whether the configured value is the unique zero encoding. -/
@[inline] def isZero
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) : Bool :=
  Model.isZero (toModel value)

/-- Whether the configured value is the unique Not-a-Real encoding. -/
@[inline] def isNaR
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) : Bool :=
  Model.isNaR (toModel value)

end ExecFloat.Posit
end FloatLib.Floats
