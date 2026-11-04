/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Runtime
public import FloatLib.Floats.Formats.OCP.MX.Configured.Core

/-!
# Executable configured OCP MX operations

On the E8M0 side you get checked scale decoding and construction. An MX block gives you its joint
storage and a checked decoder, which rejects non-finite element words and, when the block is
nonempty, a NaN scale.

These wrappers take any array length and any binary element descriptor. When a block decodes, you
get the exact dyadic value of every element with the shared scale applied. An empty block decodes
to an empty array without looking at its scale.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.OCP.MX

open FloatLib.Floats.Formats.BinaryInterchange

universe u

namespace E8M0

/-- Wrap a complete E8M0 code without conversion. -/
@[inline] def ofCode (code : Formats.OCP.MX.E8M0) : ExecFloat.OCP.MX.E8M0 :=
  ExecFloat.ofRaw code

/-- Recover the complete E8M0 code without conversion. -/
@[inline] def toCode (value : ExecFloat.OCP.MX.E8M0) : Formats.OCP.MX.E8M0 :=
  value.raw

/-- Construct an E8M0 value from its complete byte pattern. -/
@[inline] def ofNatBits (bits : Nat) : ExecFloat.OCP.MX.E8M0 :=
  ofCode (Formats.OCP.MX.E8M0.ofNatBits bits)

/-- Read the complete E8M0 byte pattern. -/
@[inline] def toNatBits (value : ExecFloat.OCP.MX.E8M0) : Nat :=
  Formats.OCP.MX.E8M0.toNatBits value.toCode

/-- Whether the value is the unique E8M0 NaN code. -/
@[inline] def isNaN (value : ExecFloat.OCP.MX.E8M0) : Bool :=
  Formats.OCP.MX.E8M0.isNaN value.toCode

/-- Decode the unbiased power-of-two exponent, or `none` for NaN. -/
@[inline] def exponent? (value : ExecFloat.OCP.MX.E8M0) : Option Int :=
  Formats.OCP.MX.E8M0.exponent? value.toCode

/-- Decode the exact positive dyadic scale, or `none` for NaN. -/
@[inline] def toDyadic? (value : ExecFloat.OCP.MX.E8M0) :
    Option Numerics.Dyadic :=
  Formats.OCP.MX.E8M0.toDyadic? value.toCode

/-- Construct an E8M0 scale when the requested exponent is representable. -/
@[inline] def ofExponent? (exponent : Int) : Option ExecFloat.OCP.MX.E8M0 :=
  (Formats.OCP.MX.E8M0.ofExponent? exponent).map ofCode

/-- Construct an E8M0 scale, clamping the exponent into `[-127, 127]` first. -/
@[inline] def ofExponentSaturating (exponent : Int) : ExecFloat.OCP.MX.E8M0 :=
  ofCode (Formats.OCP.MX.E8M0.ofExponentSaturating exponent)

/-- Apply a finite E8M0 scale to an exact dyadic value. -/
@[inline] def scaleDyadic? (scale : ExecFloat.OCP.MX.E8M0)
    (value : Numerics.Dyadic) : Option Numerics.Dyadic :=
  Formats.OCP.MX.E8M0.scaleDyadic? scale.toCode value

end E8M0

namespace Block

variable {format : FloatFormat}

/-- Wrap a complete MX block code without conversion. -/
@[inline] def ofCode (code : Formats.OCP.MX.BlockCode format) :
    ExecFloat.OCP.MX.Block format :=
  ExecFloat.ofRaw code

/-- Recover the complete MX block code without conversion. -/
@[inline] def toCode (value : ExecFloat.OCP.MX.Block format) :
    Formats.OCP.MX.BlockCode format :=
  value.raw

/-- Construct a joint block from one configured E8M0 scale and its element words. -/
@[inline] def ofComponents (scale : ExecFloat.OCP.MX.E8M0)
    (values : Array (Model format)) : ExecFloat.OCP.MX.Block format :=
  ofCode { scale := scale.toCode, values }

/--
Construct a block from nominal static-byte elements.

The element family determines the block descriptor. Conversion to the proof model happens only at
this storage boundary, so application code can keep using the ordinary executable low-bit type.
-/
@[inline] def ofElements {F : Type u} [StaticByte.Family F]
    (scale : ExecFloat.OCP.MX.E8M0)
    (values : Array (FloatLib.Floats.ExecFloat F)) :
    ExecFloat.OCP.MX.Block (StaticByte.Family.format (F := F)) :=
  ofComponents scale <|
    values.map fun value => StaticByte.toModel (F := F) value

/-- Configured E8M0 scale stored by the block. -/
@[inline] def scale (value : ExecFloat.OCP.MX.Block format) :
    ExecFloat.OCP.MX.E8M0 :=
  E8M0.ofCode value.toCode.scale

/-- Binary-interchange element words stored by the block. -/
@[inline] def values (value : ExecFloat.OCP.MX.Block format) :
    Array (Model format) :=
  value.toCode.values

/-- Decode each scaled element. An empty block succeeds without inspecting the scale. -/
@[inline] def decode? (value : ExecFloat.OCP.MX.Block format) :
    Option (Array Numerics.Dyadic) :=
  value.toCode.decode?

end Block
end FloatLib.Floats.ExecFloat.OCP.MX
