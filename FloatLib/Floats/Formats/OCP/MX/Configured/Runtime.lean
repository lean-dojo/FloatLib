/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Configured.Core

/-!
# Executable configured E8M0 operations

Checked decoding and construction of the E8M0 scale on the common carrier, and exact scaling of a
dyadic by a finite scale.
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

end FloatLib.Floats.ExecFloat.OCP.MX
