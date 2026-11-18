/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.Posit.Cast.Integer.Unsigned.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Configured unsigned integer conversions

Unsigned integers follow the Posit Standard (2022) §6.4 word-sentinel policy through any lawful
configured codec, and here too the integer width can differ from the posit width. Every numerical
rounding and range decision happens in the shared model kernel.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Posit Standard (2022), §6.4: convert unsigned bits, reserving the MSB-only input for NaR. -/
@[inline] def ofUnsigned {width : Nat} (value : BitVec width)
    (hwidth : 0 < width := by decide) : Value :=
  ofModel (Model.ofUnsigned format value hwidth)

/-- Posit Standard (2022), §6.4: round to the nearest even unsigned integer, then check range. -/
@[inline] def toUnsigned (width : Nat) (value : Value)
    (hwidth : 0 < width := by decide) : BitVec width :=
  Model.toUnsigned width (toModel value) hwidth

end ExecFloat.Posit
end FloatLib.Floats
