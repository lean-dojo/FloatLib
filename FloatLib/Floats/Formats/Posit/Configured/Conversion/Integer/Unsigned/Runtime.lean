/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.Posit.Cast.Integer.Unsigned.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Configured unsigned integer conversions

These adapters apply the Posit Standard (2022) §6.4 word-sentinel policy through
any lawful configured codec. Integer width is independent of posit width.
The shared model kernel handles all numerical rounding and range decisions.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Convert unsigned bits to posit, reserving the MSB-only input word for NaR. -/
@[inline] def ofUnsigned {width : Nat} (value : BitVec width)
    (hwidth : 0 < width := by decide) : Value :=
  ofModel (Model.ofUnsigned format value hwidth)

/-- Convert posit to unsigned bits, with nearest-even rounding before the range check. -/
@[inline] def toUnsigned (width : Nat) (value : Value)
    (hwidth : 0 < width := by decide) : BitVec width :=
  Model.toUnsigned width (toModel value) hwidth

end ExecFloat.Posit
end FloatLib.Floats
