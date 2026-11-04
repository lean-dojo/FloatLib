/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Cast.Integer.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Configured posit conversions for fixed-width signed integers

`ofFixedInt` and `toFixedInt` convert between configured posits and signed integers, and the
integer width has nothing to do with the posit width. Both keep the Section 6.4 MSB-only sentinel
intact through any lawful posit model codec. Going from integer to posit rounds the exact signed
value once, by Section 4.1, and going back rounds to the nearest integer with ties to even and
checks the signed range after rounding.

The catch is that the signed minimum shares its word with the sentinel. On that one word these
adapters differ from generic numerical conversion through an ordinary `FixedInt` decoder, which
reads it as a finite integer.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit
open FloatLib.Numerics.Representations

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Convert a signed integer to a configured posit, reserving the MSB-only input for NaR. -/
@[inline] def ofFixedInt {width : Nat} (value : FixedInt width)
    (hwidth : 0 < width := by decide) : Value :=
  ofModel (Model.ofFixedInt format value hwidth)

/--
Convert a configured posit to a signed integer with nearest-even rounding.
NaR and a rounded value outside the signed range produce the MSB-only sentinel.
-/
@[inline] def toFixedInt (width : Nat) (value : Value)
    (hwidth : 0 < width := by decide) : FixedInt width :=
  Model.toFixedInt width (toModel value) hwidth

end ExecFloat.Posit
end FloatLib.Floats
