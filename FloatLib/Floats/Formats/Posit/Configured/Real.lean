/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured
public import FloatLib.Floats.Formats.Posit.Semantics.Real

/-!
# Optional real-valued views of configured posits

This adapter embeds the exact rational value of an ordinary configured posit into mathlib's
`Real`. The optional view returns `none` for NaR; the complete view retains its exceptional status.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [codec : FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Complete real-valued view of the exact rational semantics. -/
@[inline] noncomputable def decodeReal
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    FloatLib.Numerics.NumericalValue ℝ :=
  Model.decodeReal (toModel value)

/-- Exact real value of an ordinary configured posit, or `none` exactly for NaR. -/
@[inline] noncomputable def toReal?
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    Option ℝ :=
  Model.toReal? (toModel value)

/-- The public optional real view is absent precisely for the unique NaR value. -/
@[simp, grind =] theorem toReal?_eq_none_iff
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    toReal? value = none ↔ isNaR value = true :=
  Model.toReal?_eq_none_iff (toModel value)

end ExecFloat.Posit
end FloatLib.Floats
