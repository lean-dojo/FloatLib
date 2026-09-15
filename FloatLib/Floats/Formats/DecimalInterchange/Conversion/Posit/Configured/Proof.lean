/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Posit.Configured.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Posit.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Value.Proof

/-!
# Configured posit conversion refinement

The conversion equations hold for every width, storage plan and lawful codec.
Encoding and decoding add no rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion

open FloatLib.Floats
open FloatLib.Floats.Formats

variable {format : Posit.Format} {plan : Posit.Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Posit.Model format) code]

local notation "Value" => ExecFloat (Posit.Configured.Family format code plan)

/-- Configured posit-to-decimal conversion is exactly the model conversion. -/
@[simp] theorem fromConfiguredPosit_eq (target : Format) (mode : RoundingMode) (x : Value) :
    fromConfiguredPosit target mode x =
      fromPosit target mode (ExecFloat.Posit.toModel x) := rfl

/-- The encoded result decodes exactly to the model decimal-to-posit conversion. -/
@[simp] theorem toModel_toConfiguredPosit (x : Datum) :
    ExecFloat.Posit.toModel (toConfiguredPosit x : Value) = toPosit format x := by
  simp [toConfiguredPosit]

/-- A finite decimal input rounds once by the Posit Standard rule, for any lawful carrier. -/
theorem toConfiguredPosit_eq_real (x : Datum) {a : ℚ} (hx : x.toRat? = some a) :
    ExecFloat.Posit.toModel (toConfiguredPosit x : Value) =
      Posit.Model.RealRounding.round format (a : ℝ) := by
  rw [toModel_toConfiguredPosit]
  exact toPosit_eq_real format x hx

/-- A finite configured posit is projected from its exact rational value. -/
theorem fromConfiguredPosit_eq_project (target : Format) (mode : RoundingMode)
    (x : Value) {a : ℚ} (hx : ExecFloat.Posit.toRat? x = some a) :
    fromConfiguredPosit target mode x = project target mode a 0 false :=
  fromPosit_eq_project target mode (ExecFloat.Posit.toModel x) hx

end FloatLib.Floats.Formats.DecimalInterchange.Conversion
