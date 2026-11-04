/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Type
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime
public import FloatLib.Floats.Formats.Posit.Interval

/-!
# Outward rounding for configured posit endpoints

Interval arithmetic on configured posits reuses the candidate search of model-level posit
intervals, packing each endpoint through the existing storage codec, and it works for every
configured width and storage plan. So you can use `ExecFloat.Posit` with the common interval
operations as it is. The exact decoded check rejects NaR and overflow, as it does for model
endpoints, and `intervalRounding_enclose?` shows the codec changes neither outcome nor endpoints.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Posit

open FloatLib.Floats.Formats.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- An interval over the configured posit carrier, independent of its storage representation. -/
abbrev Interval :=
  Numerics.Interval (FloatLib.Floats.ExecFloat (Configured.Family format code plan))

/-- Outward rounding through the posit storage codec. Leaving the finite range is a failure. -/
def intervalRounding :
    Numerics.OutwardRounding
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) ℚ :=
  Numerics.OutwardRounding.ofCandidates toRat?
    (fun x ↦ (FloatLib.Floats.Formats.Posit.intervalCandidates format x).map ofModel)

/-- Changing the storage codec preserves success, failure, and both model endpoints. -/
theorem intervalRounding_enclose? (x : ℚ) :
    (intervalRounding (plan := plan) (code := code)).enclose? x =
      ((FloatLib.Floats.Formats.Posit.intervalRounding format).enclose? x).map
        (Numerics.Interval.map ofModel) := by
  simp only [intervalRounding, FloatLib.Floats.Formats.Posit.intervalRounding,
    Numerics.OutwardRounding.ofCandidates, Numerics.OutwardRounding.checkedCandidates?,
    Numerics.Interval.map, toRat?, toModel, ofModel, Configured.Family.toModel_ofModel]
  cases Model.toRat? (intervalCandidates format x).lo <;>
    cases Model.toRat? (intervalCandidates format x).hi <;> simp
  split <;> rfl

end FloatLib.Floats.ExecFloat.Posit
