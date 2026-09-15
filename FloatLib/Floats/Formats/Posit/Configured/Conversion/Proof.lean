/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Real
public import FloatLib.Floats.ExecFloat.Conversion.Runtime
import FloatLib.Floats.Formats.Posit.Cast.Widening

/-!
# Configured posit conversion proofs

The conversion relation specifies finite results through real posit rounding and the complete
decoded model. Its implementation proof uses the rational-to-real rounding bridge and codec
inverse laws. The exponent size is fixed at two bits by the Posit Standard (2022), so width is the
only descriptor parameter.

Conversion to an equally wide or wider descriptor appends zero bits to the source word.
The configured results follow from exact model widening and the codec inverse laws.
Complete decoding and default conversion preserve zero and NaR as well as finite values.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {source target : Format}
    {sourcePlan : Configured.StoragePlan source} {targetPlan : Configured.StoragePlan target}
    {sourceCode targetCode : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec sourcePlan (Model source) sourceCode]
    [FloatLib.Floats.ExecFloat.ModelCodec targetPlan (Model target) targetCode]

private theorem model_decode_eq_toRat?_elim {format : Format} (value : Model format) :
    Model.decode value = value.toRat?.elim (.exceptional .notAReal) .finite := by
  change value.decodeExact.forget = value.decodeExact.toRat?.elim _ _
  cases value.decodeExact <;> rfl

/-- Appending zero bits preserves the complete configured observation, including zero and NaR. -/
theorem decode_ofModel_widen (hw : source.bits ≤ target.bits)
    (value : FloatLib.Floats.ExecFloat (Configured.Family source sourceCode sourcePlan)) :
    decode (ofModel (plan := targetPlan) (code := targetCode)
      (Model.ofNatBits (toNatBits value * 2 ^ (target.bits - source.bits)))) = decode value := by
  simpa only [decode, toNatBits, toModel, ofModel, Configured.Family.toModel_ofModel,
    model_decode_eq_toRat?_elim] using
    congrArg (fun q : Option Rat => q.elim (NumericalValue.exceptional .notAReal) .finite)
      (Model.toRat?_widen target hw (toModel value))

namespace Conversion

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/--
Finite conversion follows real posit rounding, with exact status for the delivered model.

The real rounder uses the standard appended-bit boundary, minPos underflow, and maxPos saturation.
Model equality retains the complete word. Infinity and exceptional observations obey their
explicit policies. This proof-facing relation needs no real-number evaluation at runtime.
-/
def spec :
    Quantization.Spec Context (NumericalValue Rat)
      (FloatLib.Floats.ExecFloat.ConversionOutcome
        (FloatLib.Floats.ExecFloat (Configured.Family format code plan))) :=
  fun context input outcome =>
    match input with
    | .finite exact =>
        match outcome with
        | .success rounded indicators =>
            toModel rounded = Model.RealRounding.round format (exact : ℝ) ∧
              indicators = finiteStatus exact (toModel rounded)
        | .failure _ => False
    | .infinity negative => outcome = quantizeInfinity context negative
    | .exceptional exceptional => outcome = quantizeExceptional context exceptional

/-- Finite observations use the exact arbitrary-width posit rounder. -/
@[simp, grind =] theorem run_finite (context : Context) (exact : Rat) :
    run (format := format) (plan := plan) (code := code)
        context (.finite exact) =
      quantizeFinite exact :=
  rfl

/-- Infinity observations are handled only by the explicit posit infinity policy. -/
@[simp, grind =] theorem run_infinity (context : Context) (negative : Bool) :
    run (format := format) (plan := plan) (code := code)
        context (.infinity negative) =
      quantizeInfinity context negative :=
  rfl

/-- Exceptional observations are handled only by the explicit posit exceptional policy. -/
@[simp, grind =] theorem run_exceptional
    (context : Context) (exceptional : ExceptionalValue) :
    run (format := format) (plan := plan) (code := code)
        context (.exceptional exceptional) =
      quantizeExceptional context exceptional :=
  rfl

/-- The real rounding bridge and the codec inverse law establish the finite contract. -/
theorem implements_run :
    Quantization.Spec.Implements
      (spec (format := format) (plan := plan) (code := code))
      (run (format := format) (plan := plan) (code := code)) := by
  intro context input
  cases input with
  | finite exact =>
      change toModel (ofModel (Model.roundRat format exact)) =
          Model.RealRounding.round format (exact : ℝ) ∧ _
      simp [toModel, ofModel, Configured.Family.toModel_ofModel,
        Model.RealRounding.round_ratCast]
  | infinity negative => rfl
  | exceptional exceptional => rfl

/-- Real rounding plus the codec law determines the complete original outcome and status. -/
theorem spec_iff_eq_run (context : Context) (input : NumericalValue Rat)
    (outcome : FloatLib.Floats.ExecFloat.ConversionOutcome
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan))) :
    spec context input outcome ↔ outcome = run context input := by
  constructor
  · cases input with
    | finite exact =>
        cases outcome with
        | success rounded indicators =>
            rintro ⟨hmodel, rfl⟩
            rw [Model.RealRounding.round_ratCast] at hmodel
            have hrounded : rounded = ofModel (Model.roundRat format exact) := by
              rw [← hmodel]
              exact (Configured.Family.ofModel_toModel rounded).symm
            subst rounded
            simp only [run, quantizeFinite, toModel, ofModel,
              Configured.Family.toModel_ofModel]
        | failure reason => exact False.elim
    | infinity negative => exact id
    | exceptional exceptional => exact id
  · rintro rfl
    exact implements_run context input

/-- The installed exact decoder is the public configured posit decoder. -/
@[simp, grind =] theorem exactDecoder_run
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value =
      ExecFloat.Posit.decode value :=
  rfl

/-- Default conversion maps either infinity to `NaR`, as required by Posit Standard (2022), §6.5. -/
@[grind =] theorem run_default_infinity (negative : Bool) :
    run (format := format) (plan := plan) (code := code)
        Context.default (.infinity negative) =
      .success ExecFloat.Posit.nar { mappedSpecial := true } :=
  rfl

/-- Default conversion maps exceptional observations to `NaR`, including IEEE NaNs and posit `NaR`. -/
@[grind =] theorem run_default_exceptional (exceptional : ExceptionalValue) :
    run (format := format) (plan := plan) (code := code)
        Context.default (.exceptional exceptional) =
      .success ExecFloat.Posit.nar { mappedSpecial := true } :=
  rfl

/-- Quantizing a decoded finite source into a wider codec appends exactly the additional zero bits.
The statement concerns the successful value, not the conversion status. -/
theorem quantizeFinite_widen (hw : source.bits ≤ target.bits)
    (value : FloatLib.Floats.ExecFloat (Configured.Family source sourceCode sourcePlan))
    (exact : Rat) (hfinite : decode value = .finite exact) :
    (quantizeFinite (format := target) (plan := targetPlan) (code := targetCode) exact).value? =
      some (ofModel (Model.ofNatBits (toNatBits value * 2 ^ (target.bits - source.bits)))) := by
  have hq : (toModel value).toRat? = some exact := by
    change Model.decode (toModel value) = .finite exact at hfinite
    rw [model_decode_eq_toRat?_elim] at hfinite
    cases hq : (toModel value).toRat? <;> simp_all
  simp only [quantizeFinite, ConversionOutcome.value?,
    Model.roundRat_widen target hw (toModel value) exact hq]
  rfl

private theorem run_default_model_value (value : Model format) :
    (run (format := format) (plan := plan) (code := code)
      Context.default (Model.decode value)).value? = some (ofModel value) := by
  rw [model_decode_eq_toRat?_elim]
  cases hq : value.toRat? with
  | none =>
      have hn : value = Model.nar format :=
        (Model.isNaR_eq_true_iff value).mp ((Model.toRat?_eq_none_iff value).mp hq)
      subst value
      simp [run, quantizeExceptional, Context.default, nar, ofModel, ConversionOutcome.value?]
  | some q =>
      simp [run, quantizeFinite, Model.roundRat_toRat? value q hq, ConversionOutcome.value?]

/-- Default conversion into a wider codec returns the source word with appended zero bits.
This includes the unique zero and NaR words; the default exceptional-value policy preserves NaR. -/
theorem run_default_widen (hw : source.bits ≤ target.bits)
    (value : FloatLib.Floats.ExecFloat (Configured.Family source sourceCode sourcePlan)) :
    (run (format := target) (plan := targetPlan) (code := targetCode)
      Context.default (decode value)).value? =
      some (ofModel (Model.ofNatBits (toNatBits value * 2 ^ (target.bits - source.bits)))) := by
  rw [← decode_ofModel_widen (targetPlan := targetPlan) (targetCode := targetCode) hw value]
  simpa only [decode, toModel, ofModel, Configured.Family.toModel_ofModel] using
    run_default_model_value (plan := targetPlan) (code := targetCode)
      (Model.ofNatBits (toNatBits value * 2 ^ (target.bits - source.bits)))

end Conversion
end ExecFloat.Posit
end FloatLib.Floats
