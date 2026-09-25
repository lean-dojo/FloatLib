/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Family.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Proof
public import FloatLib.Floats.ExecFloat.Conversion.Runtime

/-!
# Configured binary-interchange conversion proofs

Configured conversion inherits the descriptor's default IEEE nearest-value contract and preserves
the complete outcome for every context.

It is the final transport layer between descriptor-level conversion semantics and the public packed
carrier. Storage selection is intentionally absent from the statement: any configured backend must
decode to the same converted value and status, so changing from a native word to arbitrary-width
storage cannot change the numerical contract.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.Binary
namespace Conversion

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Finite observations are handled by the configured binary finite quantizer. -/
@[simp, grind =] theorem run_finite (context : Context) (exact : SignedRat) :
    run (format := format) (plan := plan) (code := code)
        context (.finite exact) =
      quantizeFinite context exact :=
  rfl

/-- Infinity observations are handled only by the explicit infinity policy. -/
@[simp, grind =] theorem run_infinity (context : Context) (negative : Bool) :
    run (format := format) (plan := plan) (code := code)
        context (.infinity negative) =
      quantizeInfinity context negative :=
  rfl

/-- Exceptional observations are handled only by the explicit exceptional policy. -/
@[simp, grind =] theorem run_exceptional
    (context : Context) (exceptional : ExceptionalValue) :
    run (format := format) (plan := plan) (code := code)
        context (.exceptional exceptional) =
      quantizeExceptional context exceptional :=
  rfl

/-- The configured carrier inherits the descriptor's nearest-value and complete-outcome clauses. -/
theorem implements_run :
    Quantization.Spec.Implements
      (spec (format := format) (plan := plan) (code := code))
      (run (format := format) (plan := plan) (code := code)) :=
  implements_runWith configuredPack

/-- The semantic contract retains the exact configured word and every status field. -/
theorem spec_iff_eq_run (context : Context) (input : NumericalValue SignedRat)
    (outcome : FloatLib.Floats.ExecFloat.ConversionOutcome
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan))) :
    spec context input outcome ↔ outcome = run context input :=
  specWith_iff_eq_runWith configuredPack context input outcome

/-- A successful default IEEE conversion satisfies the nearest-value predicate after decoding. -/
theorem nearestFinite_of_spec (context : Context) (exact : SignedRat)
    (rounded : FloatLib.Floats.ExecFloat (Configured.Family format code plan))
    (indicators : FloatLib.Floats.ExecFloat.ConversionStatus)
    (hpolicy : context.quantization = QuantizationPolicy.nearestEven)
    (hformat : format.isIEEE = true)
    (h : spec context (.finite exact) (.success rounded indicators)) :
    NearestFinite exact.value (toModel rounded) := by
  obtain ⟨model, houtcome, hnearest⟩ := h.2 hpolicy hformat
  have hrounded : rounded = configuredPack model := (ConversionOutcome.success.inj houtcome).1
  rw [hrounded]
  simpa only [configuredPack, toModel, ofModel, Configured.Family.toModel_ofModel] using hnearest

/-- The installed exact decoder is the public signed-rational decoder. -/
@[simp, grind =] theorem exactDecoder_run
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value =
      ExecFloat.Binary.decode value :=
  rfl

/--
A default-context finite conversion is the canonical nearest-even rational rounder applied to the
sign bit and magnitude of the signed rational.

The delivered value is `Model.roundRat`. For conventional IEEE destinations and finite results,
`Model.toReal_roundRatScaled_eq_roundAt` relates that rounder to nearest-even rounding over `ℝ`.
-/
theorem run_default_finite (exact : SignedRat) :
    run (format := format) (plan := plan) (code := code) Context.default (.finite exact) =
      .success
        (ofModel (Model.roundRat format exact.negative exact.value.num.natAbs exact.value.den))
        (finiteStatus Context.default exact.value
          (Model.roundRat format exact.negative exact.value.num.natAbs exact.value.den)) := by
  have hpolicy : Context.default.quantization = QuantizationPolicy.nearestEven := rfl
  simp only [run, runWith, quantizeFiniteWith, hpolicy,
    Model.Policy.roundRat_nearestEven_eq_execFloat _ _ _ _ _ exact.value.den_nz]
  rfl

/--
Converting an exact negative zero preserves its sign when the destination supports negative zero.

For an encoding with one unsigned zero, `zero true` is that encoding's positive zero, so the
statement also covers FNUZ destinations.
-/
theorem run_default_negZero_value? :
    (run (format := format) (plan := plan) (code := code) Context.default
      (.finite SignedRat.negZero)).value? = some (ExecFloat.Binary.zero true) := by
  rw [run_default_finite]
  simp [ExecFloat.Binary.zero, Model.roundRat_num_zero, ConversionOutcome.value?]

/-- Rejecting infinity produces the corresponding explicit failure. -/
@[grind =] theorem run_infinity_reject (negative : Bool) :
    run (format := format) (plan := plan) (code := code)
        ({ infinity := .reject } : Context) (.infinity negative) =
      .failure (.infinity .source negative) :=
  rfl

/-- Rejecting an exceptional observation preserves its complete common classification. -/
@[grind =] theorem run_exceptional_reject (exceptional : ExceptionalValue) :
    run (format := format) (plan := plan) (code := code)
        ({ exceptional := .reject } : Context) (.exceptional exceptional) =
      .failure (.exceptional .source exceptional) :=
  rfl

/-- A configured NaN decodes to the NaN observation carrying its fraction field, sign, and class. -/
theorem decode_of_isNaN {source : FloatFormat}
    {sourcePlan : Configured.StoragePlan source} {sourceCode : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec sourcePlan (Model source) sourceCode]
    (value : FloatLib.Floats.ExecFloat (Configured.Family source sourceCode sourcePlan))
    (hnan : Model.isNaN (toModel value) = true) :
    ExecFloat.Binary.decode value =
      .exceptional (.nan (some (Model.fracField (toModel value)))
        (Model.signBit (toModel value)) (Model.isSNaN (toModel value))) := by
  have hdyadic : Model.toDyadic? (toModel value) = none := by
    cases h : Model.toDyadic? (toModel value) with
    | none => rfl
    | some d => simp [Model.isNaN_eq_false_of_toDyadic?_some h] at hnan
  have hinf : Model.isInf (toModel value) = false := by
    cases h : Model.isInf (toModel value) with
    | false => rfl
    | true => simp [Model.isNaN_eq_false_of_isInf_eq_true _ h] at hnan
  simp [ExecFloat.Binary.decode, Model.exactNumericalSystem, hdyadic, hinf, NumericalValue.map]

/--
Default conversion of a decoded configured NaN is `Model.castWithStatus` on the source model.
An IEEE destination keeps the sign and any payload that fits; an oversized payload becomes zero.
Maximum-NaN encodings keep only the sign, while FNUZ has a single NaN. Invalid is raised exactly
for a signaling source. The destination must have a NaN encoding; when it has none,
`run_default_decode_of_isNaN_of_encoding_finite` shows that conversion fails while
`Model.castWithStatus` raises invalid.
-/
theorem run_default_decode_of_isNaN {source : FloatFormat}
    {sourcePlan : Configured.StoragePlan source} {sourceCode : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec sourcePlan (Model source) sourceCode]
    (value : FloatLib.Floats.ExecFloat (Configured.Family source sourceCode sourcePlan))
    (mode : Model.IEEERoundingMode)
    (hnan : Model.isNaN (toModel value) = true) (hformat : format.encoding ≠ .finite) :
    run (format := format) (plan := plan) (code := code) Context.default
        (ExecFloat.Binary.decode value) =
      .success (ofModel (Model.castWithStatus source format (toModel value) mode).value)
        { invalid := (Model.castWithStatus source format (toModel value) mode).status.invalid } := by
  rw [decode_of_isNaN value hnan]
  exact runWith_default_nan_eq_castWithStatus configuredPack (toModel value) mode hnan hformat

/--
Default conversion of a decoded configured NaN into a destination with no NaN encoding fails with
the source NaN as the reported exceptional value, and `Model.castWithStatus` on the same source
raises invalid.

`ExecFloat` keeps the explicit failure because the destination has no NaN to deliver. The
descriptor model instead returns positive zero with the invalid flag set, so both paths classify
the conversion as invalid.
-/
theorem run_default_decode_of_isNaN_of_encoding_finite {source : FloatFormat}
    {sourcePlan : Configured.StoragePlan source} {sourceCode : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec sourcePlan (Model source) sourceCode]
    (value : FloatLib.Floats.ExecFloat (Configured.Family source sourceCode sourcePlan))
    (mode : Model.IEEERoundingMode)
    (hnan : Model.isNaN (toModel value) = true) (hformat : format.encoding = .finite) :
    run (format := format) (plan := plan) (code := code) Context.default
        (ExecFloat.Binary.decode value) =
      .failure (.exceptional .source
        (.nan (some (Model.fracField (toModel value)))
          (Model.signBit (toModel value)) (Model.isSNaN (toModel value)))) ∧
      (Model.castWithStatus source format (toModel value) mode).status.invalid = true := by
  rw [decode_of_isNaN value hnan]
  exact runWith_default_nan_of_encoding_finite configuredPack (toModel value) mode hnan hformat

end Conversion
end ExecFloat.Binary
end FloatLib.Floats
