/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Conversion.Runtime
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Proof
public import FloatLib.Floats.ExecFloat.Conversion.Runtime

/-!
# P3109 conversion proofs

These theorems expose the executable equations, connect conversion output to the proved
round-then-saturate projection semantics, and discharge the declared quantizer contract.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats
namespace ExecFloat.P3109
namespace Conversion

variable {format : Formats.P3109.Format}

/-- Every P3109 conversion is the policy-selected projection with its computed status. -/
@[simp, grind =] theorem run_eq_success
    (policy : Formats.P3109.ProjectionPolicy)
    (input : NumericalValue Rat) :
    run (format := format) policy input =
      .success (ExecFloat.P3109.projectRat policy input)
        (status format policy input) :=
  rfl

/-- Finite conversion uses the exact rational projection path directly. -/
@[grind =] theorem run_finite
    (policy : Formats.P3109.ProjectionPolicy) (exact : Rat) :
    run (format := format) policy (.finite exact) =
      .success (ExecFloat.P3109.ofRat policy exact)
        (status format policy (.finite exact)) :=
  rfl

/-- Infinity conversion is controlled entirely by the named P3109 projection policy. -/
@[simp, grind =] theorem run_infinity
    (policy : Formats.P3109.ProjectionPolicy) (negative : Bool) :
    run (format := format) policy (.infinity negative) =
      .success (ExecFloat.P3109.projectRat policy (.infinity negative))
        (status format policy (.infinity negative)) :=
  rfl

/-- Exceptional conversion is controlled entirely by the named P3109 projection policy. -/
@[simp, grind =] theorem run_exceptional
    (policy : Formats.P3109.ProjectionPolicy)
    (exceptional : ExceptionalValue) :
    run (format := format) policy (.exceptional exceptional) =
      .success (ExecFloat.P3109.projectRat policy (.exceptional exceptional))
        (status format policy (.exceptional exceptional)) :=
  rfl

/-- Decoding a conversion result yields the proved P3109 round-then-saturate datum. -/
theorem sameDatum_decode_run_value
    (policy : Formats.P3109.ProjectionPolicy)
    (input : NumericalValue Rat) :
    Formats.P3109.Format.SameDatum
      (ExecFloat.P3109.decode
        (ExecFloat.P3109.projectRat (format := format) policy input))
      (format.projectRatValue policy input) :=
  ExecFloat.P3109.decode_projectRat policy input

/-- The codec bridge supplies the semantic clause as well as the complete word and status. -/
theorem implements_run :
    Quantization.Spec.Implements
      (spec (format := format))
      (run (format := format)) := by
  intro policy input
  exact ⟨rfl, rfl, ExecFloat.P3109.decode_projectRat policy input⟩

/-- The semantic contract retains the converter's complete outcome, including its status. -/
theorem spec_iff_eq_run
    (policy : Formats.P3109.ProjectionPolicy) (input : NumericalValue Rat)
    (outcome : FloatLib.Floats.ExecFloat.ConversionOutcome (ExecFloat.P3109 format)) :
    spec policy input outcome ↔ outcome = run policy input := by
  constructor
  · cases outcome with
    | success value indicators =>
        rintro ⟨rfl, rfl, _⟩
        rfl
    | failure reason => exact False.elim
  · rintro rfl
    exact implements_run policy input

/-- Any successful outcome admitted by the contract denotes the policy-selected datum. -/
theorem sameDatum_of_spec
    (policy : Formats.P3109.ProjectionPolicy) (input : NumericalValue Rat)
    (value : ExecFloat.P3109 format)
    (indicators : FloatLib.Floats.ExecFloat.ConversionStatus)
    (h : spec policy input (.success value indicators)) :
    Formats.P3109.Format.SameDatum
      (ExecFloat.P3109.decode value) (format.projectRatValue policy input) :=
  h.2.2

/-- The installed P3109 exact decoder exposes exact rational denotations. -/
@[simp, grind =] theorem exactDecoder_run
    (value : ExecFloat.P3109 format) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value =
      decodeRat value :=
  rfl

end Conversion
end ExecFloat.P3109
end FloatLib.Floats
