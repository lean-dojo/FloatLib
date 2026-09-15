/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.E8M0.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactNumericalSystem
public import FloatLib.Numerics.Operation.Semantics

/-!
# Numerical semantics of E8M0 scaling

E8M0 is an exponent-only scale rather than a sign/exponent/fraction float. Its runtime carrier
remains one byte. The contracts in this module relate that byte and the existing exact decoders to
the same `NumericalSystem` and `Operation` interfaces used by ordinary floats and other numerical
representations.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.E8M0

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model
open FloatLib.Numerics

/-- E8M0 codes interpreted as exact positive dyadic scales, with `0xff` denoting NaN. -/
def numericalSystem : NumericalSystem where
  Code := E8M0
  Scalar := Numerics.Dyadic
  denote scale :=
    match toDyadic? scale with
    | some value => .finite value
    | none => .exceptional .nan

/-- An E8M0 code with an erased proof of its exact finite scale. -/
abbrev AtFinite (value : Numerics.Dyadic) :=
  numericalSystem.AtFinite value

/-- Finite E8M0 representation is exactly successful dyadic decoding. -/
theorem numericalSystem_represents_iff (scale : E8M0)
    (value : Numerics.Dyadic) :
    numericalSystem.Represents scale value ↔ toDyadic? scale = some value := by
  unfold NumericalSystem.Represents numericalSystem
  cases hdecode : toDyadic? scale with
  | none => simp [hdecode]
  | some decoded => simp [hdecode]

/-- Recover successful E8M0 decoding from a finite representation proof. -/
theorem toDyadic?_eq_some_of_represents {scale : E8M0}
    {value : Numerics.Dyadic}
    (hscale : numericalSystem.Represents scale value) :
    toDyadic? scale = some value :=
  (numericalSystem_represents_iff scale value).1 hscale

/-- Apply the exponent carried by an E8M0 scale to an exact dyadic. -/
@[inline] def scaledValue (scale value : Numerics.Dyadic) : Numerics.Dyadic :=
  { value with exponent := value.exponent + scale.exponent }

/-- E8M0 scaling is exact on every represented finite scale. -/
theorem scaleDyadic_refines :
    Operation.Checked2 numericalSystem
      (NumericalSystem.exact Numerics.Dyadic)
      (NumericalSystem.exact Numerics.Dyadic) scaleDyadic?
      (fun scale value => .finite (scaledValue scale value)) := by
  intro scale code scaleValue value hscale hvalue
  have hdecode := toDyadic?_eq_some_of_represents hscale
  have hcode : code = value :=
    (NumericalSystem.exact_represents_iff code value).1 hvalue
  subst code
  unfold toDyadic? at hdecode
  cases hexponent : exponent? scale with
  | none => simp [hexponent] at hdecode
  | some exponent =>
      simp [hexponent] at hdecode
      have hscaleValue :
          scaleValue = ({ negative := false, significand := 1, exponent } :
            Numerics.Dyadic) :=
        (Option.some.inj hdecode).symm
      subst scaleValue
      simp [scaleDyadic?, hexponent, scaledValue, NumericalSystem.exact]

/-- Decoding one block element applies the represented E8M0 scale exactly. -/
theorem decodeElement_refines (fmt : FloatFormat) :
    Operation.Checked2 numericalSystem (Model.exactNumericalSystem fmt)
      (NumericalSystem.exact Numerics.Dyadic)
      (decodeElement? (fmt := fmt))
      (fun scale value => .finite (scaledValue scale value)) := by
  intro scale code scaleValue value hscale hvalue
  unfold decodeElement?
  rw [Model.toDyadic?_eq_some_of_exactRepresents hvalue]
  exact scaleDyadic_refines scale value scaleValue value hscale
    ((NumericalSystem.exact_represents_iff value value).2 rfl)

end FloatLib.Floats.Formats.OCP.MX.E8M0
