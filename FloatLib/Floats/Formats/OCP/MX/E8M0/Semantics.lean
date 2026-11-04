/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.E8M0.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactNumericalSystem
public import FloatLib.Numerics.Operation.Semantics
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime

/-!
# Numerical semantics of E8M0 scaling

E8M0 has no sign and no fraction, only an exponent, and at runtime it's one byte. The contracts
here connect that byte and its exact decoders to the `NumericalSystem` and `Operation` interfaces
that ordinary floats and the other numerical representations use. A finite code denotes a positive
power of two, so scaling by code `130` multiplies an exact value by `8`.
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

/-- A scale represents a dyadic value if and only if decoding it returns that value. -/
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

/--
Apply the exponent carried by an E8M0 scale to an exact dyadic.

This is the same field update as the body of `scaleDyadic?`, and it reads only the scale's
exponent. For a decoded scale, a positive power of two, it is the exact product `Dyadic.mul`
(`scaledValue_eq_mul_of_toDyadic?_eq_some`), which the refinement theorems below state.
-/
@[inline] def scaledValue (scale value : Numerics.Dyadic) : Numerics.Dyadic :=
  { value with exponent := value.exponent + scale.exponent }

/-- Adding a scale's exponent multiplies the exact value by two to that exponent. The scale's sign
and significand are never read. -/
private theorem toRat_scaledValue (scale value : Numerics.Dyadic) :
    (scaledValue scale value).toRat = value.toRat * 2 ^ scale.exponent := by
  rcases value with ⟨negative, significand, exponent⟩
  cases negative <;>
    simp [scaledValue, Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand,
      zpow_add₀ (two_ne_zero (α := ℚ)), mul_assoc]

/-- A finite E8M0 code denotes the positive power of two `2 ^ (code - 127)`. -/
theorem toRat_of_toDyadic?_eq_some {scale : E8M0} {scaleValue : Numerics.Dyadic}
    (hscale : toDyadic? scale = some scaleValue) :
    scaleValue.toRat = 2 ^ ((scale.toNatBits : Int) - 127) := by
  obtain ⟨exponent, hexponent, rfl⟩ := toDyadic?_eq_some_iff.mp hscale
  simp only [exponent?, Option.ite_none_left_eq_some, Option.some.injEq] at hexponent
  obtain ⟨-, rfl⟩ := hexponent
  simp [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand, bias, toNatBits]

/-- For a decoded E8M0 scale, shifting the exponent is the exact dyadic product. -/
theorem scaledValue_eq_mul_of_toDyadic?_eq_some {scale : E8M0} {scaleValue : Numerics.Dyadic}
    (hscale : toDyadic? scale = some scaleValue) (value : Numerics.Dyadic) :
    scaledValue scaleValue value = Numerics.Dyadic.mul scaleValue value := by
  obtain ⟨exponent, -, rfl⟩ := toDyadic?_eq_some_iff.mp hscale
  simp [scaledValue, Numerics.Dyadic.mul, Numerics.Dyadic.mulFields, Int.add_comm]

/-- Scaling by a decoded E8M0 scale multiplies the exact value by that scale. -/
theorem toRat_scaledValue_of_toDyadic?_eq_some {scale : E8M0} {scaleValue : Numerics.Dyadic}
    (hscale : toDyadic? scale = some scaleValue) (value : Numerics.Dyadic) :
    (scaledValue scaleValue value).toRat = scaleValue.toRat * value.toRat := by
  obtain ⟨exponent, -, rfl⟩ := toDyadic?_eq_some_iff.mp hscale
  rw [toRat_scaledValue, mul_comm]
  simp [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand]

/-- E8M0 scaling multiplies the exact value by the decoded scale, and it fails on the NaN scale and
nowhere else. -/
theorem map_toRat_scaleDyadic? (scale : E8M0) (value : Numerics.Dyadic) :
    (scaleDyadic? scale value).map Numerics.Dyadic.toRat =
      (toDyadic? scale).map fun scaleValue => scaleValue.toRat * value.toRat := by
  cases hscale : toDyadic? scale with
  | none => simp [scaleDyadic?, toDyadic?_eq_none_iff.mp hscale]
  | some scaleValue =>
      obtain ⟨exponent, hexponent, rfl⟩ := toDyadic?_eq_some_iff.mp hscale
      simp only [scaleDyadic?, hexponent, Option.map_some, Option.some.injEq]
      rw [← toRat_scaledValue_of_toDyadic?_eq_some hscale value]
      rfl

/-- On every represented finite scale, E8M0 scaling succeeds and returns the exact dyadic product
of the scale and the input. -/
theorem scaleDyadic_refines :
    Operation.Checked2 numericalSystem
      (NumericalSystem.exact Numerics.Dyadic)
      (NumericalSystem.exact Numerics.Dyadic) scaleDyadic?
      (fun scale value => .finite (Numerics.Dyadic.mul scale value)) := by
  intro scale code scaleValue value hscale hvalue
  have hdecode := toDyadic?_eq_some_of_represents hscale
  have hcode : code = value :=
    (NumericalSystem.exact_represents_iff code value).1 hvalue
  subst code
  obtain ⟨exponent, hexponent, rfl⟩ := toDyadic?_eq_some_iff.mp hdecode
  simp [scaleDyadic?, hexponent, NumericalSystem.exact, Numerics.Dyadic.mul,
    Numerics.Dyadic.mulFields, Int.add_comm]

/-- Decoding one finite block element under a finite scale succeeds and returns the exact dyadic
product of the scale and the element's value. -/
theorem decodeElement_refines (fmt : FloatFormat) :
    Operation.Checked2 numericalSystem (Model.exactNumericalSystem fmt)
      (NumericalSystem.exact Numerics.Dyadic)
      (decodeElement? (fmt := fmt))
      (fun scale value => .finite (Numerics.Dyadic.mul scale value)) := by
  intro scale code scaleValue value hscale hvalue
  unfold decodeElement?
  rw [Model.toDyadic?_eq_some_of_exactRepresents hvalue]
  exact scaleDyadic_refines scale value scaleValue value hscale
    ((NumericalSystem.exact_represents_iff value value).2 rfl)

end FloatLib.Floats.Formats.OCP.MX.E8M0
