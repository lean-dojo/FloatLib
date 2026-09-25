/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode
public import FloatLib.Numerics.Core.Proof

/-!
# Exact policy-aware numerical systems

The adapter interprets every finite FP8, FP6, FP4, FNUZ, or IEEE code as an exact dyadic. It uses
the complete `FloatFormat`, so an all-ones exponent can mean infinity, a finite value, or part of a
NaN encoding according to the selected representation policy. A NaN is denoted by its fraction
field, sign bit, and signaling class, the same convention as `ExactValue.nan` and the real-valued
`numericalSystem`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

/--
Exact numerical-system semantics for a policy-aware binary format.

Finite codes denote their exact dyadic value, infinities carry their sign, and a NaN carries its
fraction field as payload together with its sign bit and signaling class.
-/
def exactNumericalSystem (fmt : FloatFormat) : NumericalSystem where
  Code := Model fmt
  Scalar := Numerics.Dyadic
  denote x :=
    match Model.toDyadic? x with
    | some value => .finite value
    | none =>
        if Model.isInf x then .infinity (Model.signBit x)
        else .exceptional (.nan (some (Model.fracField x)) (Model.signBit x) (Model.isSNaN x))

/-- A policy-aware binary word with an erased proof of its exact finite dyadic value. -/
abbrev ExactAtFinite (fmt : FloatFormat) (value : Numerics.Dyadic) :=
  (exactNumericalSystem fmt).AtFinite value

/-- Exact decoding is precisely finite representation in the general interface. -/
theorem exactNumericalSystem_represents_iff {fmt : FloatFormat} (x : Model fmt)
    (value : Numerics.Dyadic) :
    (exactNumericalSystem fmt).Represents x value ↔ Model.toDyadic? x = some value := by
  unfold NumericalSystem.Represents exactNumericalSystem
  cases hdecode : Model.toDyadic? x with
  | none =>
      simp only [hdecode]
      split <;> simp
  | some decoded => simp [hdecode]

/-- A represented finite value is exactly the result of decoding its code. -/
theorem toDyadic?_eq_some_of_exactRepresents {fmt : FloatFormat} {x : Model fmt}
    {value : Numerics.Dyadic}
    (hvalue : (exactNumericalSystem fmt).Represents x value) :
    Model.toDyadic? x = some value :=
  (exactNumericalSystem_represents_iff x value).mp hvalue

/-- Successful finite decoding establishes representation in the general interface. -/
theorem exactRepresents_of_toDyadic?_eq_some {fmt : FloatFormat} {x : Model fmt}
    {value : Numerics.Dyadic} (hdecode : Model.toDyadic? x = some value) :
    (exactNumericalSystem fmt).Represents x value :=
  (exactNumericalSystem_represents_iff x value).mpr hdecode

/-- Non-IEEE binary encodings never denote infinity in the general interface. -/
theorem exactNumericalSystem_ne_infinity_of_nonIEEE {fmt : FloatFormat}
    (hfmt : fmt.encoding ≠ .ieee) (x : Model fmt) (sign : Bool) :
    (exactNumericalSystem fmt).denote x ≠ .infinity sign := by
  unfold exactNumericalSystem
  cases hdecode : Model.toDyadic? x with
  | some value => simp [hdecode]
  | none =>
      have hinf : Model.isInf x = false := by
        cases hencoding : fmt.encoding <;> simp_all [Model.isInf]
      simp [hdecode, hinf]

end FloatLib.Floats.Formats.BinaryInterchange.Model
