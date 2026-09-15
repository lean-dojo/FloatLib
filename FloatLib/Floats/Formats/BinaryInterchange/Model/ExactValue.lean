/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode

/-!
# Exact values represented by binary models

`Model.ExactValue` records the complete interpretation of an executable bit pattern without
introducing another floating-point carrier. Finite values retain their exact dyadic decoding, so
positive and negative zero remain distinct when the format represents both. Infinities retain
their sign, and NaNs retain their sign, signaling class, and fraction payload.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Complete exact interpretation of a `Model` bit pattern. -/
inductive ExactValue where
  /-- A finite exact dyadic, including the sign of zero. -/
  | finite (value : Numerics.Dyadic)
  /-- A signed infinity. -/
  | infinity (sign : Bool)
  /-- A NaN with its sign, signaling class, and complete fraction field. -/
  | nan (sign : Bool) (signaling : Bool) (payload : Nat)
  deriving Repr, DecidableEq

/--
Decode an executable bit pattern to its complete exact value.

This function is computational. It refines the real-valued numerical interpretation by retaining
the distinctions that `ℝ` necessarily forgets.
-/
@[inline] def exactValue {fmt : FloatFormat} (x : Model fmt) : ExactValue :=
  match toDyadic? x with
  | some value => .finite value
  | none =>
      if isInf x then
        .infinity (signBit x)
      else
        .nan (signBit x) (isSNaN x) (fracField x)

/-- A successful dyadic decoding determines the exact finite value. -/
@[simp] theorem exactValue_eq_finite_of_toDyadic?_eq_some
    {fmt : FloatFormat} {x : Model fmt} {value : Numerics.Dyadic}
    (hvalue : toDyadic? x = some value) :
    exactValue x = .finite value := by
  simp [exactValue, hvalue]

/-- Exact finiteness is equivalent to successful decoding with the indexed dyadic. -/
@[simp] theorem exactValue_eq_finite_iff
    {fmt : FloatFormat} {x : Model fmt} {value : Numerics.Dyadic} :
    exactValue x = .finite value ↔ toDyadic? x = some value := by
  constructor
  · intro hvalue
    cases hdecode : toDyadic? x with
    | none =>
        simp only [exactValue, hdecode] at hvalue
        split at hvalue <;> cases hvalue
    | some decoded =>
        have hdecoded : decoded = value := by
          simpa [exactValue, hdecode] using hvalue
        exact congrArg some hdecoded
  · exact exactValue_eq_finite_of_toDyadic?_eq_some

end Model
end FloatLib.Floats.Formats.BinaryInterchange
