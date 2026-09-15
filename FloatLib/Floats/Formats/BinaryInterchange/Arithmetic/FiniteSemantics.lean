/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactNumericalSystem
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core
public import FloatLib.Numerics.Operation.Semantics

/-!
# Correctness of finite arithmetic

The arithmetic layer decodes represented inputs to exact dyadics, performs one exact operation,
and quantizes once under the selected output policy. These theorems expose that contract through
the family-independent `NumericalSystem` and `Operation` interfaces.

Subtraction needs one format-specific convention. IEEE, OCP E4M3, FP4, and FP6 retain signed zero,
so negation toggles the sign of zero. FNUZ has only one zero encoding, so its exact semantic
negation canonicalizes zero to positive zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

/-- Complete denotation produced by quantizing one exact dyadic. -/
@[inline] def quantizedValue (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (value : Numerics.Dyadic) : NumericalValue Numerics.Dyadic :=
  (exactNumericalSystem fmt).denote (Policy.roundDyadic fmt policy entropy value)

/-- Complete denotation produced by quantizing one exact rational magnitude. -/
def quantizedRatValue (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (sign : Bool) (num den : Nat) : NumericalValue Numerics.Dyadic :=
  match Policy.roundRat fmt policy entropy sign num den with
  | some result => (exactNumericalSystem fmt).denote result
  | none => .exceptional .undefined

private theorem map_roundRat_eq_some_quantizedRatValue
    (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (sign : Bool) (num den : Nat) (hden : den ≠ 0) :
    (Policy.roundRat fmt policy entropy sign num den).map
        (exactNumericalSystem fmt).denote =
      some (quantizedRatValue fmt policy entropy sign num den) := by
  cases hround : Policy.roundRat fmt policy entropy sign num den with
  | none =>
      unfold Policy.roundRat at hround
      rw [dif_neg hden] at hround
      split at hround <;> simp at hround
  | some result =>
      unfold quantizedRatValue
      rw [hround]
      change some ((exactNumericalSystem fmt).denote result) =
        some ((exactNumericalSystem fmt).denote result)
      rfl

/-- Denotation of the quantized exact quotient, or `undefined` for a zero divisor. -/
def divValue (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (left right : Numerics.Dyadic) : NumericalValue Numerics.Dyadic :=
  if right.significand == 0 then
    .exceptional .undefined
  else
    let sign := Bool.xor left.negative right.negative
    let exponentDifference := left.exponent - right.exponent
    let (numerator, denominator) :=
      match exponentDifference with
      | .ofNat shift => (Nat.shiftLeft left.significand shift, right.significand)
      | .negSucc shift => (left.significand, Nat.shiftLeft right.significand (shift + 1))
    quantizedRatValue fmt policy entropy sign numerator denominator

/-- Negation refines format-aware exact dyadic negation on every represented finite input. -/
theorem negExact_refines (fmt : FloatFormat) :
    Operation.Finite1 (exactNumericalSystem fmt) (exactNumericalSystem fmt)
      Model.neg (Model.negDyadic fmt) := by
  intro code value hvalue
  apply exactRepresents_of_toDyadic?_eq_some
  exact Model.toDyadic?_neg_of_toDyadic?_some code
    (toDyadic?_eq_some_of_exactRepresents hvalue)

/-- Finite addition performs exact dyadic addition followed by one quantization. -/
theorem addFinite_refines (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat) :
    Operation.Checked2 (exactNumericalSystem fmt) (exactNumericalSystem fmt)
      (exactNumericalSystem fmt) (addFinite? fmt policy entropy)
      (fun left right => quantizedValue fmt policy entropy
        (Model.addDyadic left right)) := by
  intro left right x y hx hy
  unfold addFinite?
  rw [toDyadic?_eq_some_of_exactRepresents hx, toDyadic?_eq_some_of_exactRepresents hy]
  rfl

/-- Finite subtraction performs exact format-aware negation and addition, then quantizes once. -/
theorem subFinite_refines (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat) :
    Operation.Checked2 (exactNumericalSystem fmt) (exactNumericalSystem fmt)
      (exactNumericalSystem fmt) (subFinite? fmt policy entropy)
      (fun left right => quantizedValue fmt policy entropy
        (Model.addDyadic left (Model.negDyadic fmt right))) := by
  intro left right x y hx hy
  unfold subFinite? addFinite?
  rw [toDyadic?_eq_some_of_exactRepresents hx,
    Model.toDyadic?_neg_of_toDyadic?_some right
      (toDyadic?_eq_some_of_exactRepresents hy)]
  rfl

/-- Finite multiplication performs an exact dyadic product followed by one quantization. -/
theorem mulFinite_refines (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat) :
    Operation.Checked2 (exactNumericalSystem fmt) (exactNumericalSystem fmt)
      (exactNumericalSystem fmt) (mulFinite? fmt policy entropy)
      (fun left right => quantizedValue fmt policy entropy (mulDyadic left right)) := by
  intro left right x y hx hy
  unfold mulFinite? mulFiniteSpec?
  rw [toDyadic?_eq_some_of_exactRepresents hx, toDyadic?_eq_some_of_exactRepresents hy]
  rfl

/-- Finite fused multiply-add has one quantization after the exact product and sum. -/
theorem fmaFinite_refines (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat) :
    Operation.Checked3 (exactNumericalSystem fmt) (exactNumericalSystem fmt)
      (exactNumericalSystem fmt) (exactNumericalSystem fmt) (fmaFinite? fmt policy entropy)
      (fun x y z => quantizedValue fmt policy entropy
        (Model.addDyadic (mulDyadic x y) z)) := by
  intro a b c x y z hx hy hz
  unfold fmaFinite?
  rw [toDyadic?_eq_some_of_exactRepresents hx, toDyadic?_eq_some_of_exactRepresents hy,
    toDyadic?_eq_some_of_exactRepresents hz]
  rfl

/-- Mixed-format multiply-add decodes storage operands and quantizes once into the accumulator. -/
theorem mulAddFinite_refines (storage accumulator : FloatFormat)
    (policy : QuantizationPolicy) (entropy : Nat) :
    Operation.Checked3 (exactNumericalSystem storage) (exactNumericalSystem storage)
      (exactNumericalSystem accumulator) (exactNumericalSystem accumulator)
      (mulAddFinite? storage accumulator policy entropy)
      (fun x y acc => quantizedValue accumulator policy entropy
        (Model.addDyadic (mulDyadic x y) acc)) := by
  intro a b c x y z hx hy hz
  unfold mulAddFinite?
  rw [toDyadic?_eq_some_of_exactRepresents hx, toDyadic?_eq_some_of_exactRepresents hy,
    toDyadic?_eq_some_of_exactRepresents hz]
  rfl

/-- Finite division refines exact rational division whenever the divisor is nonzero. -/
theorem divFinite_refines (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat) :
    Operation.Checked2On (exactNumericalSystem fmt) (exactNumericalSystem fmt)
      (exactNumericalSystem fmt) (divFinite? fmt policy entropy)
      (divValue fmt policy entropy) (fun _ right => right.significand ≠ 0) := by
  intro left right x y hy hx hyrep
  change Numerics.Dyadic at x y
  have hleft := toDyadic?_eq_some_of_exactRepresents hx
  have hright := toDyadic?_eq_some_of_exactRepresents hyrep
  have hrun :
      divFinite? fmt policy entropy left right =
        Policy.roundRat fmt policy entropy (Bool.xor x.negative y.negative)
          (match x.exponent - y.exponent with
          | .ofNat shift => (Nat.shiftLeft x.significand shift, y.significand)
          | .negSucc shift => (x.significand, Nat.shiftLeft y.significand (shift + 1))).1
          (match x.exponent - y.exponent with
          | .ofNat shift => (Nat.shiftLeft x.significand shift, y.significand)
          | .negSucc shift => (x.significand, Nat.shiftLeft y.significand (shift + 1))).2 := by
    unfold divFinite?
    rw [hleft, hright]
    simp [hy]
    rfl
  rw [hrun]
  unfold divValue
  rw [if_neg (by simpa using hy)]
  cases hdiff : x.exponent - y.exponent with
  | ofNat shift =>
      exact map_roundRat_eq_some_quantizedRatValue fmt policy entropy
        (Bool.xor x.negative y.negative) (Nat.shiftLeft x.significand shift) y.significand hy
  | negSucc shift =>
      have hden : Nat.shiftLeft y.significand (shift + 1) ≠ 0 := by
        simpa [Nat.shiftLeft_eq] using
          Nat.mul_ne_zero hy (pow_ne_zero (shift + 1) (by decide : (2 : Nat) ≠ 0))
      exact map_roundRat_eq_some_quantizedRatValue fmt policy entropy
        (Bool.xor x.negative y.negative) x.significand
          (Nat.shiftLeft y.significand (shift + 1)) hden

/-- Finite casts decode exactly and quantize once into the destination format. -/
theorem castFinite_refines (src dst : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat) :
    Operation.Checked1 (exactNumericalSystem src) (exactNumericalSystem dst)
      (Policy.castFinite? src dst policy entropy)
      (quantizedValue dst policy entropy) := by
  intro code value hvalue
  unfold Policy.castFinite?
  rw [toDyadic?_eq_some_of_exactRepresents hvalue]
  rfl

end FloatLib.Floats.Formats.BinaryInterchange.Model
