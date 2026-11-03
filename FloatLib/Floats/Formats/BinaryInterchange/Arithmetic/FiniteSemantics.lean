/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactNumericalSystem
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core
public import
  FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable
public import FloatLib.Numerics.Operation.Semantics

/-!
# Correctness of finite arithmetic

The arithmetic layer decodes represented inputs to exact dyadics, performs one exact operation,
and quantizes once under the selected output policy. These theorems expose that contract through
the family-independent `NumericalSystem` and `Operation` interfaces.

Subtraction needs one format-specific convention. IEEE, OCP E4M3, FP4, and FP6 retain signed zero,
so negation toggles the sign of zero. FNUZ has only one zero encoding, so its exact semantic
negation canonicalizes zero to positive zero.

The exact sums of addition, subtraction and fused multiply-add are `Policy.addDyadic`, whose zero
has the sign of IEEE 754-2019 Section 6.3 for the policy's rounding rule. The cancellation
theorems (`addFinite?_eq_zero_of_toRat_add_eq_zero` and its multiply-add forms) state that signed
zero at the encoding level. Division rounds a numerator and denominator whose signed quotient is
the exact rational quotient (`divValue_eq_quantizedRatValue`). For nearest-even rounding in an
IEEE format a finite quotient is the correctly rounded real quotient
(`toReal_divFinite?_nearest`), and a zero dividend gives the zero signed by the exclusive or of
the operand signs under every policy (`divFinite?_eq_zero_of_toRat_eq_zero`).
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
      rw [dite_eq_right hden] at hround
      split at hround <;> simp at hround
  | some result =>
      unfold quantizedRatValue
      rw [hround]
      change some ((exactNumericalSystem fmt).denote result) =
        some ((exactNumericalSystem fmt).denote result)
      rfl

/--
Denotation of the quantized exact quotient.

The sign is the exclusive or of the operand signs and the exponent difference is shifted into the
numerator or the denominator; `divValue_eq_quantizedRatValue` proves that these denote the exact
quotient. `divFinite_refines` uses this value only for a nonzero divisor. For a zero divisor it is
the placeholder `undefined`, which no theorem relates to IEEE division by zero.
-/
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

/-- The numerator and denominator that `divFinite?` and `divValue` round. -/
private def divOperands (left right : Numerics.Dyadic) : Nat × Nat :=
  match left.exponent - right.exponent with
  | .ofNat shift => (Nat.shiftLeft left.significand shift, right.significand)
  | .negSucc shift => (left.significand, Nat.shiftLeft right.significand (shift + 1))

/-- A nonzero divisor gives a nonzero denominator, and the signed quotient is the exact one. -/
private theorem divOperands_spec (left right : Numerics.Dyadic) (hright : right.significand ≠ 0) :
    (divOperands left right).2 ≠ 0 ∧
      signedScaledRatToReal (Bool.xor left.negative right.negative)
          (divOperands left right).1 (divOperands left right).2 0 =
        left.toReal / right.toReal := by
  rw [← signedScaledRatToReal_eq_div_toReal]
  unfold divOperands
  cases hdiff : left.exponent - right.exponent with
  | ofNat shift =>
      refine ⟨hright, ?_⟩
      simp only [signedScaledRatToReal, scaledRatToReal, bpow_zero, mul_one,
        div_mul_bpow_ofNat]
  | negSucc shift =>
      refine ⟨?_, ?_⟩
      · simpa [Nat.shiftLeft_eq] using
          Nat.mul_ne_zero hright (pow_ne_zero (shift + 1) (by decide : (2 : Nat) ≠ 0))
      · simp only [signedScaledRatToReal, scaledRatToReal, bpow_zero, mul_one,
          div_mul_bpow_negSucc]

private theorem divValue_eq_divOperands (fmt : FloatFormat) (policy : QuantizationPolicy)
    (entropy : Nat) (left right : Numerics.Dyadic) (hright : right.significand ≠ 0) :
    divValue fmt policy entropy left right =
      quantizedRatValue fmt policy entropy (Bool.xor left.negative right.negative)
        (divOperands left right).1 (divOperands left right).2 := by
  unfold divValue divOperands
  simp only [beq_iff_eq, hright, ↓reduceIte]

/--
For a nonzero divisor, `divValue` quantizes the exact quotient: it rounds the exclusive or of the
operand signs with a natural numerator and a nonzero denominator whose signed quotient is
`left.toReal / right.toReal`.
-/
theorem divValue_eq_quantizedRatValue (fmt : FloatFormat) (policy : QuantizationPolicy)
    (entropy : Nat) (left right : Numerics.Dyadic) (hright : right.significand ≠ 0) :
    ∃ numerator denominator : Nat, denominator ≠ 0 ∧
      signedScaledRatToReal (Bool.xor left.negative right.negative) numerator denominator 0 =
        left.toReal / right.toReal ∧
      divValue fmt policy entropy left right =
        quantizedRatValue fmt policy entropy (Bool.xor left.negative right.negative)
          numerator denominator :=
  ⟨_, _, (divOperands_spec left right hright).1, (divOperands_spec left right hright).2,
    divValue_eq_divOperands fmt policy entropy left right hright⟩

/-- Negation refines format-aware exact dyadic negation on every represented finite input. -/
theorem negExact_refines (fmt : FloatFormat) :
    Operation.Finite1 (exactNumericalSystem fmt) (exactNumericalSystem fmt)
      Model.neg (Model.negDyadic fmt) := by
  intro code value hvalue
  apply exactRepresents_of_toDyadic?_eq_some
  exact Model.toDyadic?_neg_of_toDyadic?_some code
    (toDyadic?_eq_some_of_exactRepresents hvalue)

/--
Finite addition performs exact dyadic addition followed by one quantization. The exact sum is
`Policy.addDyadic`, which signs an exactly cancelling sum by the policy's rounding rule.
-/
theorem addFinite_refines (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat) :
    Operation.Checked2 (exactNumericalSystem fmt) (exactNumericalSystem fmt)
      (exactNumericalSystem fmt) (addFinite? fmt policy entropy)
      (fun left right => quantizedValue fmt policy entropy
        (Policy.addDyadic policy.rounding left right)) := by
  intro left right x y hx hy
  unfold addFinite?
  rw [toDyadic?_eq_some_of_exactRepresents hx, toDyadic?_eq_some_of_exactRepresents hy]
  rfl

/-- Finite subtraction performs exact format-aware negation and addition, then quantizes once. -/
theorem subFinite_refines (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat) :
    Operation.Checked2 (exactNumericalSystem fmt) (exactNumericalSystem fmt)
      (exactNumericalSystem fmt) (subFinite? fmt policy entropy)
      (fun left right => quantizedValue fmt policy entropy
        (Policy.addDyadic policy.rounding left (Model.negDyadic fmt right))) := by
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

/-- Mixed-format multiply-add decodes storage operands and quantizes once into the accumulator. -/
theorem mulAddFinite_refines (storage accumulator : FloatFormat)
    (policy : QuantizationPolicy) (entropy : Nat) :
    Operation.Checked3 (exactNumericalSystem storage) (exactNumericalSystem storage)
      (exactNumericalSystem accumulator) (exactNumericalSystem accumulator)
      (mulAddFinite? storage accumulator policy entropy)
      (fun x y acc => quantizedValue accumulator policy entropy
        (Policy.addDyadic policy.rounding (mulDyadic x y) acc)) := by
  intro a b c x y z hx hy hz
  unfold mulAddFinite?
  rw [toDyadic?_eq_some_of_exactRepresents hx, toDyadic?_eq_some_of_exactRepresents hy,
    toDyadic?_eq_some_of_exactRepresents hz]
  rfl

/--
Finite fused multiply-add has one quantization after the exact product and sum. An exactly zero
result is signed from the product sign and the addend sign, as in `addFinite_refines`. It is
mixed-format multiply-add with all three operands and the result in `fmt`.
-/
theorem fmaFinite_refines (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat) :
    Operation.Checked3 (exactNumericalSystem fmt) (exactNumericalSystem fmt)
      (exactNumericalSystem fmt) (exactNumericalSystem fmt) (fmaFinite? fmt policy entropy)
      (fun x y z => quantizedValue fmt policy entropy
        (Policy.addDyadic policy.rounding (mulDyadic x y) z)) :=
  mulAddFinite_refines fmt fmt policy entropy

/-- Finite division with a nonzero divisor rounds `divOperands` with the product sign. -/
private theorem divFinite?_eq_roundRat {fmt : FloatFormat} {policy : QuantizationPolicy}
    {entropy : Nat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hx : Model.toDyadic? x = some dx) (hy : Model.toDyadic? y = some dy)
    (hdy : dy.significand ≠ 0) :
    divFinite? fmt policy entropy x y =
      Policy.roundRat fmt policy entropy (Bool.xor dx.negative dy.negative)
        (divOperands dx dy).1 (divOperands dx dy).2 := by
  unfold divFinite? divOperands
  rw [hx, hy]
  simp only [Option.bind_eq_bind, Option.bind_some, beq_iff_eq, hdy, ↓reduceIte]
  split <;> rename_i hdiff <;> simp only [hdiff]

/--
Finite division refines exact rational division whenever the divisor is nonzero:
`divValue_eq_quantizedRatValue` shows that `divValue` quantizes the exact quotient.
-/
theorem divFinite_refines (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat) :
    Operation.Checked2On (exactNumericalSystem fmt) (exactNumericalSystem fmt)
      (exactNumericalSystem fmt) (divFinite? fmt policy entropy)
      (divValue fmt policy entropy) (fun _ right => right.significand ≠ 0) := by
  intro left right x y hy hx hyrep
  change Numerics.Dyadic at x y
  rw [divFinite?_eq_roundRat (toDyadic?_eq_some_of_exactRepresents hx)
      (toDyadic?_eq_some_of_exactRepresents hyrep) hy,
    divValue_eq_divOperands fmt policy entropy x y hy]
  exact map_roundRat_eq_some_quantizedRatValue fmt policy entropy _ _ _
    (divOperands_spec x y hy).1

/-- Every policy rounds a zero numerator to the format's zero of the requested sign. -/
theorem Policy.roundRat_num_zero (fmt : FloatFormat) (policy : QuantizationPolicy)
    (entropy : Nat) (sign : Bool) (den : Nat) (hden : den ≠ 0) :
    Policy.roundRat fmt policy entropy sign 0 den = some (Model.zero fmt sign) := by
  unfold Policy.roundRat
  simp only [hden, ↓reduceDIte]
  split
  · rw [Model.roundRat_num_zero fmt sign den hden]
  · have hzero : Model.isSubnormal (Model.zero fmt sign) = false := by
      unfold Model.zero
      split <;> simp [Model.isSubnormal]
    rcases policy with ⟨rounding, overflow, underflow⟩
    cases underflow <;>
      simp [Policy.roundRatGeneralOfDenNeZero, Policy.applyUnderflow, hzero]

/--
A zero dividend over a nonzero finite divisor gives the zero signed by the exclusive or of the two
stored signs, under every policy, as IEEE 754-2019 Section 6.3 signs a quotient. A format without a
signed zero returns its one zero.
-/
theorem divFinite?_eq_zero_of_toRat_eq_zero (fmt : FloatFormat) (policy : QuantizationPolicy)
    (entropy : Nat) {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hx : Model.toDyadic? x = some dx) (hy : Model.toDyadic? y = some dy)
    (hdx : dx.toRat = 0) (hdy : dy.toRat ≠ 0) :
    divFinite? fmt policy entropy x y =
      some (Model.zero fmt (Bool.xor (signBit x) (signBit y))) := by
  have hdx' : dx.significand = 0 := (Numerics.Dyadic.toRat_eq_zero_iff dx).mp hdx
  have hdy' : dy.significand ≠ 0 := fun h => hdy ((Numerics.Dyadic.toRat_eq_zero_iff dy).mpr h)
  have hnum : (divOperands dx dy).1 = 0 := by
    unfold divOperands
    split <;> simp [hdx']
  rw [divFinite?_eq_roundRat hx hy hdy', hnum, ← sign_eq_signBit_of_toDyadic?_some hx,
    ← sign_eq_signBit_of_toDyadic?_some hy]
  exact Policy.roundRat_num_zero fmt policy entropy _ _ (divOperands_spec dx dy hdy').1

/--
Nearest-even finite division in an IEEE format is the correctly rounded real quotient: a finite
result of `divFinite?` is `roundAt fmt (toReal x / toReal y)`. A successful division already has
finite operands and a nonzero divisor.
-/
theorem toReal_divFinite?_nearest {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (entropy : Nat)
    {x y result : Model fmt}
    (hresult : divFinite? fmt QuantizationPolicy.nearest entropy x y = some result)
    (hfinite : isFinite result = true) :
    toReal result = roundAt fmt (toReal x / toReal y) := by
  cases hx : Model.toDyadic? x with
  | none => simp [divFinite?, hx] at hresult
  | some dx =>
      cases hy : Model.toDyadic? y with
      | none => simp [divFinite?, hx, hy] at hresult
      | some dy =>
          by_cases hdy : dy.significand = 0
          · simp [divFinite?, hx, hy, hdy] at hresult
          · obtain ⟨hden, hquotient⟩ := divOperands_spec dx dy hdy
            rw [divFinite?_eq_roundRat hx hy hdy,
              Policy.roundRat_nearest_eq_execFloat fmt entropy _ _ _ hden] at hresult
            obtain rfl := Option.some.inj hresult
            rw [Model.roundRat] at hfinite ⊢
            rw [toReal_roundRatScaled_eq_roundAt fmt _ _ _ 0 hfmt hfinite, hquotient]
            simp [toReal_eq, hx, hy]

/-! ## Signed zero of an exactly cancelling sum -/

private theorem roundDyadic_addDyadic_of_toRat_add_eq_zero (fmt : FloatFormat)
    (policy : QuantizationPolicy) (entropy : Nat) (left right : Numerics.Dyadic)
    (hsum : left.toRat + right.toRat = 0) :
    Policy.roundDyadic fmt policy entropy (Policy.addDyadic policy.rounding left right) =
      Model.zero fmt (Policy.zeroSumSign policy.rounding left.negative right.negative) := by
  have hzero : (Model.addDyadic left right).significand = 0 := by
    rw [← Numerics.Dyadic.toRat_eq_zero_iff, Model.addDyadic, Numerics.Dyadic.add_toRat, hsum]
  unfold Policy.addDyadic
  simp only [hzero, beq_self_eq_true, ↓reduceIte]
  exact Policy.roundDyadic_significand_zero fmt policy entropy _ _

/--
Exact cancellation in finite addition (IEEE 754-2019 Section 6.3). When two finite values have an
exact sum of zero, `addFinite?` returns the format's zero with the sign `Policy.zeroSumSign` gives
the policy's rounding rule and the two stored signs, whatever the overflow and underflow choices.
Toward negative infinity `+1 + (-1)` is `-0`; under every other rule it is `+0`, and two zeros of
one sign keep that sign. A format without a signed zero returns its one zero.
-/
theorem addFinite?_eq_zero_of_toRat_add_eq_zero (fmt : FloatFormat)
    (policy : QuantizationPolicy) (entropy : Nat) {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hx : Model.toDyadic? x = some dx) (hy : Model.toDyadic? y = some dy)
    (hsum : dx.toRat + dy.toRat = 0) :
    addFinite? fmt policy entropy x y =
      some (Model.zero fmt (Policy.zeroSumSign policy.rounding (signBit x) (signBit y))) := by
  unfold addFinite?
  rw [hx, hy, ← sign_eq_signBit_of_toDyadic?_some hx, ← sign_eq_signBit_of_toDyadic?_some hy]
  exact congrArg some (roundDyadic_addDyadic_of_toRat_add_eq_zero fmt policy entropy dx dy hsum)

/--
Exact cancellation in mixed-format multiply-add. When `x * y + acc` is exactly zero for finite
operands, `mulAddFinite?` returns the accumulator format's zero that
`addFinite?_eq_zero_of_toRat_add_eq_zero` gives a sum whose summands have the signs of the exact
product, `Bool.xor (signBit x) (signBit y)`, and of `acc`.
-/
theorem mulAddFinite?_eq_zero_of_toRat_add_eq_zero (storage accumulator : FloatFormat)
    (policy : QuantizationPolicy) (entropy : Nat) {x y : Model storage} {acc : Model accumulator}
    {dx dy da : Numerics.Dyadic} (hx : Model.toDyadic? x = some dx)
    (hy : Model.toDyadic? y = some dy) (hacc : Model.toDyadic? acc = some da)
    (hsum : dx.toRat * dy.toRat + da.toRat = 0) :
    mulAddFinite? storage accumulator policy entropy x y acc =
      some (Model.zero accumulator (Policy.zeroSumSign policy.rounding
        (Bool.xor (signBit x) (signBit y)) (signBit acc))) := by
  have hproduct : (mulDyadic dx dy).toRat = dx.toRat * dy.toRat := Numerics.Dyadic.mul_toRat dx dy
  unfold mulAddFinite?
  rw [hx, hy, hacc, ← sign_eq_signBit_of_toDyadic?_some hx,
    ← sign_eq_signBit_of_toDyadic?_some hy, ← sign_eq_signBit_of_toDyadic?_some hacc]
  exact congrArg some (roundDyadic_addDyadic_of_toRat_add_eq_zero accumulator policy entropy
    (mulDyadic dx dy) da (by rw [hproduct, hsum]))

/--
Exact cancellation in fused multiply-add: `mulAddFinite?_eq_zero_of_toRat_add_eq_zero` with the
storage and accumulator formats both `fmt`. When `x * y + z` is exactly zero for finite operands,
the result is the zero whose sign `Policy.zeroSumSign` gives from the policy's rounding rule, the
product sign `Bool.xor (signBit x) (signBit y)` and the sign of `z`.
-/
theorem fmaFinite?_eq_zero_of_toRat_add_eq_zero (fmt : FloatFormat)
    (policy : QuantizationPolicy) (entropy : Nat) {x y z : Model fmt}
    {dx dy dz : Numerics.Dyadic} (hx : Model.toDyadic? x = some dx)
    (hy : Model.toDyadic? y = some dy) (hz : Model.toDyadic? z = some dz)
    (hsum : dx.toRat * dy.toRat + dz.toRat = 0) :
    fmaFinite? fmt policy entropy x y z =
      some (Model.zero fmt (Policy.zeroSumSign policy.rounding
        (Bool.xor (signBit x) (signBit y)) (signBit z))) :=
  mulAddFinite?_eq_zero_of_toRat_add_eq_zero fmt fmt policy entropy hx hy hz hsum

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
