/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Proof
import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Order

/-!
# Binary-interchange conversion proofs

Every configured and static-byte carrier adapter shares these conversion equations and numerical
contract. For default IEEE finite rounding, the nearest-value clause follows from the real rounding
bridge and the generic nearest-point theorem.
Complete outcome equality retains all word, status, and policy guarantees.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.Binary
namespace Conversion

universe u

/-- The context changes only a possible zero sign, never the exact rational sum. -/
@[simp, grind =] theorem value_addExact (context : Context) (left right : SignedRat) :
    (addExact context left right).value = left.value + right.value :=
  rfl

/-- The context changes only a possible zero sign, never the exact rational difference. -/
@[simp, grind =] theorem value_subExact (context : Context) (left right : SignedRat) :
    (subExact context left right).value = left.value - right.value := by
  simp [subExact, sub_eq_add_neg]

/-- The default context uses the ordinary nearest-even sign rule of `SignedRat`. -/
@[simp, grind =] theorem addExact_default (left right : SignedRat) :
    addExact Context.default left right = left + right :=
  rfl

/-- Default-context subtraction retains the ordinary `SignedRat` semantics. -/
@[simp, grind =] theorem subExact_default (left right : SignedRat) :
    subExact Context.default left right = left - right :=
  rfl

/-- Downward exact cancellation uses the disjunction of the operand signs. -/
theorem negative_addExact_downward_of_eq_zero {left right : SignedRat}
    (hsum : left.value + right.value = 0) :
    (addExact (Context.withRounding .towardNegative) left right).negative =
      (left.negative || right.negative) :=
  SignedRat.negative_addWithCancellationSign_of_eq_zero true hsum

/-- Finite observations use the exact rational binary quantizer. -/
@[simp, grind =] theorem runWith_finite {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (context : Context) (exact : SignedRat) :
    runWith pack context (.finite exact) =
      quantizeFiniteWith pack context exact :=
  rfl

/-- Infinity observations are governed only by the explicit infinity policy. -/
@[simp, grind =] theorem runWith_infinity {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (context : Context) (negative : Bool) :
    runWith pack context (.infinity negative) =
      quantizeInfinityWith pack context negative :=
  rfl

/-- Exceptional observations are governed only by the explicit exceptional policy. -/
@[simp, grind =] theorem runWith_exceptional
    {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (context : Context)
    (exceptional : ExceptionalValue) :
    runWith pack context (.exceptional exceptional) =
      quantizeExceptionalWith pack context exceptional :=
  rfl

private theorem finite_denotation {format : FloatFormat} (rounded : Model format) (value : Rat)
    (h : Model.toRat? rounded = some value) :
    Model.isFinite rounded = true ∧ Model.toReal rounded = (value : ℝ) := by
  cases hd : Model.toDyadic? rounded with
  | none => simp [Model.toRat?, hd] at h
  | some d =>
      have hvalue : d.toRat = value := by simpa [Model.toRat?, hd] using h
      refine ⟨Model.isFinite_eq_true_of_toDyadic?_some hd, ?_⟩
      rw [Model.toReal_eq, hd, ← hvalue, Numerics.Dyadic.cast_toRat]

private theorem signedRat_toReal (exact : SignedRat) (hvalue : exact.value ≠ 0) :
    Model.signedScaledRatToReal exact.negative exact.value.num.natAbs exact.value.den 0 =
      (exact.value : ℝ) := by
  have hmagnitude :
      (exact.value.num.natAbs : ℝ) / exact.value.den = |(exact.value : ℝ)| := by
    simp [Rat.cast_def, abs_div]
  simp only [Model.signedScaledRatToReal, Model.scaledRatToReal, Model.bpow_zero, mul_one,
    hmagnitude, exact.negative_eq_of_ne_zero hvalue]
  by_cases hnegative : exact.value < 0
  · have hnegativeReal : (exact.value : ℝ) < 0 := by exact_mod_cast hnegative
    simp [hnegative, abs_of_neg hnegativeReal]
  · have hnonnegativeReal : 0 ≤ (exact.value : ℝ) := by
      exact_mod_cast le_of_not_gt hnegative
    simp [hnegative, abs_of_nonneg hnonnegativeReal]

/--
The canonical IEEE rational rounder selects a nearest finite value whenever its result is finite.

This includes signed zero. The independent real grid has no infinity, so nonfinite results are
covered by the complete outcome clause of `specWith`.
-/
theorem nearestFinite_roundRat (format : FloatFormat) (hformat : format.isIEEE = true)
    (exact : SignedRat) :
    NearestFinite exact.value
      (Model.roundRat format exact.negative exact.value.num.natAbs exact.value.den) := by
  intro value hvalue candidate candidateValue hcandidate
  obtain ⟨hfinite, hreal⟩ := finite_denotation _ _ hvalue
  obtain ⟨hcandidateFinite, hcandidateReal⟩ := finite_denotation _ _ hcandidate
  have hround :
      Model.toReal
          (Model.roundRat format exact.negative exact.value.num.natAbs exact.value.den) =
        Model.roundAt format (exact.value : ℝ) := by
    by_cases hzero : exact.value = 0
    · simp [hzero]
    · have hnumerator : exact.value.num.natAbs ≠ 0 := by
        simpa using hzero
      rw [Model.roundRat, Model.toReal_roundRatScaled_eq_roundAt
        format exact.negative exact.value.num.natAbs exact.value.den 0
        hformat hnumerator exact.value.den_nz hfinite, signedRat_toReal exact hzero]
  have hnearest :=
    (Formats.Flocq.round_nearestEven_point (β := binaryRadix) (fexp := Model.fexpOf format)
      (exact.value : ℝ)).2 (Model.toReal candidate)
        (Model.toReal_genericFormat_of_isFinite candidate hcandidateFinite)
  change |Model.roundAt format (exact.value : ℝ) - exact.value| ≤
    |Model.toReal candidate - exact.value| at hnearest
  rw [← hround, hreal, hcandidateReal] at hnearest
  exact_mod_cast hnearest

/-- Descriptor rounding semantics establish the nearest clause for every carrier adapter. -/
theorem implements_runWith {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) :
    Quantization.Spec.Implements (specWith pack) (runWith pack) := by
  intro context input
  refine ⟨rfl, ?_⟩
  cases input with
  | finite exact =>
      intro hpolicy hformat
      refine ⟨Model.roundRat format exact.negative exact.value.num.natAbs exact.value.den,
        ?_, nearestFinite_roundRat format hformat exact⟩
      simp only [runWith, quantizeFiniteWith, hpolicy,
        Model.Policy.roundRat_nearestEven_eq_execFloat _ _ _ _ _ exact.value.den_nz]
  | infinity negative => trivial
  | exceptional exceptional => trivial

/-- The additional semantic clause preserves exactly the original complete conversion outcomes. -/
theorem specWith_iff_eq_runWith {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (context : Context) (input : NumericalValue SignedRat)
    (outcome : FloatLib.Floats.ExecFloat.ConversionOutcome Destination) :
    specWith pack context input outcome ↔ outcome = runWith pack context input := by
  constructor
  · exact And.left
  · rintro rfl
    exact implements_runWith pack context input

/-- Rejecting infinity produces the corresponding explicit failure for every carrier. -/
@[grind =] theorem runWith_infinity_reject
    {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (negative : Bool) :
    runWith pack ({ infinity := .reject } : Context) (.infinity negative) =
      .failure (.infinity .source negative) :=
  rfl

/-- Rejecting an exceptional observation preserves its complete common classification. -/
@[grind =] theorem runWith_exceptional_reject
    {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (exceptional : ExceptionalValue) :
    runWith pack ({ exceptional := .reject } : Context) (.exceptional exceptional) =
      .failure (.exceptional .source exceptional) :=
  rfl

/--
Default conversion of an observed binary NaN agrees with `Model.castWithStatus` in value and in
the invalid flag, for every rounding mode and for equal or unequal descriptors.

The sign and signaling class travel with the observation, and the destination NaN is
`Model.propagatedNaN` on the IEEE payload, as IEEE 754-2019 §6.2.3 and §7.2 require. A destination
with no NaN encoding is excluded here and covered by `runWith_default_nan_of_encoding_finite`:
conversion then fails, while `Model.castWithStatus` returns positive zero and raises invalid.
-/
theorem runWith_default_nan_eq_castWithStatus {src dst : FloatFormat} {Destination : Type u}
    (pack : Model dst → Destination) (x : Model src) (mode : Model.IEEERoundingMode)
    (hnan : Model.isNaN x = true) (hdst : dst.encoding ≠ .finite) :
    runWith pack Context.default
        (.exceptional (.nan (some (Model.fracField x)) (Model.signBit x) (Model.isSNaN x))) =
      .success (pack (Model.castWithStatus src dst x mode).value)
        { invalid := (Model.castWithStatus src dst x mode).status.invalid } := by
  have hcast := Model.castWithRounding_of_isNaN (dst := dst) x mode hnan
  have hisnan := Model.isNaN_propagatedNaN dst (Model.signBit x)
    (Model.payloadOfNaNField (Model.isSNaN x) (Model.fracField x)) hdst
  have hsome : ∃ v, Model.canonicalNaN? dst = some v := by
    unfold Model.canonicalNaN?; cases h : dst.encoding <;> simp_all
  obtain ⟨v, hv⟩ := hsome
  simp only [runWith, quantizeExceptionalWith, Context.default, hv, Model.castWithStatus, hnan,
    hcast, hisnan, Model.outcomeWithInvalid, Option.getD_some]
  cases Model.isSNaN x <;> rfl

/--
Default conversion of an observed binary NaN into a destination with no NaN encoding fails with
the source NaN as the reported exceptional value, and `Model.castWithStatus` on the same source
raises invalid.

The two paths agree that the conversion is invalid. `ExecFloat` reports it as an explicit failure;
the descriptor model delivers positive zero and sets the invalid flag.
-/
theorem runWith_default_nan_of_encoding_finite {src dst : FloatFormat} {Destination : Type u}
    (pack : Model dst → Destination) (x : Model src) (mode : Model.IEEERoundingMode)
    (hnan : Model.isNaN x = true) (hdst : dst.encoding = .finite) :
    runWith pack Context.default
        (.exceptional (.nan (some (Model.fracField x)) (Model.signBit x) (Model.isSNaN x))) =
      .failure (.exceptional .source
        (.nan (some (Model.fracField x)) (Model.signBit x) (Model.isSNaN x))) ∧
      (Model.castWithStatus src dst x mode).status.invalid = true := by
  refine ⟨?_, Model.castWithStatus_invalid_of_isNaN_of_encoding_finite x mode hnan hdst⟩
  have hv : Model.canonicalNaN? dst = none := by simp [Model.canonicalNaN?, hdst]
  simp only [runWith, quantizeExceptionalWith, Context.default, hv]

end Conversion
end ExecFloat.Binary
end FloatLib.Floats
