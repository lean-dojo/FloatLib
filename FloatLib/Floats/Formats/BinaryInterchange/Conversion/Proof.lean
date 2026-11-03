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
public import FloatLib.Floats.ExecFloat.Conversion.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Classification.Predicates
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.NearestAwayAgreement

/-!
# Binary-interchange conversion proofs

Every configured and static-byte carrier adapter shares these conversion equations and numerical
contract. For default IEEE finite rounding, the nearest-value clause follows from the real rounding
bridge and the generic nearest-point theorem. Complete outcome equality keeps all word, status,
and policy guarantees.

For a rounding mode with an `IEEERoundingMode` direction,
`finiteStatus_of_ieeeRoundingMode?_eq_some` gives the conversion status from that direction's exact
classifiers. For nearest-away rounding, `finiteStatus_of_nearestAway` names them:
`rationalNearestAwayOverflowsScaled` and `rationalIsTinyAfterRoundingScaled` with the nearest-even
tininess boundary.

The significand-based calculation `roundedSignificandStatus` serves stochastic rounding. For
nearest-away rounding, `roundedSignificandStatus_nearestAway` shows that it matches the
nearest-away overflow classifier
and the comparison with `underflowMidpoint`. The tininess classifier also counts a tiny delivered
value, so `finiteStatus_eq_roundedSignificandStatus_of_nearestAway` adds the engine's result: for
the value that `Model.Policy.roundRat` delivers, the two calculations give the same status under
every overflow and underflow policy.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.Binary
namespace Conversion

universe u

/--
A binary model decodes to its exact denotation in `SignedRat`, the decoding the configured and
static-byte carriers apply to their stored model.
-/
@[simp, grind =] theorem modelDecoder_run {format : FloatFormat} (value : Model format) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value =
      ((Model.exactNumericalSystem format).denote value).map SignedRat.ofDyadic :=
  rfl

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

/-- Default-context subtraction is ordinary `SignedRat` subtraction. -/
@[simp, grind =] theorem subExact_default (left right : SignedRat) :
    subExact Context.default left right = left - right :=
  rfl

/-- The context of a policy and a direction rounds in that direction. -/
@[simp, grind =] theorem Policy.rounding_withRounding (policy : Policy) (mode : RoundingMode) :
    (policy.withRounding mode).quantization.rounding = mode :=
  rfl

/-- The context of a policy and a direction has the policy's overflow rule. -/
@[simp, grind =] theorem Policy.overflow_withRounding (policy : Policy) (mode : RoundingMode) :
    (policy.withRounding mode).quantization.overflow = policy.overflow :=
  rfl

/-- The context of a policy and a direction has the policy's underflow rule. -/
@[simp, grind =] theorem Policy.underflow_withRounding (policy : Policy) (mode : RoundingMode) :
    (policy.withRounding mode).quantization.underflow = policy.underflow :=
  rfl

/-- The context of a policy and a direction has the policy's stochastic entropy. -/
@[simp, grind =] theorem Policy.entropy_withRounding (policy : Policy) (mode : RoundingMode) :
    (policy.withRounding mode).entropy = policy.entropy :=
  rfl

/-- The context of a policy and a direction has the policy's infinity policy. -/
@[simp, grind =] theorem Policy.infinity_withRounding (policy : Policy) (mode : RoundingMode) :
    (policy.withRounding mode).infinity = policy.infinity :=
  rfl

/-- The context of a policy and a direction has the policy's exceptional-value policy. -/
@[simp, grind =] theorem Policy.exceptional_withRounding (policy : Policy)
    (mode : RoundingMode) :
    (policy.withRounding mode).exceptional = policy.exceptional :=
  rfl

/--
The canonical policy rounding to nearest is the canonical context, so a conversion that names
neither `mode` nor `context` runs in `Context.default`.
-/
@[simp, grind =] theorem Policy.default_withRounding_nearest :
    Policy.default.withRounding .nearest = Context.default :=
  rfl

/-- Downward exact cancellation uses the disjunction of the operand signs, under every policy. -/
theorem negative_addExact_downward_of_eq_zero (policy : Policy) {left right : SignedRat}
    (hsum : left.value + right.value = 0) :
    (addExact (policy.withRounding .down) left right).negative =
      (left.negative || right.negative) :=
  SignedRat.negative_addWithCancellationSign_of_eq_zero true hsum

/-- Finite observations use the exact rational binary quantizer. -/
@[simp, grind =] theorem runWith_finite {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (context : Context) (exact : SignedRat) :
    runWith pack context (.finite exact) =
      quantizeFiniteWith pack context exact :=
  rfl

/-- Infinity observations are governed by the infinity policy alone. -/
@[simp, grind =] theorem runWith_infinity {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (context : Context) (negative : Bool) :
    runWith pack context (.infinity negative) =
      quantizeInfinityWith pack context negative :=
  rfl

/-- Exceptional observations are governed by the exceptional policy alone. -/
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

private theorem natAbs_div_den_eq_abs (value : Rat) :
    (value.num.natAbs : ℝ) / value.den = |(value : ℝ)| := by
  simp [Rat.cast_def, abs_div]

private theorem signedRat_toReal (exact : SignedRat) (hvalue : exact.value ≠ 0) :
    Model.signedScaledRatToReal exact.negative exact.value.num.natAbs exact.value.den 0 =
      (exact.value : ℝ) := by
  simp only [Model.signedScaledRatToReal, Model.scaledRatToReal, Model.bpow_zero, mul_one,
    natAbs_div_den_eq_abs, exact.negative_eq_of_ne_zero hvalue]
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
theorem nearestFinite_roundRat (format : FloatFormat) (exact : SignedRat)
    (hformat : format.isIEEE = true := by ieee_format) :
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
    · rw [Model.roundRat, Model.toReal_roundRatScaled_eq_roundAt
        format exact.negative exact.value.num.natAbs exact.value.den 0
        hformat hfinite, signedRat_toReal exact hzero]
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
        ?_, nearestFinite_roundRat format exact⟩
      simp only [runWith, quantizeFiniteWith, hpolicy,
        Model.Policy.roundRat_nearest_eq_execFloat _ _ _ _ _ exact.value.den_nz]
  | infinity negative => trivial
  | exceptional exceptional => trivial

/--
Default IEEE conversion of an exact value whose magnitude is at most the largest finite value
delivers a finite nearest value, so the nearest clause of `specWith` is not vacuous there.

Above that magnitude the result may be the largest finite value or an infinity; this theorem does
not say where the boundary lies.
-/
theorem runWith_nearest_of_abs_le_posMaxFinite {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (context : Context) (exact : SignedRat)
    (hpolicy : context.quantization = QuantizationPolicy.nearest)
    (hbound : |(exact.value : ℝ)| ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    ∃ rounded : Model format, Model.isFinite rounded = true ∧
      NearestFinite exact.value rounded ∧
        runWith pack context (.finite exact) =
          .success (pack rounded) (finiteStatus context exact.value rounded) := by
  refine ⟨Model.roundRat format exact.negative exact.value.num.natAbs exact.value.den,
    ?_, nearestFinite_roundRat format exact, ?_⟩
  · apply Model.isFinite_roundRatScaled_of_abs_le_posMaxFinite format _ _ _ 0 hformat
      exact.value.den_nz
    simpa only [Model.abs_signedScaledRatToReal, Model.scaledRatToReal, Model.bpow_zero, mul_one,
      natAbs_div_den_eq_abs] using hbound
  · simp only [runWith, quantizeFiniteWith, hpolicy,
      Model.Policy.roundRat_nearest_eq_execFloat _ _ _ _ _ exact.value.den_nz]

/-- An outcome satisfies `specWith` exactly when it is the outcome of `runWith`. -/
theorem specWith_iff_eq_runWith {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (context : Context) (input : NumericalValue SignedRat)
    (outcome : FloatLib.Floats.ExecFloat.ConversionOutcome Destination) :
    specWith pack context input outcome ↔ outcome = runWith pack context input := by
  constructor
  · exact And.left
  · rintro rfl
    exact implements_runWith pack context input

/-- Rejecting infinity fails with the source infinity and its sign, for every carrier. -/
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
Default conversion of an observed binary NaN agrees with `Model.cast` in value and in
the invalid flag, for every rounding mode and for equal or unequal descriptors.

The sign and signaling class travel with the observation, and the destination NaN is
`Model.propagatedNaN` on the IEEE payload, as IEEE 754-2019 §6.2.3 and §7.2 require. A destination
with no NaN encoding is excluded here and covered by `runWith_default_nan_of_encoding_finite`:
conversion then fails, while `Model.cast` returns positive zero and raises invalid.
-/
theorem runWith_default_nan_eq_cast_status {src dst : FloatFormat} {Destination : Type u}
    (pack : Model dst → Destination) (x : Model src) (mode : Model.IEEERoundingMode)
    (hnan : Model.isNaN x = true) (hdst : dst.encoding ≠ .finite) :
    runWith pack Context.default
        (.exceptional (.nan (some (Model.nanPayload x)) (Model.signBit x) (Model.isSNaN x))) =
      .success (pack (Model.cast src dst x mode (status := true)).value)
        { invalid := (Model.cast src dst x mode (status := true)).status.invalid } := by
  have hcast : Model.Internal.Directed.cast src dst x mode =
      Model.propagatedNaN dst (Model.signBit x) (Model.nanPayload x) := by
    rw [Model.Internal.Directed.cast_eq]
    exact Model.cast_of_isNaN (dst := dst) x hnan mode
  have hisnan := Model.isNaN_propagatedNaN dst (Model.signBit x)
    (Model.nanPayload x) hdst
  have hsome : ∃ v, Model.canonicalNaN? dst = some v := by
    unfold Model.canonicalNaN?; cases h : dst.encoding <;> simp_all
  obtain ⟨v, hv⟩ := hsome
  simp only [runWith, quantizeExceptionalWith, Context.default, hv, Model.cast,
    Model.Internal.Status.cast, hnan, hcast, hisnan, Model.outcomeWithInvalid, Option.getD_some]
  cases Model.isSNaN x <;> rfl

/--
Default conversion of an observed binary NaN into a destination with no NaN encoding fails with
the source NaN as the reported exceptional value, and `Model.cast` on the same source
raises invalid.

The two paths agree that the conversion is invalid. `ExecFloat` reports a failure, while the
descriptor model delivers positive zero and sets the invalid flag.
-/
theorem runWith_default_nan_of_encoding_finite {src dst : FloatFormat} {Destination : Type u}
    (pack : Model dst → Destination) (x : Model src) (mode : Model.IEEERoundingMode)
    (hnan : Model.isNaN x = true) (hdst : dst.encoding = .finite) :
    runWith pack Context.default
        (.exceptional (.nan (some (Model.nanPayload x)) (Model.signBit x) (Model.isSNaN x))) =
      .failure (.exceptional .source
        (.nan (some (Model.nanPayload x)) (Model.signBit x) (Model.isSNaN x))) ∧
      (Model.cast src dst x mode (status := true)).status.invalid = true := by
  refine ⟨?_, Model.cast_invalid_of_isNaN_of_encoding_finite x mode hnan hdst⟩
  have hv : Model.canonicalNaN? dst = none := by simp [Model.canonicalNaN?, hdst]
  simp only [runWith, quantizeExceptionalWith, Context.default, hv]

/-! ## Significand-based status of nearest-away rounding -/

/-- A natural quotient scaled by a binary power, as a real number. -/
private theorem scaleByPowerOfTwo_div_eq (numerator denominator : Nat) (exponent : Int) :
    ((RationalBinary.scaleByPowerOfTwo numerator denominator exponent).1 : ℝ) /
        ((RationalBinary.scaleByPowerOfTwo numerator denominator exponent).2 : ℝ) =
      (numerator : ℝ) / denominator * (2 : ℝ) ^ exponent := by
  rw [Model.scaleByPowerOfTwo_real]
  simp [Model.scaledRatToReal, Model.bpow, Formats.Flocq.bpow, binaryRadix, Radix.toReal]

/--
Nearest-away rounding of a scaled quotient exceeds a bound exactly when twice the scaled real
quotient reaches twice the bound plus one.
-/
private theorem lt_roundQuotient_nearestAway_scaled_iff (bound numerator denominator : Nat)
    (exponent : Int) (hdenominator : denominator ≠ 0) :
    bound < roundQuotient .nearestAway
        (RationalBinary.scaleByPowerOfTwo numerator denominator exponent).1
        (RationalBinary.scaleByPowerOfTwo numerator denominator exponent).2 ↔
      ((2 * bound + 1 : Nat) : ℝ) ≤ 2 * ((numerator : ℝ) / denominator * (2 : ℝ) ^ exponent) := by
  have hscaled :=
    RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator exponent hdenominator
  rw [lt_roundQuotient_nearestAway_iff _ _ _ hscaled, ← scaleByPowerOfTwo_div_eq]
  have hpositive :
      (0 : ℝ) < (RationalBinary.scaleByPowerOfTwo numerator denominator exponent).2 := by
    exact_mod_cast Nat.pos_of_ne_zero hscaled
  rw [mul_div_assoc', le_div_iff₀ hpositive]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- `floorLog2` brackets a positive quotient between consecutive real powers of two. -/
private theorem floorLog2_zpow_bounds (numerator denominator : Nat) (hnumerator : numerator ≠ 0)
    (hdenominator : denominator ≠ 0) :
    (2 : ℝ) ^ RationalBinary.floorLog2 numerator denominator ≤ (numerator : ℝ) / denominator ∧
      (numerator : ℝ) / denominator <
        (2 : ℝ) ^ (RationalBinary.floorLog2 numerator denominator + 1) := by
  have hbounds := Model.floorLog2_bounds numerator denominator hnumerator hdenominator
  simpa [Model.bpow, Formats.Flocq.bpow, binaryRadix, Radix.toReal] using hbounds

/--
Scaling by `2 ^ (f - E)` inverts twice the unit `2 ^ (E - f - 1)`, so a bound on twice the scaled
quotient is a bound on the quotient measured in that unit.
-/
private theorem le_two_mul_mul_zpow_iff (q bound : ℝ) (f : ℕ) (E : ℤ) :
    bound ≤ 2 * (q * (2 : ℝ) ^ ((f : ℤ) - E)) ↔ bound * (2 : ℝ) ^ (E - f - 1) ≤ q := by
  have hinverse : (2 : ℝ) ^ ((f : ℤ) - E) * (2 * (2 : ℝ) ^ (E - f - 1)) = 1 := by
    rw [← zpow_one_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
      show (f : ℤ) - E + (1 + (E - f - 1)) = 0 by ring]
    exact zpow_zero 2
  have hscaled : 2 * (q * (2 : ℝ) ^ ((f : ℤ) - E)) * (2 : ℝ) ^ (E - f - 1) = q := by
    calc
      _ = q * ((2 : ℝ) ^ ((f : ℤ) - E) * (2 * (2 : ℝ) ^ (E - f - 1))) := by ring
      _ = q := by rw [hinverse, mul_one]
  rw [← mul_le_mul_iff_left₀ (zpow_pos (by norm_num : (0 : ℝ) < 2) (E - f - 1)), hscaled]

/--
The general branch's nearest-away overflow test, on the significand rounded with an unbounded
exponent range, is reaching the top finite midpoint.
-/
private theorem nearestAway_significandOverflow_iff (format : FloatFormat)
    (numerator denominator : Nat) (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    (format.maxNormalExponent < RationalBinary.floorLog2 numerator denominator ∨
      (RationalBinary.floorLog2 numerator denominator = format.maxNormalExponent ∧
        (Model.maxFiniteDyadic format).significand <
          roundQuotient .nearestAway
            (RationalBinary.scaleByPowerOfTwo numerator denominator
              (Int.ofNat format.fracWidth - RationalBinary.floorLog2 numerator denominator)).1
            (RationalBinary.scaleByPowerOfTwo numerator denominator
              (Int.ofNat format.fracWidth - RationalBinary.floorLog2 numerator denominator)).2)) ↔
      (Model.overflowMidpoint format).toReal ≤ (numerator : ℝ) / denominator := by
  have hbounds := floorLog2_zpow_bounds numerator denominator hnumerator hdenominator
  have hfraction := format.maxFiniteFracField_lt_two_pow
  have hsignificandLower :
      (2 : ℝ) ^ format.fracWidth ≤ ((Model.maxFiniteDyadic format).significand : ℝ) := by
    simp only [Model.maxFiniteDyadic, Model.pow2_eq_two_pow]
    push_cast
    linarith [(Nat.cast_nonneg format.maxFiniteFracField : (0 : ℝ) ≤ _)]
  have hsignificandUpper :
      ((Model.maxFiniteDyadic format).significand : ℝ) + 1 ≤ 2 * (2 : ℝ) ^ format.fracWidth := by
    have hnat : (Model.maxFiniteDyadic format).significand + 1 ≤ 2 * 2 ^ format.fracWidth := by
      simp only [Model.maxFiniteDyadic, Model.pow2_eq_two_pow]
      omega
    exact_mod_cast hnat
  set unit : ℝ := (2 : ℝ) ^ (format.maxNormalExponent - format.fracWidth - 1) with hunit
  have hunitPos : 0 < unit := zpow_pos (by norm_num) _
  have hmidpoint : (Model.overflowMidpoint format).toReal =
      (2 * ((Model.maxFiniteDyadic format).significand : ℝ) + 1) * unit := by
    simp only [Model.overflowMidpoint, Numerics.Dyadic.toReal_mk_false, hunit]
    push_cast
    rw [show (Model.maxFiniteDyadic format).exponent - 1 =
        format.maxNormalExponent - format.fracWidth - 1 by
      simp [Model.maxFiniteDyadic]]
  have htop : (2 : ℝ) ^ format.maxNormalExponent = 2 * (2 : ℝ) ^ format.fracWidth * unit := by
    rw [hunit, ← zpow_natCast, mul_assoc, ← zpow_add₀ (by norm_num), ← zpow_one_add₀
      (by norm_num)]
    congr 1
    ring
  rw [hmidpoint]
  rcases lt_trichotomy (RationalBinary.floorLog2 numerator denominator)
      format.maxNormalExponent with hlt | heq | hgt
  · have hnotAbove : ¬format.maxNormalExponent < RationalBinary.floorLog2 numerator denominator :=
      by omega
    have hne : RationalBinary.floorLog2 numerator denominator ≠ format.maxNormalExponent := by
      omega
    simp only [hnotAbove, hne, false_and, or_false, false_iff, not_le]
    have hpow : (2 : ℝ) ^ (RationalBinary.floorLog2 numerator denominator + 1) ≤
        (2 : ℝ) ^ format.maxNormalExponent :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hlower : 2 * (2 : ℝ) ^ format.fracWidth * unit <
        (2 * ((Model.maxFiniteDyadic format).significand : ℝ) + 1) * unit :=
      mul_lt_mul_of_pos_right (by linarith) hunitPos
    linarith [hbounds.2]
  · simp only [heq, lt_self_iff_false, false_or, true_and]
    rw [lt_roundQuotient_nearestAway_scaled_iff _ _ _ _ hdenominator]
    push_cast
    exact le_two_mul_mul_zpow_iff _ _ format.fracWidth format.maxNormalExponent
  · simp only [hgt, true_or, true_iff]
    have hpow : (2 : ℝ) ^ (format.maxNormalExponent + 1) ≤
        (2 : ℝ) ^ RationalBinary.floorLog2 numerator denominator :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have habove : (2 : ℝ) ^ (format.maxNormalExponent + 1) =
        2 * (2 : ℝ) ^ format.maxNormalExponent := by
      rw [add_comm, zpow_one_add₀ (by norm_num)]
    have hupper : (2 * ((Model.maxFiniteDyadic format).significand : ℝ) + 1) * unit ≤
        4 * (2 : ℝ) ^ format.fracWidth * unit :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hunitPos)
    linarith [hbounds.1]

/--
The general branch's tininess test for nearest-away, on the significand rounded with an unbounded
exponent range, is a magnitude strictly below `underflowMidpoint`.
-/
private theorem nearestAway_significandTiny_iff (format : FloatFormat)
    (numerator denominator : Nat) (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    (RationalBinary.floorLog2 numerator denominator < format.minNormalExponent ∧
      (RationalBinary.floorLog2 numerator denominator + 1 < format.minNormalExponent ∨
        roundQuotient .nearestAway
            (RationalBinary.scaleByPowerOfTwo numerator denominator
              (Int.ofNat format.fracWidth - RationalBinary.floorLog2 numerator denominator)).1
            (RationalBinary.scaleByPowerOfTwo numerator denominator
              (Int.ofNat format.fracWidth - RationalBinary.floorLog2 numerator denominator)).2 <
          2 ^ (format.fracWidth + 1))) ↔
      (numerator : ℝ) / denominator < (Model.underflowMidpoint format).toReal := by
  have hbounds := floorLog2_zpow_bounds numerator denominator hnumerator hdenominator
  have hfractionPos : (1 : ℝ) ≤ (2 : ℝ) ^ format.fracWidth := one_le_pow₀ (by norm_num)
  set unit : ℝ := (2 : ℝ) ^ (format.minNormalExponent - format.fracWidth - 2) with hunit
  have hunitPos : 0 < unit := zpow_pos (by norm_num) _
  have hmidpoint : (Model.underflowMidpoint format).toReal =
      (4 * (2 : ℝ) ^ format.fracWidth - 1) * unit := by
    have hpow : 1 ≤ 4 * 2 ^ format.fracWidth := by
      have := Nat.two_pow_pos format.fracWidth
      omega
    simp only [Model.underflowMidpoint, Numerics.Dyadic.toReal_mk_false, hunit,
      Model.pow2_eq_two_pow]
    rw [Nat.cast_sub hpow]
    push_cast
    rw [show format.minSubnormalExponent - 2 = format.minNormalExponent - format.fracWidth - 2 by
      simp [FloatFormat.minSubnormalExponent]]
  have hbottom : (2 : ℝ) ^ format.minNormalExponent = 4 * (2 : ℝ) ^ format.fracWidth * unit := by
    rw [hunit, ← zpow_natCast, mul_assoc, ← zpow_add₀ (by norm_num),
      show (4 : ℝ) = (2 : ℝ) ^ (2 : Int) by norm_num, ← zpow_add₀ (by norm_num)]
    congr 1
    ring
  rw [hmidpoint]
  by_cases hnormal : format.minNormalExponent ≤ RationalBinary.floorLog2 numerator denominator
  · have hnotSub : ¬RationalBinary.floorLog2 numerator denominator < format.minNormalExponent :=
      by omega
    simp only [hnotSub, false_and, false_iff, not_lt]
    have hpow : (2 : ℝ) ^ format.minNormalExponent ≤
        (2 : ℝ) ^ RationalBinary.floorLog2 numerator denominator :=
      zpow_le_zpow_right₀ (by norm_num) hnormal
    have hupper : (4 * (2 : ℝ) ^ format.fracWidth - 1) * unit ≤
        4 * (2 : ℝ) ^ format.fracWidth * unit :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hunitPos)
    linarith [hbounds.1]
  by_cases hfar : RationalBinary.floorLog2 numerator denominator + 1 < format.minNormalExponent
  · have hsub : RationalBinary.floorLog2 numerator denominator < format.minNormalExponent := by
      omega
    simp only [hsub, hfar, true_or, and_self, true_iff]
    have hpow : (2 : ℝ) ^ (RationalBinary.floorLog2 numerator denominator + 1) ≤
        (2 : ℝ) ^ (format.minNormalExponent - 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hbelow : (2 : ℝ) ^ format.minNormalExponent =
        2 * (2 : ℝ) ^ (format.minNormalExponent - 1) := by
      rw [← zpow_one_add₀ (by norm_num)]
      congr 1
      ring
    have hlower : 2 * (2 : ℝ) ^ format.fracWidth * unit <
        (4 * (2 : ℝ) ^ format.fracWidth - 1) * unit :=
      mul_lt_mul_of_pos_right (by linarith) hunitPos
    linarith [hbounds.2]
  · have hexponentEq :
        RationalBinary.floorLog2 numerator denominator = format.minNormalExponent - 1 := by
      omega
    have hsub : RationalBinary.floorLog2 numerator denominator < format.minNormalExponent := by
      omega
    simp only [hsub, true_and, hfar, false_or]
    have hlimit : 2 ^ (format.fracWidth + 1) = (2 ^ (format.fracWidth + 1) - 1) + 1 := by
      have := Nat.two_pow_pos (format.fracWidth + 1)
      omega
    rw [hlimit, Nat.lt_add_one_iff, ← not_lt,
      lt_roundQuotient_nearestAway_scaled_iff _ _ _ _ hdenominator, not_le]
    have hbound : ((2 * (2 ^ (format.fracWidth + 1) - 1) + 1 : Nat) : ℝ) =
        4 * (2 : ℝ) ^ format.fracWidth - 1 := by
      have := Nat.two_pow_pos (format.fracWidth + 1)
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hbound, hexponentEq]
    have h := (le_two_mul_mul_zpow_iff ((numerator : ℝ) / denominator)
      (4 * (2 : ℝ) ^ format.fracWidth - 1) format.fracWidth (format.minNormalExponent - 1)).not
    rw [not_le, not_le, show format.minNormalExponent - 1 - (format.fracWidth : ℤ) - 1 =
      format.minNormalExponent - format.fracWidth - 2 by ring] at h
    exact h

/--
With nearest-away rounding, the significand-based status calculation matches the nearest-away
overflow classifier and the comparison with `underflowMidpoint`: a nonzero magnitude overflows
exactly when `rationalNearestAwayOverflowsScaled` says so, at or above the top finite midpoint, and
it is tiny exactly below `underflowMidpoint`.

`finiteStatus` sends nearest-away rounding to the classifiers, as `finiteStatus_of_nearestAway`
states. The tininess classifier also counts a tiny delivered value, and
`finiteStatus_eq_roundedSignificandStatus_of_nearestAway` uses this theorem to show that both
give the same status for the value that `Model.Policy.roundRat` delivers.
-/
theorem roundedSignificandStatus_nearestAway (format : FloatFormat) (entropy : Nat)
    (sign : Bool) (numerator denominator : Nat) (hnumerator : numerator ≠ 0)
    (hdenominator : denominator ≠ 0) :
    roundedSignificandStatus format .nearestAway entropy sign numerator denominator =
      (Model.rationalNearestAwayOverflowsScaled format numerator denominator 0,
        decide ((numerator : ℝ) / denominator < (Model.underflowMidpoint format).toReal)) := by
  have hoverflow := nearestAway_significandOverflow_iff format numerator denominator
    hnumerator hdenominator
  have htiny := nearestAway_significandTiny_iff format numerator denominator
    hnumerator hdenominator
  rw [← Model.rationalNearestAwayOverflowsScaled_eq_true_iff format _ _ hdenominator]
    at hoverflow
  simp only [roundedSignificandStatus, beq_iff_eq, hnumerator, ite_false]
  rw [Model.Policy.roundQuot_nearestAway_eq_roundQuotient _ _ _ _
    (RationalBinary.scaleByPowerOfTwo_snd_ne_zero _ _ _ hdenominator)]
  refine Prod.ext ?_ ?_
  · apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, gt_iff_lt]
    exact hoverflow
  · apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact htiny

/-! ## Conversion status of the rounding directions -/

/--
For a rounding mode with an `IEEERoundingMode` direction, conversion status is built from the
exact classifiers of that direction: `rationalRoundingOverflows` for overflow and
`rationalIsTinyAfterRoundingScaled` for tininess, under every overflow and underflow policy.
-/
theorem finiteStatus_of_ieeeRoundingMode?_eq_some {format : FloatFormat} (context : Context)
    {mode : Model.IEEERoundingMode}
    (hmode : Model.Policy.ieeeRoundingMode? context.quantization.rounding = some mode)
    (exact : Rat) (rounded : Model format) :
    finiteStatus context exact rounded =
      let overflow := Model.rationalRoundingOverflows format mode (decide (exact < 0))
        exact.num.natAbs exact.den
      let tiny := Model.rationalIsTinyAfterRoundingScaled format mode (decide (exact < 0))
        exact.num.natAbs exact.den 0 rounded
      let inexact := Model.toRat? rounded != some exact
      { inexact
        overflow
        underflow := (tiny || (context.quantization.underflow == .flushToZero &&
          Model.isTinyAfterRounding rounded)) && inexact
        saturated := overflow && context.quantization.overflow == .saturate } := by
  simp only [finiteStatus, hmode]

/--
Nearest-away conversion status is the status of the nearest-away classifiers.

The top finite midpoint overflows, and a magnitude is tiny exactly below `underflowMidpoint` or
when the delivered value is tiny, as for nearest-even rounding. This holds under every overflow and
underflow policy.
-/
theorem finiteStatus_of_nearestAway {format : FloatFormat} (context : Context)
    (hrounding : context.quantization.rounding = .nearestAway) (exact : Rat)
    (rounded : Model format) :
    finiteStatus context exact rounded =
      let overflow := Model.rationalNearestAwayOverflowsScaled format exact.num.natAbs exact.den 0
      let tiny := Model.rationalIsTinyAfterRoundingScaled format .nearest (decide (exact < 0))
        exact.num.natAbs exact.den 0 rounded
      let inexact := Model.toRat? rounded != some exact
      { inexact
        overflow
        underflow := (tiny || (context.quantization.underflow == .flushToZero &&
          Model.isTinyAfterRounding rounded)) && inexact
        saturated := overflow && context.quantization.overflow == .saturate } := by
  -- The nearest-away tininess classifier unfolds to the nearest-even one.
  rw [finiteStatus_of_ieeeRoundingMode?_eq_some context (mode := .nearestAway)
    (by rw [hrounding]; rfl) exact rounded]
  rfl

/--
For the value that `Model.Policy.roundRat` delivers, nearest-away conversion status is the status
assembled from `roundedSignificandStatus`, the significand rounded with an unbounded exponent range,
with the same inexactness, flush-to-zero underflow, and saturation as `finiteStatus`.

This holds under every overflow and underflow policy. The two tininess bits differ only when the
delivered value is tiny and the exact magnitude is zero or at least `underflowMidpoint`. The engine
never delivers a tiny value at or above `underflowMidpoint`, and at an exact zero the result is
exact, so the underflow flag agrees.
-/
theorem finiteStatus_eq_roundedSignificandStatus_of_nearestAway {format : FloatFormat}
    (context : Context) (hrounding : context.quantization.rounding = .nearestAway)
    (negative : Bool) (exact : Rat) (rounded : Model format)
    (hrounded : Model.Policy.roundRat format context.quantization context.entropy negative
      exact.num.natAbs exact.den = some rounded) :
    finiteStatus context exact rounded =
      let (overflow, tiny) := roundedSignificandStatus format .nearestAway context.entropy
        (decide (exact < 0)) exact.num.natAbs exact.den
      let inexact := Model.toRat? rounded != some exact
      { inexact
        overflow
        underflow := (tiny || (context.quantization.underflow == .flushToZero &&
          Model.isTinyAfterRounding rounded)) && inexact
        saturated := overflow && context.quantization.overflow == .saturate } := by
  have hdenominator : exact.den ≠ 0 := exact.den_nz
  have hpolicy : context.quantization =
      { rounding := .nearestAway, overflow := context.quantization.overflow,
        underflow := context.quantization.underflow } := by
    rw [← hrounding]
  have hnotNearestEven : context.quantization ≠ QuantizationPolicy.nearest := by
    intro h
    rw [h] at hrounding
    simp [QuantizationPolicy.nearest] at hrounding
  have hroundedEq : rounded = Model.Policy.roundRatGeneralOfDenNeZero format
      context.quantization context.entropy negative exact.num.natAbs exact.den hdenominator := by
    simp only [Model.Policy.roundRat, hdenominator, dite_false, beq_iff_eq, hnotNearestEven,
      ite_false, Option.some.injEq] at hrounded
    exact hrounded.symm
  rw [finiteStatus_of_nearestAway context hrounding exact rounded]
  by_cases hnumerator : exact.num.natAbs = 0
  · have hexact : exact = 0 := by
      simpa using hnumerator
    subst hexact
    have hzero : rounded = Model.zero format negative := by
      rw [hroundedEq, hpolicy]
      cases context.quantization.underflow <;>
        simp [Model.Policy.roundRatGeneralOfDenNeZero, Model.Policy.applyUnderflow,
          Model.isSubnormal_eq_false_of_isZero (Model.isZero_zero format negative)]
    have hexactResult : Model.toRat? rounded = some 0 := by
      simp [hzero, Model.toRat?]
    simp [hexactResult, roundedSignificandStatus, Model.rationalNearestAwayOverflowsScaled,
      RationalBinary.compareDyadicScaled?, Model.overflowMidpoint]
  · have hroundedTiny :
        ¬((exact.num.natAbs : ℝ) / exact.den < (Model.underflowMidpoint format).toReal) →
          Model.isTinyAfterRounding rounded = false := by
      intro hbound
      rw [hroundedEq, hpolicy]
      exact
        Model.Policy.isTinyAfterRounding_roundRatGeneralOfDenNeZero_nearestAway_eq_false format _ _
        _ _ _ _ hdenominator (le_of_not_gt hbound)
    rw [roundedSignificandStatus_nearestAway format _ _ _ _ hnumerator hdenominator,
      Model.rationalIsTinyAfterRoundingScaled_nearest_eq _ _ _ hdenominator]
    by_cases hbelow :
        (exact.num.natAbs : ℝ) / exact.den < (Model.underflowMidpoint format).toReal
    · rw [decide_eq_true hbelow]
      simp
    · rw [decide_eq_false hbelow, hroundedTiny hbelow]
      simp

end Conversion
end ExecFloat.Binary
end FloatLib.Floats
