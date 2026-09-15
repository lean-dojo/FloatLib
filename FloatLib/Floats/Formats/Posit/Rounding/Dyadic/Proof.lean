/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Runtime
import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Correctness of exact-dyadic posit rounding

The executable posit rounder searches codes using exact dyadic comparisons, chooses between
neighbors with ties-to-even, restores the sign, and packs the final model value. This module proves
that the complete pipeline is equal to the simple rational specification in `Rounding.Proof`.

Using dyadics avoids constructing large rational numerators in the runtime, but it does not change
the rounding rule. The lemmas here are the common semantic boundary for arbitrary-precision,
native-word, and fixed-limb posit backends, so specialized kernels need only prove that their local
comparisons agree with this rounder.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DyadicRounding

/--
A positive code below the sign mask takes the ordinary finite branch of the totalized decoder.

Native-word and fixed-limb backends use this shared fact after proving that their direct field
decoder agrees with `Model.decodeFields`; the exceptional-value argument therefore lives in one
place rather than being duplicated by every representation backend.
-/
theorem nonnegativeDyadicAt_eq_decodeFields_of_nonzero
    (format : Format) (code : Nat)
    (hcode : code < format.signMaskNat)
    (hnonzero : code ≠ 0) :
    nonnegativeDyadicAt format code =
      (Model.ofNatBits (format := format) code).decodeFields.toDyadic := by
  let value := Model.ofNatBits (format := format) code
  have hvalueBits : value.toNatBits = code :=
    Model.toNatBits_ofNatBits_of_lt code
      (hcode.trans format.signMaskNat_lt_modulus)
  have hvalueZero : value ≠ Model.zero format := by
    intro equality
    have bitsEquality := congrArg Model.toNatBits equality
    rw [hvalueBits, Model.zero_toNatBits] at bitsEquality
    exact hnonzero bitsEquality
  have hvalueNaR : value ≠ Model.nar format := by
    intro equality
    have bitsEquality := congrArg Model.toNatBits equality
    rw [hvalueBits, Model.nar_toNatBits] at bitsEquality
    omega
  have hnar : value.isNaR = false :=
    beq_eq_false_iff_ne.mpr hvalueNaR
  have hzero : value.isZero = false :=
    beq_eq_false_iff_ne.mpr hvalueZero
  have hdecode :
      value.decodeExact = .finite value.decodeFields := by
    simp [Model.decodeExact, hnar, hzero]
  unfold nonnegativeDyadicAt
  change
    (match value.decodeExact with
      | .zero => FloatLib.Numerics.Dyadic.zero
      | .finite fields => fields.toDyadic
      | .nar => FloatLib.Numerics.Dyadic.zero) =
        value.decodeFields.toDyadic
  rw [hdecode]

/-- Dyadic code decoding has the same rational denotation as the reference helper. -/
@[simp] theorem nonnegativeDyadicAt_toRat (format : Format) (code : Nat) :
    (nonnegativeDyadicAt format code).toRat =
      Model.nonnegativeRatAt format code := by
  unfold nonnegativeDyadicAt Model.nonnegativeRatAt
  cases Model.decodeExact (Model.ofNatBits (format := format) code) <;>
    simp [Model.DecodedFields.toRat]

/-- The dyadic and rational lower-code searches are extensionally identical. -/
theorem lowerCodeForPositive_eq_reference
    (format : Format) (target : FloatLib.Numerics.Dyadic) :
    lowerCodeForPositive format target =
      Model.lowerCodeForPositive format target.toRat := by
  unfold lowerCodeForPositive Model.lowerCodeForPositive
  congr 1
  funext code
  rw [FloatLib.Numerics.Dyadic.isLessOrEqual_eq_decide,
    nonnegativeDyadicAt_toRat]

/--
A locally bracketed candidate is exactly the lower code selected by bisection.

This is a property of the exact dyadic specification, not of any execution backend. Direct
packers use it to prove their field constructors once, then execute without searching.
-/
theorem lowerCodeForPositive_eq_of_bracket
    (format : Format) (target : FloatLib.Numerics.Dyadic) (candidate : Nat)
    (hcandidate : candidate < format.signMaskNat)
    (hlower :
      (nonnegativeDyadicAt format candidate).isLessOrEqual target = true)
    (hupper :
      candidate + 1 < format.signMaskNat →
        target.isLess (nonnegativeDyadicAt format (candidate + 1)) = true) :
    lowerCodeForPositive format target = candidate := by
  rw [lowerCodeForPositive_eq_reference]
  apply Model.lowerCodeForPositive_eq_of_bracket
      format target.toRat candidate hcandidate
  · simpa only [FloatLib.Numerics.Dyadic.isLessOrEqual_eq_decide,
      decide_eq_true_eq, nonnegativeDyadicAt_toRat] using hlower
  · intro hsuccessor
    simpa only [FloatLib.Numerics.Dyadic.isLess_eq_decide,
      decide_eq_true_eq, nonnegativeDyadicAt_toRat] using
      hupper hsuccessor

/-- Decoding code `1` yields the closed minimum-positive dyadic fields. -/
theorem nonnegativeDyadicAt_one_eq_fields (format : Format) :
    nonnegativeDyadicAt format 1 =
      {
        negative := false
        significand := 1
        exponent := -(4 * Int.ofNat (format.payloadBits - 1))
      } := by
  rw [nonnegativeDyadicAt_eq_decodeFields_of_nonzero
    format 1 format.one_lt_signMaskNat (by decide)]
  set value := Model.ofNatBits (format := format) 1
  have hsign : value.signBit = false :=
    Model.signBit_ofNatBits_eq_false format 1 format.one_lt_signMaskNat
  have hmagnitude : value.magnitudeBits = 1 :=
    Model.magnitudeBits_ofNatBits_of_lt_signMask format 1 format.one_lt_signMaskNat
  have hpayloadPos := format.payloadBits_pos
  have hfields :
      value.trailingBits = 0 ∧
        value.regimeValue = -Int.ofNat (format.payloadBits - 1) := by
    by_cases hpayload : format.payloadBits = 1
    · have hregimeBit : value.regimeBit = true := by
        simp [Model.regimeBit, hmagnitude, hpayload]
      have hrun : value.regimeRunLength = 1 := by
        simp [Model.regimeRunLength, hmagnitude, hregimeBit, hpayload,
          Model.countLeadingRun]
      simp [Model.trailingBits, Model.hasRegimeTerminator, Model.regimeValue,
        hregimeBit, hrun, hpayload]
    · have hregimeBit : value.regimeBit = false := by
        simp only [Model.regimeBit, hmagnitude, Nat.testBit_eq_decide_div_mod_eq]
        rw [Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega))]
        decide
      have hrun : value.regimeRunLength = format.payloadBits - 1 := by
        unfold Model.regimeRunLength
        rw [hmagnitude, hregimeBit,
          Model.countLeadingRun_false_eq_log2 1 _ one_pos (Nat.one_lt_two_pow (by omega))]
        rfl
      have hterminator : value.hasRegimeTerminator = true := by
        simp only [Model.hasRegimeTerminator, hrun, decide_eq_true_eq]
        omega
      refine ⟨?_, by simp [Model.regimeValue, hregimeBit, hrun]⟩
      simp only [Model.trailingBits, hrun, hterminator, ite_true]
      omega
  obtain ⟨htrailing, hregimeValue⟩ := hfields
  have hused : value.usedExponentBits = 0 := by
    simp [Model.usedExponentBits, htrailing]
  have hfractionBits : value.fractionBits = 0 := by
    simp [Model.fractionBits, htrailing, hused]
  have hexponent : value.exponentField = 0 := by
    simp [Model.exponentField, Model.storedExponentField, hmagnitude, hfractionBits, hused]
  have hfractionField : value.fractionField = 0 := by
    simp [Model.fractionField, hmagnitude, hfractionBits]
  simp only [Model.DecodedFields.toDyadic, Model.decodeFields, Model.scale, hsign,
    hfractionBits, hfractionField, hexponent, hregimeValue, Format.regimeExponentStep]
  congr 1
  simp only [Int.ofNat_eq_natCast]
  push_cast
  omega

/--
The smallest positive posit is a unit significand at the bottom regime scale.

This closed form is shared by every execution backend, so underflow tests do not decode the
fixed encoding `1` on each arithmetic operation.
-/
theorem minPositive_eq_fields (format : Format) :
    minPositive format =
      {
        negative := false
        significand := 1
        exponent := -(4 * Int.ofNat (format.payloadBits - 1))
      } :=
  rfl

/-- The executable closed form equals the standard decoding of code `1`. -/
theorem minPositive_eq_nonnegativeDyadicAt (format : Format) :
    minPositive format = nonnegativeDyadicAt format 1 := by
  rw [nonnegativeDyadicAt_one_eq_fields]
  rfl

/--
The smallest positive posit's exponent is a lower bound for every ordinary nonzero posit scale.

The negative-regime case uses the mandatory terminator bit: a nonzero magnitude cannot consume
the complete payload as a run of leading zeros. This is the representation fact needed to align
an exact product of two posits with the associated quire.
-/
theorem minPositive_exponent_le_scale_of_not_special
    {format : Format} (value : Model format)
    (hzero : value.isZero = false)
    (hnar : value.isNaR = false) :
    (minPositive format).exponent ≤ value.scale := by
  rw [minPositive_eq_fields]
  have hzeroNe : value ≠ Model.zero format := by
    intro hvalue
    subst value
    simp at hzero
  have hnarNe : value ≠ Model.nar format := by
    intro hvalue
    subst value
    simp at hnar
  have hmagnitudePos : 0 < value.magnitudeBits :=
    Nat.pos_of_ne_zero
      (Model.magnitudeBits_ne_zero_of_ne_zero value hzeroNe)
  have hmagnitudeBound :
      value.magnitudeBits < 2 ^ format.payloadBits := by
    simpa [Format.signMaskNat, Format.signIndex, Format.payloadBits] using
      (Model.magnitudeBits_lt_signMask_of_ne_nar value hnarNe)
  have hrunPositive : 0 < value.regimeRunLength :=
    Model.regimeRunLength_pos value
  have hfraction :
      value.fractionBits ≤ value.trailingBits :=
    Model.fractionBits_le_trailingBits value
  have hpayloadPos := format.payloadBits_pos
  have hstep :
      Int.ofNat format.regimeExponentStep = (4 : Int) :=
    rfl
  cases hbit : value.regimeBit with
  | false =>
      have hrun :
          value.regimeRunLength < format.payloadBits := by
        have hrunEq :=
          Model.countLeadingRun_false_eq_log2
            value.magnitudeBits format.payloadBits hmagnitudePos hmagnitudeBound
        unfold Model.regimeRunLength
        rw [hbit, hrunEq]
        omega
      have hterminator : value.hasRegimeTerminator = true := by
        simp [Model.hasRegimeTerminator, hrun]
      have htrailing :
          value.trailingBits =
            format.payloadBits - value.regimeRunLength - 1 := by
        simp [Model.trailingBits, hterminator]
      have hfields :
          value.regimeRunLength + 1 + value.fractionBits ≤
            format.payloadBits := by
        rw [htrailing] at hfraction
        omega
      have hfieldsInt :
          (value.regimeRunLength : Int) + 1 + value.fractionBits ≤
            format.payloadBits := by
        exact_mod_cast hfields
      simp only [Model.scale, Model.regimeValue, hbit,
        Bool.false_eq_true, ite_false, hstep, Int.ofNat_eq_natCast]
      omega
  | true =>
      have hfields :
          value.regimeRunLength + value.fractionBits ≤ format.payloadBits :=
        Model.regimeRunLength_add_fractionBits_le_payload value
      have hrunPositiveInt : (0 : Int) < value.regimeRunLength := by
        exact_mod_cast hrunPositive
      have hfieldsInt :
          (value.regimeRunLength : Int) + value.fractionBits ≤
            format.payloadBits := by
        exact_mod_cast hfields
      have hpayloadPosInt : (0 : Int) < format.payloadBits := by
        exact_mod_cast hpayloadPos
      simp only [Model.scale, Model.regimeValue, hbit, ite_true,
        hstep, Int.ofNat_eq_natCast]
      omega

/-- The dyadic minimum has exactly the reference minimum's rational denotation. -/
@[simp] theorem minPositive_toRat (format : Format) :
    (minPositive format).toRat = Model.minPositiveRat format := by
  rw [minPositive_eq_nonnegativeDyadicAt, nonnegativeDyadicAt_toRat]
  rfl

/-- The dyadic threshold has exactly the reference threshold's rational denotation. -/
@[simp] theorem roundingThreshold_toRat (format : Format) (lowerCode : Nat) :
    (roundingThreshold format lowerCode).toRat =
      Model.roundingThreshold format lowerCode := by
  simp [roundingThreshold, Model.roundingThreshold]

/-- Single-comparison nearest-even selection equals the reference two-predicate decision tree. -/
theorem chooseNearestCode_eq
    (target threshold : FloatLib.Numerics.Dyadic) (lower upper : Nat) :
    chooseNearestCode target threshold lower upper =
      if target.isLess threshold then
        lower
      else if threshold.isLess target then
        upper
      else if lower % 2 = 0 then
        lower
      else
        upper := by
  unfold chooseNearestCode
  rw [FloatLib.Numerics.Dyadic.isLess_eq_decide,
    FloatLib.Numerics.Dyadic.isLess_eq_decide]
  cases hcomparison : target.compare threshold with
  | lt =>
      have hless : target.toRat < threshold.toRat :=
        (FloatLib.Numerics.Dyadic.compare_eq_lt_iff target threshold).mp
          hcomparison
      have hnotGreater : ¬threshold.toRat < target.toRat :=
        not_lt_of_ge hless.le
      simp [hless]
  | eq =>
      have hnotLess : ¬target.toRat < threshold.toRat := by
        intro hless
        have himpossible :
            target.compare threshold = .lt :=
          (FloatLib.Numerics.Dyadic.compare_eq_lt_iff target threshold).mpr
            hless
        rw [hcomparison] at himpossible
        contradiction
      have hnotGreater : ¬threshold.toRat < target.toRat := by
        intro hgreater
        have himpossible :
            target.compare threshold = .gt :=
          (FloatLib.Numerics.Dyadic.compare_eq_gt_iff target threshold).mpr
            hgreater
        rw [hcomparison] at himpossible
        contradiction
      simp [hnotLess, hnotGreater]
  | gt =>
      have hgreater : threshold.toRat < target.toRat :=
        (FloatLib.Numerics.Dyadic.compare_eq_gt_iff target threshold).mp
          hcomparison
      have hnotLess : ¬target.toRat < threshold.toRat :=
        not_lt_of_ge hgreater.le
      simp [hgreater, hnotLess]

/-- Nearest-even selection returns one of the two supplied neighboring codes. -/
theorem chooseNearestCode_eq_lower_or_upper
    (target threshold : FloatLib.Numerics.Dyadic) (lower upper : Nat) :
    chooseNearestCode target threshold lower upper = lower ∨
      chooseNearestCode target threshold lower upper = upper := by
  unfold chooseNearestCode
  generalize target.compare threshold = comparison
  cases comparison with
  | lt => exact Or.inl rfl
  | eq =>
      by_cases heven : lower % 2 = 0
      · simp [heven]
      · simp [heven]
  | gt => exact Or.inr rfl

/--
Positive dyadic rounding selects exactly the code chosen by the rational specification.

The hypotheses are the invariant established by `round`: zero has already been handled and the
temporary magnitude has its sign cleared.
-/
theorem roundPositiveCode_eq_reference_of_positive
    (format : Format) (target : FloatLib.Numerics.Dyadic)
    (hsignificand : target.significand ≠ 0)
    (hnegative : target.negative = false) :
    roundPositiveCode format target =
      Model.roundPositiveCode format target.toRat := by
  have hpositive :=
    FloatLib.Numerics.Dyadic.toRat_pos_of_significand_ne_zero
      target hsignificand hnegative
  have hsignificandBool : (target.significand == 0) = false :=
    beq_eq_false_iff_ne.mpr hsignificand
  unfold roundPositiveCode Model.roundPositiveCode
  simp only [hsignificandBool, hnegative, Bool.false_or,
    Bool.false_eq_true, ite_false, not_le.mpr hpositive,
    FloatLib.Numerics.Dyadic.isLess_eq_decide, decide_eq_true_eq,
    minPositive_toRat, chooseNearestCode_eq, roundingThreshold_toRat,
    lowerCodeForPositive_eq_reference]

/--
Positive exact-dyadic rounding re-encodes every nonnegative finite posit code.

This is the dyadic counterpart of `Model.roundPositiveCode_nonnegativeRatAt`. Native execution
backends use it to return an exactly representable direct candidate without decoding its
successor or the one-bit-wider rounding boundary.
-/
theorem roundPositiveCode_nonnegativeDyadicAt
    (format : Format) {code : Nat}
    (hcode : code < format.signMaskNat) :
    roundPositiveCode format (nonnegativeDyadicAt format code) = code := by
  by_cases hzero : code = 0
  · subst code
    have htarget :
        nonnegativeDyadicAt format 0 =
          FloatLib.Numerics.Dyadic.zero := by
      unfold nonnegativeDyadicAt
      change
        (match (Model.zero format).decodeExact with
        | .zero => FloatLib.Numerics.Dyadic.zero
        | .finite fields => fields.toDyadic
        | .nar => FloatLib.Numerics.Dyadic.zero) =
          FloatLib.Numerics.Dyadic.zero
      rw [Model.decodeExact_zero]
    rw [htarget]
    rfl
  · have hdecoded :=
      nonnegativeDyadicAt_eq_decodeFields_of_nonzero
        format code hcode hzero
    have hsignificand :
        (nonnegativeDyadicAt format code).significand ≠ 0 := by
      rw [hdecoded]
      simp only [Model.DecodedFields.toDyadic, Model.decodeFields]
      have hpositive := Nat.two_pow_pos
        (Model.ofNatBits (format := format) code).fractionBits
      omega
    have hnegative :
        (nonnegativeDyadicAt format code).negative = false := by
      rw [hdecoded]
      simp only [Model.DecodedFields.toDyadic, Model.decodeFields]
      exact Model.signBit_ofNatBits_eq_false format code hcode
    rw [roundPositiveCode_eq_reference_of_positive
      format (nonnegativeDyadicAt format code) hsignificand hnegative]
    rw [nonnegativeDyadicAt_toRat]
    exact Model.roundPositiveCode_nonnegativeRatAt format hcode

/-- Positive dyadic model rounding refines the reference rational model rounding. -/
theorem roundPositive_eq_reference_of_positive
    (format : Format) (target : FloatLib.Numerics.Dyadic)
    (hsignificand : target.significand ≠ 0)
    (hnegative : target.negative = false) :
    roundPositive format target =
      Model.roundPositiveRat format target.toRat := by
  unfold roundPositive Model.roundPositiveRat
  rw [roundPositiveCode_eq_reference_of_positive
    format target hsignificand hnegative]

/-- Clearing the sign leaves the integer significand unchanged. -/
@[simp] theorem magnitude_significand (value : FloatLib.Numerics.Dyadic) :
    (magnitude value).significand = value.significand :=
  rfl

/-- The magnitude of a dyadic has a clear sign bit. -/
@[simp] theorem magnitude_negative (value : FloatLib.Numerics.Dyadic) :
    (magnitude value).negative = false :=
  rfl

/-- Clearing the sign preserves a positive value and negates a negative value. -/
theorem magnitude_toRat (value : FloatLib.Numerics.Dyadic) :
    (magnitude value).toRat =
      if value.negative then -value.toRat else value.toRat := by
  cases hnegative : value.negative <;>
    simp [magnitude, FloatLib.Numerics.Dyadic.toRat,
      FloatLib.Numerics.Dyadic.signedSignificand, hnegative]

/-- Direct sign restoration preserves the configured posit word width. -/
theorem restoreSignCode_lt_modulus
    (format : Format) (negative : Bool) (positiveCode : Nat)
    (hpositive : positiveCode < format.signMaskNat) :
    restoreSignCode format negative positiveCode < format.modulus := by
  unfold restoreSignCode
  split
  · split
    · exact Nat.two_pow_pos format.bits
    · rename_i hnonzero
      have hpositiveNonzero : positiveCode ≠ 0 :=
        fun equality => hnonzero (beq_iff_eq.mpr equality)
      have hpositiveLt : positiveCode < format.modulus :=
        lt_trans hpositive format.signMaskNat_lt_modulus
      omega
  · exact lt_trans hpositive format.signMaskNat_lt_modulus

/-- Packing a sign-restored code agrees with whole-word model negation. -/
theorem ofNatBits_restoreSignCode
    (format : Format) (negative : Bool) (positiveCode : Nat)
    (hpositive : positiveCode < format.signMaskNat) :
    Model.ofNatBits (format := format)
        (restoreSignCode format negative positiveCode) =
      if negative then
        Model.neg (Model.ofNatBits (format := format) positiveCode)
      else
        Model.ofNatBits (format := format) positiveCode := by
  unfold restoreSignCode
  split
  · split
    · rename_i hzero
      have hcode : positiveCode = 0 := beq_iff_eq.mp hzero
      subst positiveCode
      change Model.zero format = Model.neg (Model.zero format)
      rw [Model.neg_zero]
    · unfold Model.neg
      rw [Model.toNatBits_ofNatBits_of_lt]
      exact lt_trans hpositive format.signMaskNat_lt_modulus
  · rfl

/-- Exact-dyadic rounding returns exactly the reference rational specification. -/
theorem round_eq_roundRat (format : Format) (value : FloatLib.Numerics.Dyadic) :
    round format value = Model.roundRat format value.toRat := by
  by_cases hsignificand : value.significand = 0
  · have hzero : value.toRat = 0 := by
      simp [FloatLib.Numerics.Dyadic.toRat,
        FloatLib.Numerics.Dyadic.signedSignificand, hsignificand]
    simp [round, hsignificand, hzero]
  · have hsignificandBool : (value.significand == 0) = false :=
      beq_eq_false_iff_ne.mpr hsignificand
    cases hnegative : value.negative
    · have hpositive :
          0 < value.toRat :=
        FloatLib.Numerics.Dyadic.toRat_pos_of_significand_ne_zero
          value hsignificand hnegative
      rw [round]
      simp only [hsignificandBool, Bool.false_eq_true, ite_false,
        hnegative]
      rw [roundPositive_eq_reference_of_positive format (magnitude value)]
      · rw [magnitude_toRat, hnegative]
        simp [Model.roundRat, hpositive.ne', not_lt.mpr hpositive.le]
      · simpa using hsignificand
      · rfl
    · have hmagnitudePositive :
          0 < (magnitude value).toRat :=
        FloatLib.Numerics.Dyadic.toRat_pos_of_significand_ne_zero
          (magnitude value) (by simpa using hsignificand) rfl
      have hvalueNegative : value.toRat < 0 := by
        rw [magnitude_toRat, hnegative] at hmagnitudePositive
        simpa using hmagnitudePositive
      rw [round]
      simp only [hsignificandBool, Bool.false_eq_true, ite_false,
        hnegative, ite_true]
      rw [roundPositive_eq_reference_of_positive format (magnitude value)]
      · rw [magnitude_toRat, hnegative]
        simp [Model.roundRat, hvalueNegative, hvalueNegative.ne]
      · simpa using hsignificand
      · rfl

end FloatLib.Floats.Formats.Posit.Model.DyadicRounding
