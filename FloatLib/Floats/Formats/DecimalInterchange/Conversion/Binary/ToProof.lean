/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Binary.NearestAwayProof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Bounds

/-!
# Decimal-to-binary conversion contracts

Finite decimal inputs are evaluated as exact rationals, independently of their
cohort. Nearest-even conversion refines binary rounded-real semantics; nearest-away
conversion has the exact integer-grid semantics proved in `NearestAwayProof`.
The directed conversions inherit the binary kernels' extended-real enclosure
bounds, which include overflow to infinity.

Exception theorems expose the exact overflow and tininess predicates, including
the distinction between exponent overflow and an inexact result at the largest
finite value.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion

open FloatLib.Floats.Formats BinaryInterchange

/-- Signed natural quotient semantics agree with the exact rational input. -/
theorem signedScaledRatToReal_eq_rat (s : Bool) {x : ℚ} (hx : 0 ≤ x) :
    Model.signedScaledRatToReal s x.num.natAbs x.den 0 =
      if s then -(x : ℝ) else x := by
  have hcast : (x.num.natAbs : ℝ) / x.den = (x : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using
      congrArg (fun q : ℚ => (q : ℝ)) (rat_eq_unsigned_div hx).symm
  simp only [Model.signedScaledRatToReal, Model.scaledRatToReal, Flocq.bpow,
    zpow_zero, mul_one, hcast]

/-- The source cohort affects neither the rounded binary value nor its flags. -/
theorem toBinary_eq_of_magnitude_eq (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mode : RoundingMode) (s : Bool) (c₁ c₂ : Nat) (q₁ q₂ : Int)
    (h : (c₁ : ℚ) * (10 : ℚ) ^ q₁ = (c₂ : ℚ) * (10 : ℚ) ^ q₂) :
    toBinary fmt hfmt mode (.finite s c₁ q₁) =
      toBinary fmt hfmt mode (.finite s c₂ q₂) := by
  simp only [toBinary, h]

/-- Infinities preserve their sign and raise no exception. -/
@[simp] theorem toBinary_infinity (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mode : RoundingMode) (s : Bool) :
    toBinary fmt hfmt mode (.infinity s) =
      { value := Model.infinityOrMaxFinite fmt s, status := {} } := rfl

/-- A signaling NaN raises invalid; a quiet NaN does not. Both use the documented
quiet payload-selection policy and raise no other flag. -/
@[simp] theorem toBinary_nan (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mode : RoundingMode) (s signaling : Bool) (payload : Nat) :
    toBinary fmt hfmt mode (.nan s signaling payload) =
      { value := binaryNaN fmt s payload, status := { invalid := signaling } } := rfl

/-- Zero magnitude rounds to the source-signed binary zero in every mode. -/
@[simp] theorem roundBinaryMagnitude_zero (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mode : RoundingMode) (s : Bool) :
    roundBinaryMagnitude fmt mode s 0 = Model.zero fmt s := by
  cases mode <;>
    norm_num [roundBinaryMagnitude, Model.roundRatWithRounding, Model.roundRatWithRoundingScaled,
      Model.roundRatMagnitudeDirectedScaled, binaryNearestAwayDyadic,
      RoundingMode.roundMagnitude, RoundingMode.increment, Model.roundDyadic, hfmt,
      Model.ieeeRoundDyadic, Model.zero]
  cases s <;> simp [Model.modelSign, ← Model.negZero_eq_ofModel_zero,
    ← Model.posZero_eq_ofModel_zero]

/-- Finite nearest-even rational conversion equals binary rounded-real semantics. -/
theorem roundBinaryMagnitude_nearestEven_eq (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (s : Bool) {x : ℚ} (hx : 0 ≤ x)
    (hfinite : Model.isFinite (roundBinaryMagnitude fmt .nearestEven s x) = true) :
    Model.toReal (roundBinaryMagnitude fmt .nearestEven s x) =
      Model.roundAt fmt (if s then -(x : ℝ) else x) := by
  by_cases hz : x = 0
  · subst x
    rw [roundBinaryMagnitude_zero fmt hfmt]
    simp
  have hn : x.num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (ne_of_gt (Rat.num_pos.mpr (lt_of_le_of_ne hx (Ne.symm hz))))
  change Model.toReal (Model.roundRatScaled fmt s x.num.natAbs x.den 0) = _
  rw [Model.toReal_roundRatScaled_eq_roundAt fmt s _ _ 0 hfmt hn x.den_nz hfinite,
    signedScaledRatToReal_eq_rat s hx]

/-- Nearest-even conversion of a finite decimal input has one binary rounding.
The observable finiteness condition excludes an infinite delivered result. -/
theorem toBinary_nearestEven_eq (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (s : Bool) (c : Nat) (q : Int)
    (hfinite : Model.isFinite
      (toBinary fmt hfmt .nearestEven (.finite s c q)).value = true) :
    Model.toReal (toBinary fmt hfmt .nearestEven (.finite s c q)).value =
      Model.roundAt fmt ((Datum.finiteValue s c q : ℚ) : ℝ) := by
  have h := roundBinaryMagnitude_nearestEven_eq fmt hfmt s
    (by positivity : (0 : ℚ) ≤ c * (10 : ℚ) ^ q) hfinite
  cases s <;> simpa [toBinary, Datum.finiteValue] using h

/-- Nearest-away conversion of a finite decimal input equals its exact rounded dyadic
on the destination grid; the encoder contributes no second rounding. -/
theorem toBinary_nearestAway_eq (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (s : Bool) (c : Nat) (q : Int)
    (hfinite : Model.isFinite
      (toBinary fmt hfmt .nearestAway (.finite s c q)).value = true) :
    Model.toReal (toBinary fmt hfmt .nearestAway (.finite s c q)).value =
      (binaryNearestAwayDyadic fmt s ((c : ℚ) * (10 : ℚ) ^ q)).toReal :=
  roundBinaryMagnitude_nearestAway_eq fmt hfmt s (by positivity) hfinite

/-- Upward rational conversion encloses the exact input, including an infinite result. -/
theorem le_roundBinaryMagnitude_towardPositive (fmt : FloatFormat)
    (hfmt : fmt.isIEEE = true) (s : Bool) {x : ℚ} (hx : 0 ≤ x) :
    (((if s then -(x : ℝ) else (x : ℝ)) : ℝ) : EReal) ≤
      Model.toEReal (roundBinaryMagnitude fmt .towardPositive s x) := by
  have h := Model.le_toEReal_roundRatUp fmt s x.num.natAbs x.den hfmt x.den_nz
  rwa [signedScaledRatToReal_eq_rat s hx] at h

/-- Downward rational conversion encloses the exact input, including an infinite result. -/
theorem roundBinaryMagnitude_towardNegative_le (fmt : FloatFormat)
    (hfmt : fmt.isIEEE = true) (s : Bool) {x : ℚ} (hx : 0 ≤ x) :
    Model.toEReal (roundBinaryMagnitude fmt .towardNegative s x) ≤
      (((if s then -(x : ℝ) else (x : ℝ)) : ℝ) : EReal) := by
  have h := Model.toEReal_roundRatDown_le fmt s x.num.natAbs x.den hfmt x.den_nz
  rwa [signedScaledRatToReal_eq_rat s hx] at h

/-- Conversion toward positive infinity is an extended-real upper bound. -/
theorem le_toBinary_towardPositive (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (s : Bool) (c : Nat) (q : Int) :
    (((Datum.finiteValue s c q : ℚ) : ℝ) : EReal) ≤
      Model.toEReal (toBinary fmt hfmt .towardPositive (.finite s c q)).value := by
  have h := le_roundBinaryMagnitude_towardPositive fmt hfmt s
    (by positivity : (0 : ℚ) ≤ c * (10 : ℚ) ^ q)
  cases s <;> simpa [toBinary, Datum.finiteValue] using h

/-- Conversion toward negative infinity is an extended-real lower bound. -/
theorem toBinary_towardNegative_le (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (s : Bool) (c : Nat) (q : Int) :
    Model.toEReal (toBinary fmt hfmt .towardNegative (.finite s c q)).value ≤
      (((Datum.finiteValue s c q : ℚ) : ℝ) : EReal) := by
  have h := roundBinaryMagnitude_towardNegative_le fmt hfmt s
    (by positivity : (0 : ℚ) ≤ c * (10 : ℚ) ^ q)
  cases s <;> simpa [toBinary, Datum.finiteValue] using h

/-- A positive decimal input rounded toward zero does not increase. -/
theorem toBinary_towardZero_positive_le (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (c : Nat) (q : Int) :
    Model.toEReal (toBinary fmt hfmt .towardZero (.finite false c q)).value ≤
      (((Datum.finiteValue false c q : ℚ) : ℝ) : EReal) := by
  simpa only [toBinary, roundBinaryMagnitude, Model.roundRatWithRounding,
    Model.roundRatWithRoundingScaled] using toBinary_towardNegative_le fmt hfmt false c q

/-- A negative decimal input rounded toward zero does not decrease. -/
theorem le_toBinary_towardZero_negative (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (c : Nat) (q : Int) :
    (((Datum.finiteValue true c q : ℚ) : ℝ) : EReal) ≤
      Model.toEReal (toBinary fmt hfmt .towardZero (.finite true c q)).value := by
  simpa only [toBinary, roundBinaryMagnitude, Model.roundRatWithRounding,
    Model.roundRatWithRoundingScaled, Bool.not_true] using
      le_toBinary_towardPositive fmt hfmt true c q

/-- A finite decimal input cannot raise invalid during numeric conversion. -/
@[simp] theorem toBinary_finite_invalid (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mode : RoundingMode) (s : Bool) (c : Nat) (q : Int) :
    (toBinary fmt hfmt mode (.finite s c q)).status.invalid = false := rfl

/-- Numeric conversion cannot raise division-by-zero. -/
@[simp] theorem toBinary_divideByZero (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mode : RoundingMode) (x : Datum) :
    (toBinary fmt hfmt mode x).status.divideByZero = false := by cases x <;> rfl

/-- The finite conversion path raises overflow exactly at the mode's rational boundary. -/
theorem toBinary_overflow_iff (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mode : RoundingMode) (s : Bool) (c : Nat) (q : Int) :
    (toBinary fmt hfmt mode (.finite s c q)).status.overflow = true ↔
      binaryOverflow fmt mode s ((c : ℚ) * (10 : ℚ) ^ q) = true := Iff.rfl

/-- Inexact means exponent overflow or a changed exact rational value. -/
theorem toBinary_inexact_iff (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mode : RoundingMode) (s : Bool) (c : Nat) (q : Int) :
    (toBinary fmt hfmt mode (.finite s c q)).status.inexact = true ↔
      (toBinary fmt hfmt mode (.finite s c q)).status.overflow = true ∨
      Model.toRat? (toBinary fmt hfmt mode (.finite s c q)).value ≠
        some (Datum.finiteValue s c q) := by
  cases s <;> simp [toBinary, binaryStatus, Datum.finiteValue]

/-- Underflow is an inexact tiny result without exponent overflow. Tininess is measured
after rounding to the destination precision with an unbounded exponent range. -/
theorem toBinary_underflow_iff (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mode : RoundingMode) (s : Bool) (c : Nat) (q : Int) :
    (toBinary fmt hfmt mode (.finite s c q)).status.underflow = true ↔
      (toBinary fmt hfmt mode (.finite s c q)).status.overflow = false ∧
      binaryTiny fmt mode s ((c : ℚ) * (10 : ℚ) ^ q)
        (toBinary fmt hfmt mode (.finite s c q)).value = true ∧
      (toBinary fmt hfmt mode (.finite s c q)).status.inexact = true := by
  simp [toBinary, binaryStatus, and_assoc]

end FloatLib.Floats.Formats.DecimalInterchange.Conversion
