/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.DyadicOrder
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Logarithm
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Tininess
public import FloatLib.Numerics.IEEEStatus.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SqrtSemantics
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.NonNaN
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.SquareRoot

/-!
# Correctness of IEEE exception status

The executable status kernels in `Status.Runtime` satisfy cross-flag invariants and
operation-level specifications. Import `BinaryInterchange.Status` for the combined public
interface.

The rounding-status classifiers compare an exact dyadic or scaled rational with the supplied
rounded value. Operation wrappers compute that exact witness alongside the value-only operation.
This file proves the ternary values in real order, cross-flag invariants, preservation of the
ordinary result, and operation-specific invalid and divide-by-zero conditions. In a conventional
IEEE format the invalid flag of addition, multiplication, fused multiply-add, and division depends
only on the classes and signs of the operands (`add_invalid_of_isIEEE` and its siblings): finite
operands never raise it, except zero over zero. The real-order
tininess boundaries are in `Status.Tininess`. On a finite input with a clear sign bit, square root
raises `inexact` exactly when its delivered value is not the real square root (`sqrt_inexact_iff`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats.Formats.Flocq

/-! ## Constructors and rounding-status invariants -/

/-- `outcomeWithInvalid` preserves its supplied floating-point value. -/
@[simp] theorem outcomeWithInvalid_value {fmt : FloatFormat}
    (value : Model fmt) (invalid : Bool) :
    (outcomeWithInvalid value invalid).value = value := rfl

/-- `outcomeWithInvalid` records its supplied invalid-operation condition. -/
@[simp] theorem outcomeWithInvalid_invalid {fmt : FloatFormat}
    (value : Model fmt) (invalid : Bool) :
    (outcomeWithInvalid value invalid).status.invalid = invalid := by
  cases invalid <;> rfl

/-- `outcomeWithInvalid` never raises divide-by-zero. -/
@[simp] theorem outcomeWithInvalid_divideByZero {fmt : FloatFormat}
    (value : Model fmt) (invalid : Bool) :
    (outcomeWithInvalid value invalid).status.divideByZero = false := by
  cases invalid <;> rfl

/--
`outcomeWithInvalid` carries the exceptional-result ternary convention `.eq`.

This is a convention for NaNs, exact infinities, and placeholders, not a statement that the value
equals an exact real result.
-/
@[simp] theorem outcomeWithInvalid_ternary {fmt : FloatFormat}
    (value : Model fmt) (invalid : Bool) :
    (outcomeWithInvalid value invalid).ternary = .eq := rfl

/-- A dyadic rounding outcome delivers the value it was given. -/
@[simp] theorem dyadicRoundingOutcome_value (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (value : Model fmt) :
    (dyadicRoundingOutcome fmt mode exact value).value = value :=
  rfl

/-- The status of a dyadic rounding outcome is `dyadicRoundingStatus`. -/
@[simp] theorem dyadicRoundingOutcome_status (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (value : Model fmt) :
    (dyadicRoundingOutcome fmt mode exact value).status =
      dyadicRoundingStatus fmt mode exact value :=
  rfl

/-- The ternary value of a dyadic rounding outcome is `dyadicTernary`. -/
@[simp] theorem dyadicRoundingOutcome_ternary (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (value : Model fmt) :
    (dyadicRoundingOutcome fmt mode exact value).ternary = dyadicTernary exact value :=
  rfl

/-- A scaled rational rounding outcome delivers the value it was given. -/
@[simp] theorem rationalRoundingOutcomeScaled_value (fmt : FloatFormat)
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat) (exponent : Int)
    (value : Model fmt) :
    (rationalRoundingOutcomeScaled fmt mode sign numerator denominator exponent value).value =
      value :=
  rfl

/-- The status of a scaled rational rounding outcome is `rationalRoundingStatusScaled`. -/
@[simp] theorem rationalRoundingOutcomeScaled_status (fmt : FloatFormat)
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat) (exponent : Int)
    (value : Model fmt) :
    (rationalRoundingOutcomeScaled fmt mode sign numerator denominator exponent value).status =
      rationalRoundingStatusScaled fmt mode sign numerator denominator exponent value :=
  rfl

/-- The ternary value of a scaled rational rounding outcome is `rationalTernaryScaled`. -/
@[simp] theorem rationalRoundingOutcomeScaled_ternary (fmt : FloatFormat)
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat) (exponent : Int)
    (value : Model fmt) :
    (rationalRoundingOutcomeScaled fmt mode sign numerator denominator exponent value).ternary =
      rationalTernaryScaled sign numerator denominator exponent value :=
  rfl

/-! ## Ternary values -/

/-- A finite value denotes the real value of its decoded dyadic. -/
theorem toReal_eq_toReal_finiteDyadic {fmt : FloatFormat} {x : Model fmt}
    (hfinite : isFinite x = true) :
    toReal x = (finiteDyadic x hfinite).toReal := by
  have hdecode : toDyadic? x = some (finiteDyadic x hfinite) := by
    simp [finiteDyadic]
  rw [toReal_eq, hdecode]

/-- For a finite delivery, the dyadic ternary value is the real comparison with the exact value. -/
theorem dyadicTernary_eq_compare {fmt : FloatFormat} (exact : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = true) :
    dyadicTernary exact rounded = compare (toReal rounded) exact.toReal := by
  rw [dyadicTernary, dite_eq_left hfinite, cmpDyadic_eq_compare,
    toReal_eq_toReal_finiteDyadic hfinite]

/-- A finite delivery has the dyadic ternary value `.lt` exactly when it is below the exact one. -/
theorem dyadicTernary_eq_lt_iff {fmt : FloatFormat} (exact : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = true) :
    dyadicTernary exact rounded = .lt ↔ toReal rounded < exact.toReal := by
  rw [dyadicTernary_eq_compare exact hfinite, compare_lt_iff_lt]

/-- A finite delivery has the dyadic ternary value `.eq` exactly when it equals the exact value. -/
theorem dyadicTernary_eq_eq_iff {fmt : FloatFormat} (exact : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = true) :
    dyadicTernary exact rounded = .eq ↔ toReal rounded = exact.toReal := by
  rw [dyadicTernary_eq_compare exact hfinite, compare_eq_iff_eq]

/-- A finite delivery has the dyadic ternary value `.gt` exactly when it is above the exact one. -/
theorem dyadicTernary_eq_gt_iff {fmt : FloatFormat} (exact : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = true) :
    dyadicTernary exact rounded = .gt ↔ exact.toReal < toReal rounded := by
  rw [dyadicTernary_eq_compare exact hfinite, compare_gt_iff_gt]

/--
A non-finite delivery has the ternary value given by the sign of the exact value, the overflow
convention of `dyadicTernary`.
-/
theorem dyadicTernary_of_isFinite_eq_false {fmt : FloatFormat} (exact : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = false) :
    dyadicTernary exact rounded = if exact.negative then .lt else .gt := by
  simp [dyadicTernary, hfinite]

/--
For a finite delivery and a nonzero denominator, the rational ternary value is the real comparison
with the exact signed rational.
-/
theorem rationalTernaryScaled_eq_compare {fmt : FloatFormat} (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) {rounded : Model fmt}
    (hdenominator : denominator ≠ 0) (hfinite : isFinite rounded = true) :
    rationalTernaryScaled sign numerator denominator exponent rounded =
      compare (toReal rounded) (signedScaledRatToReal sign numerator denominator exponent) := by
  rw [rationalTernaryScaled, dite_eq_left hfinite,
    compareDyadicScaled?_eq_compare sign numerator denominator exponent _ hdenominator,
    ← toReal_eq_toReal_finiteDyadic hfinite]
  rcases lt_trichotomy (toReal rounded)
      (signedScaledRatToReal sign numerator denominator exponent) with hless | hequal | hgreater
  · rw [compare_lt_iff_lt.mpr hless, compare_gt_iff_gt.mpr hless]
    rfl
  · rw [hequal]
    simp
  · rw [compare_gt_iff_gt.mpr hgreater, compare_lt_iff_lt.mpr hgreater]
    rfl

/-- A finite delivery has the rational ternary value `.lt` exactly when it is below the rational. -/
theorem rationalTernaryScaled_eq_lt_iff {fmt : FloatFormat} (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) {rounded : Model fmt}
    (hdenominator : denominator ≠ 0) (hfinite : isFinite rounded = true) :
    rationalTernaryScaled sign numerator denominator exponent rounded = .lt ↔
      toReal rounded < signedScaledRatToReal sign numerator denominator exponent := by
  rw [rationalTernaryScaled_eq_compare sign numerator denominator exponent hdenominator hfinite,
    compare_lt_iff_lt]

/-- A finite delivery has the rational ternary value `.eq` exactly when it equals the rational. -/
theorem rationalTernaryScaled_eq_eq_iff {fmt : FloatFormat} (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) {rounded : Model fmt}
    (hdenominator : denominator ≠ 0) (hfinite : isFinite rounded = true) :
    rationalTernaryScaled sign numerator denominator exponent rounded = .eq ↔
      toReal rounded = signedScaledRatToReal sign numerator denominator exponent := by
  rw [rationalTernaryScaled_eq_compare sign numerator denominator exponent hdenominator hfinite,
    compare_eq_iff_eq]

/-- A finite delivery has the rational ternary value `.gt` exactly when it is above the rational. -/
theorem rationalTernaryScaled_eq_gt_iff {fmt : FloatFormat} (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) {rounded : Model fmt}
    (hdenominator : denominator ≠ 0) (hfinite : isFinite rounded = true) :
    rationalTernaryScaled sign numerator denominator exponent rounded = .gt ↔
      signedScaledRatToReal sign numerator denominator exponent < toReal rounded := by
  rw [rationalTernaryScaled_eq_compare sign numerator denominator exponent hdenominator hfinite,
    compare_gt_iff_gt]

/--
A non-finite delivery has the rational ternary value given by the sign of the exact rational, the
overflow convention of `rationalTernaryScaled`.
-/
theorem rationalTernaryScaled_of_isFinite_eq_false {fmt : FloatFormat} (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) {rounded : Model fmt}
    (hfinite : isFinite rounded = false) :
    rationalTernaryScaled sign numerator denominator exponent rounded =
      if sign then .lt else .gt := by
  simp [rationalTernaryScaled, hfinite]

/--
With denominator one, the rational ternary value is the dyadic ternary value of the same exact
number, so operations may use either representation of their exact result.
-/
theorem rationalTernaryScaled_eq_dyadicTernary {fmt : FloatFormat} (exact : Numerics.Dyadic)
    (rounded : Model fmt) :
    rationalTernaryScaled exact.negative exact.significand 1 exact.exponent rounded =
      dyadicTernary exact rounded := by
  cases hfinite : isFinite rounded
  · rw [rationalTernaryScaled_of_isFinite_eq_false _ _ _ _ hfinite,
      dyadicTernary_of_isFinite_eq_false exact hfinite]
  · rw [rationalTernaryScaled_eq_compare _ _ _ _ one_ne_zero hfinite,
      dyadicTernary_eq_compare exact hfinite]
    congr 1
    cases hnegative : exact.negative <;>
      simp [signedScaledRatToReal, scaledRatToReal, Numerics.Dyadic.toReal,
        Numerics.Dyadic.signedSignificand, hnegative, bpow,
        FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/-- The exact-infinity ternary value is `.eq` exactly for the infinity itself. -/
theorem exactInfinityTernary_eq_eq_iff {fmt : FloatFormat} (negative : Bool)
    (value : Model fmt) :
    exactInfinityTernary negative value = .eq ↔
      isInf value = true ∧ signBit value = negative := by
  unfold exactInfinityTernary
  cases hinf : isInf value <;> cases hsign : signBit value <;> cases negative <;> simp

/--
Any delivery other than the exact infinity itself has the exact-infinity ternary value `.lt` for
`+∞` and `.gt` for `-∞`. For a saturated finite value this is the order, and for the overflow NaN
of a format without infinities it is the convention of `IEEEOutcome.ternary`.
-/
theorem exactInfinityTernary_of_not_infinity {fmt : FloatFormat} (negative : Bool)
    {value : Model fmt} (hvalue : ¬(isInf value = true ∧ signBit value = negative)) :
    exactInfinityTernary negative value = if negative then .gt else .lt := by
  unfold exactInfinityTernary
  rw [ite_eq_right (by simpa [Bool.and_eq_true, beq_iff_eq] using hvalue)]

/-- Squaring is strictly monotone on nonnegative reals, so it preserves comparisons there. -/
private theorem compare_mul_self_eq_compare {left right : ℝ} (hleft : 0 ≤ left)
    (hright : 0 ≤ right) :
    compare (left * left) (right * right) = compare left right := by
  rcases lt_trichotomy left right with hless | hequal | hgreater
  · rw [compare_lt_iff_lt.mpr hless,
      compare_lt_iff_lt.mpr (mul_self_lt_mul_self hleft hless)]
  · subst hequal
    simp
  · rw [compare_gt_iff_gt.mpr hgreater,
      compare_gt_iff_gt.mpr (mul_self_lt_mul_self hright hgreater)]

/-- A finite delivery is compared with the radicand through the exact square of its decoding. -/
theorem dyadicSqrtTernary_of_isFinite {fmt : FloatFormat} (radicand : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = true) :
    dyadicSqrtTernary radicand rounded =
      cmpDyadic
        { negative := false
          significand :=
            (finiteDyadic rounded hfinite).significand *
              (finiteDyadic rounded hfinite).significand
          exponent :=
            (finiteDyadic rounded hfinite).exponent + (finiteDyadic rounded hfinite).exponent }
        radicand := by
  obtain ⟨actual, hactual⟩ := exists_toDyadic?_of_isFinite hfinite
  simp [dyadicSqrtTernary, hactual]

/-- A non-finite delivery has the square-root ternary value `.gt`. -/
theorem dyadicSqrtTernary_of_isFinite_eq_false {fmt : FloatFormat}
    (radicand : Numerics.Dyadic) {rounded : Model fmt} (hfinite : isFinite rounded = false) :
    dyadicSqrtTernary radicand rounded = .gt := by
  simp [dyadicSqrtTernary, toDyadic?_eq_none_of_isFinite_eq_false hfinite]

/--
For a finite nonnegative delivery and a nonnegative radicand, the square-root ternary value is the
real comparison of the delivered value with the exact square root.
-/
theorem dyadicSqrtTernary_eq_compare {fmt : FloatFormat} (radicand : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = true)
    (hrounded : 0 ≤ toReal rounded) (hradicand : 0 ≤ radicand.toReal) :
    dyadicSqrtTernary radicand rounded =
      compare (toReal rounded) (Real.sqrt radicand.toReal) := by
  rw [dyadicSqrtTernary_of_isFinite radicand hfinite, cmpDyadic_eq_compare]
  have hsquare :
      ({ negative := false
         significand :=
           (finiteDyadic rounded hfinite).significand *
             (finiteDyadic rounded hfinite).significand
         exponent :=
           (finiteDyadic rounded hfinite).exponent +
             (finiteDyadic rounded hfinite).exponent } : Numerics.Dyadic).toReal =
        toReal rounded * toReal rounded := by
    rw [toReal_eq_toReal_finiteDyadic hfinite]
    simpa using Dyadic.toReal_mul (finiteDyadic rounded hfinite) (finiteDyadic rounded hfinite)
  rw [hsquare]
  calc compare (toReal rounded * toReal rounded) radicand.toReal
      = compare (toReal rounded * toReal rounded)
          (Real.sqrt radicand.toReal * Real.sqrt radicand.toReal) := by
        rw [Real.mul_self_sqrt hradicand]
    _ = compare (toReal rounded) (Real.sqrt radicand.toReal) :=
        compare_mul_self_eq_compare hrounded (Real.sqrt_nonneg _)

/-! ## Flag invariants of the rounding-status builders -/

/--
The common shape of `dyadicRoundingStatus` and `rationalRoundingStatusScaled`: the overflow
classification first, then the underflow and inexact flags of a finite delivery, then an infinite
delivery, and otherwise invalid. Only the proofs below use it; both builders unfold to it by `rfl`.
-/
private def roundingStatusShape {fmt : FloatFormat} (rounded : Model fmt) (overflows tiny : Bool)
    (inexact : isFinite rounded = true → Bool) : Numerics.IEEEStatus :=
  if overflows then
    { overflow := true, inexact := true }
  else if hfinite : isFinite rounded = true then
    { underflow := tiny && inexact hfinite, inexact := inexact hfinite }
  else if isInf rounded then
    { overflow := true, inexact := true }
  else
    { invalid := true }

private theorem dyadicRoundingStatus_eq_shape (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (rounded : Model fmt) :
    dyadicRoundingStatus fmt mode exact rounded =
      roundingStatusShape rounded (dyadicRoundingOverflows fmt mode exact)
        (dyadicIsTinyAfterRounding fmt mode exact rounded)
        (fun hfinite => cmpDyadic exact (finiteDyadic rounded hfinite) != .eq) :=
  rfl

private theorem rationalRoundingStatusScaled_eq_shape (fmt : FloatFormat)
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat) (exponent : Int)
    (rounded : Model fmt) :
    rationalRoundingStatusScaled fmt mode sign numerator denominator exponent rounded =
      roundingStatusShape rounded
        (rationalRoundingOverflowsScaled fmt mode sign numerator denominator exponent)
        (rationalIsTinyAfterRoundingScaled fmt mode sign numerator denominator exponent rounded)
        (fun hfinite => !(rationalEqualsDyadicScaled sign numerator denominator exponent
          (finiteDyadic rounded hfinite))) :=
  rfl

/--
The four branches of `roundingStatusShape`, each with the condition that selects it. The flag
invariants below are read off this case split.
-/
private theorem roundingStatusShape_cases {fmt : FloatFormat} (rounded : Model fmt)
    (overflows tiny : Bool) (inexact : isFinite rounded = true → Bool) :
    (overflows = true ∧
        roundingStatusShape rounded overflows tiny inexact =
          { overflow := true, inexact := true }) ∨
      (overflows = false ∧ ∃ hfinite : isFinite rounded = true,
        roundingStatusShape rounded overflows tiny inexact =
          { underflow := tiny && inexact hfinite, inexact := inexact hfinite }) ∨
      (overflows = false ∧ isFinite rounded = false ∧ isInf rounded = true ∧
        roundingStatusShape rounded overflows tiny inexact =
          { overflow := true, inexact := true }) ∨
      (overflows = false ∧ isFinite rounded = false ∧ isInf rounded = false ∧
        roundingStatusShape rounded overflows tiny inexact = { invalid := true }) := by
  unfold roundingStatusShape
  cases overflows
  · by_cases hfinite : isFinite rounded = true
    · exact Or.inr (Or.inl ⟨rfl, hfinite, by simp [hfinite]⟩)
    · cases isInf rounded <;> simp [hfinite]
  · simp

private theorem roundingStatusShape_inexact_of_underflow {fmt : FloatFormat}
    {rounded : Model fmt} {overflows tiny : Bool} {inexact : isFinite rounded = true → Bool}
    (h : (roundingStatusShape rounded overflows tiny inexact).underflow = true) :
    (roundingStatusShape rounded overflows tiny inexact).inexact = true := by
  rcases roundingStatusShape_cases rounded overflows tiny inexact with
    ⟨_, hs⟩ | ⟨_, _, hs⟩ | ⟨_, _, _, hs⟩ | ⟨_, _, _, hs⟩ <;> simp_all

private theorem roundingStatusShape_overflow {fmt : FloatFormat}
    (rounded : Model fmt) (overflows tiny : Bool) (inexact : isFinite rounded = true → Bool) :
    (roundingStatusShape rounded overflows tiny inexact).overflow =
      (overflows || (!isFinite rounded && isInf rounded)) := by
  rcases roundingStatusShape_cases rounded overflows tiny inexact with
    ⟨_, hs⟩ | ⟨_, _, hs⟩ | ⟨_, _, _, hs⟩ | ⟨_, _, _, hs⟩ <;> simp_all

private theorem roundingStatusShape_inexact_of_overflow {fmt : FloatFormat}
    {rounded : Model fmt} {overflows tiny : Bool} {inexact : isFinite rounded = true → Bool}
    (h : (roundingStatusShape rounded overflows tiny inexact).overflow = true) :
    (roundingStatusShape rounded overflows tiny inexact).inexact = true := by
  rcases roundingStatusShape_cases rounded overflows tiny inexact with
    ⟨_, hs⟩ | ⟨_, _, hs⟩ | ⟨_, _, _, hs⟩ | ⟨_, _, _, hs⟩ <;> simp_all

private theorem roundingStatusShape_not_underflow_of_overflow {fmt : FloatFormat}
    {rounded : Model fmt} {overflows tiny : Bool} {inexact : isFinite rounded = true → Bool}
    (h : (roundingStatusShape rounded overflows tiny inexact).overflow = true) :
    (roundingStatusShape rounded overflows tiny inexact).underflow = false := by
  rcases roundingStatusShape_cases rounded overflows tiny inexact with
    ⟨_, hs⟩ | ⟨_, _, hs⟩ | ⟨_, _, _, hs⟩ | ⟨_, _, _, hs⟩ <;> simp_all

private theorem roundingStatusShape_invalid {fmt : FloatFormat}
    (rounded : Model fmt) (overflows tiny : Bool) (inexact : isFinite rounded = true → Bool) :
    (roundingStatusShape rounded overflows tiny inexact).invalid =
      (!overflows && !isFinite rounded && !isInf rounded) := by
  rcases roundingStatusShape_cases rounded overflows tiny inexact with
    ⟨_, hs⟩ | ⟨_, _, hs⟩ | ⟨_, _, _, hs⟩ | ⟨_, _, _, hs⟩ <;> simp_all

private theorem roundingStatusShape_divideByZero {fmt : FloatFormat}
    (rounded : Model fmt) (overflows tiny : Bool) (inexact : isFinite rounded = true → Bool) :
    (roundingStatusShape rounded overflows tiny inexact).divideByZero = false := by
  rcases roundingStatusShape_cases rounded overflows tiny inexact with
    ⟨_, hs⟩ | ⟨_, _, hs⟩ | ⟨_, _, _, hs⟩ | ⟨_, _, _, hs⟩ <;> simp_all

/-- After-rounding dyadic underflow implies inexactness. -/
theorem dyadicRoundingStatus_inexact_of_underflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {exact : Numerics.Dyadic} {rounded : Model fmt}
    (h : (dyadicRoundingStatus fmt mode exact rounded).underflow = true) :
    (dyadicRoundingStatus fmt mode exact rounded).inexact = true := by
  rw [dyadicRoundingStatus_eq_shape] at h ⊢
  exact roundingStatusShape_inexact_of_underflow h

/--
Dyadic rounding reports overflow exactly when rounding crosses the format's overflow threshold or
the supplied rounded result is an infinity.
-/
@[simp] theorem dyadicRoundingStatus_overflow {fmt : FloatFormat}
    (mode : IEEERoundingMode) (exact : Numerics.Dyadic) (rounded : Model fmt) :
    (dyadicRoundingStatus fmt mode exact rounded).overflow =
      (dyadicRoundingOverflows fmt mode exact ||
        (!isFinite rounded && isInf rounded)) := by
  rw [dyadicRoundingStatus_eq_shape, roundingStatusShape_overflow]

/-- For a finite result, dyadic overflow is exactly the exact-value overflow classification. -/
theorem dyadicRoundingStatus_overflow_of_isFinite {fmt : FloatFormat}
    (mode : IEEERoundingMode) (exact : Numerics.Dyadic) (rounded : Model fmt)
    (hfinite : isFinite rounded = true) :
    (dyadicRoundingStatus fmt mode exact rounded).overflow =
      dyadicRoundingOverflows fmt mode exact := by
  rw [dyadicRoundingStatus_overflow]
  simp [hfinite]

/-- Dyadic rounding overflow always raises inexact. -/
theorem dyadicRoundingStatus_inexact_of_overflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {exact : Numerics.Dyadic} {rounded : Model fmt}
    (h : (dyadicRoundingStatus fmt mode exact rounded).overflow = true) :
    (dyadicRoundingStatus fmt mode exact rounded).inexact = true := by
  rw [dyadicRoundingStatus_eq_shape] at h ⊢
  exact roundingStatusShape_inexact_of_overflow h

/-- A dyadic rounding result cannot simultaneously signal overflow and underflow. -/
theorem dyadicRoundingStatus_not_underflow_of_overflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {exact : Numerics.Dyadic} {rounded : Model fmt}
    (h : (dyadicRoundingStatus fmt mode exact rounded).overflow = true) :
    (dyadicRoundingStatus fmt mode exact rounded).underflow = false := by
  rw [dyadicRoundingStatus_eq_shape] at h ⊢
  exact roundingStatusShape_not_underflow_of_overflow h

/-- After-rounding scaled rational underflow implies inexactness. -/
theorem rationalRoundingStatusScaled_inexact_of_underflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {sign : Bool} {numerator denominator : Nat}
    {exponent : Int} {rounded : Model fmt}
    (h : (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).underflow = true) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).inexact = true := by
  rw [rationalRoundingStatusScaled_eq_shape] at h ⊢
  exact roundingStatusShape_inexact_of_underflow h

/--
Scaled rational rounding reports overflow exactly when rounding crosses the format's overflow
threshold or the supplied rounded result is an infinity.
-/
@[simp] theorem rationalRoundingStatusScaled_overflow {fmt : FloatFormat}
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (rounded : Model fmt) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent rounded).overflow =
      (rationalRoundingOverflowsScaled fmt mode sign numerator denominator exponent ||
        (!isFinite rounded && isInf rounded)) := by
  rw [rationalRoundingStatusScaled_eq_shape, roundingStatusShape_overflow]

/--
For a finite result, scaled rational overflow is exactly the exact-value overflow classification.
-/
theorem rationalRoundingStatusScaled_overflow_of_isFinite {fmt : FloatFormat}
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (rounded : Model fmt) (hfinite : isFinite rounded = true) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent rounded).overflow =
      rationalRoundingOverflowsScaled fmt mode sign numerator denominator exponent := by
  rw [rationalRoundingStatusScaled_overflow]
  simp [hfinite]

/-- Scaled rational overflow always raises inexact. -/
theorem rationalRoundingStatusScaled_inexact_of_overflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {sign : Bool} {numerator denominator : Nat}
    {exponent : Int} {rounded : Model fmt}
    (h : (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).overflow = true) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).inexact = true := by
  rw [rationalRoundingStatusScaled_eq_shape] at h ⊢
  exact roundingStatusShape_inexact_of_overflow h

/-- Scaled rational rounding cannot signal overflow and underflow together. -/
theorem rationalRoundingStatusScaled_not_underflow_of_overflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {sign : Bool} {numerator denominator : Nat}
    {exponent : Int} {rounded : Model fmt}
    (h : (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).overflow = true) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).underflow = false := by
  rw [rationalRoundingStatusScaled_eq_shape] at h ⊢
  exact roundingStatusShape_not_underflow_of_overflow h

/--
The dyadic rounding-status builder sets invalid exactly when its overflow classifier is false and
the supplied result is neither finite nor infinite.
-/
@[simp] theorem dyadicRoundingStatus_invalid
    (fmt : FloatFormat) (mode : IEEERoundingMode) (exact : Numerics.Dyadic)
    (rounded : Model fmt) :
    (dyadicRoundingStatus fmt mode exact rounded).invalid =
      (!dyadicRoundingOverflows fmt mode exact &&
        !isFinite rounded && !isInf rounded) := by
  rw [dyadicRoundingStatus_eq_shape, roundingStatusShape_invalid]

/-- A finite dyadic rounding result cannot raise invalid. -/
theorem dyadicRoundingStatus_invalid_false_of_isFinite
    (fmt : FloatFormat) (mode : IEEERoundingMode) (exact : Numerics.Dyadic)
    (rounded : Model fmt) (hfinite : isFinite rounded = true) :
    (dyadicRoundingStatus fmt mode exact rounded).invalid = false := by
  rw [dyadicRoundingStatus_invalid]
  simp [hfinite]

/--
The dyadic rounding-status builder always leaves `divideByZero` clear, for every exact value and
supplied result.
-/
@[simp] theorem dyadicRoundingStatus_divideByZero_false
    (fmt : FloatFormat) (mode : IEEERoundingMode) (exact : Numerics.Dyadic)
    (rounded : Model fmt) :
    (dyadicRoundingStatus fmt mode exact rounded).divideByZero = false := by
  rw [dyadicRoundingStatus_eq_shape, roundingStatusShape_divideByZero]

/--
The scaled rational rounding-status builder sets invalid exactly when its overflow classifier is
false and the supplied result is neither finite nor infinite.
-/
@[simp] theorem rationalRoundingStatusScaled_invalid
    (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (rounded : Model fmt) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).invalid =
        (!rationalRoundingOverflowsScaled fmt mode sign numerator denominator exponent &&
          !isFinite rounded && !isInf rounded) := by
  rw [rationalRoundingStatusScaled_eq_shape, roundingStatusShape_invalid]

/-- A finite scaled rational rounding result cannot raise invalid. -/
theorem rationalRoundingStatusScaled_invalid_false_of_isFinite
    (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (rounded : Model fmt)
    (hfinite : isFinite rounded = true) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).invalid = false := by
  rw [rationalRoundingStatusScaled_invalid]
  simp [hfinite]

/--
The scaled rational rounding-status builder always leaves `divideByZero` clear, for every
denominator and supplied result. It does not by itself establish a correct division: the
division status raises divide-by-zero in its own exceptional branch (`div_divideByZero`).
-/
@[simp] theorem rationalRoundingStatusScaled_divideByZero_false
    (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (rounded : Model fmt) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).divideByZero = false := by
  rw [rationalRoundingStatusScaled_eq_shape, roundingStatusShape_divideByZero]

/-! ## Result projection -/

/-- Addition with `status := true` delivers the value of addition in the same direction. -/
@[simp] theorem value_add {fmt : FloatFormat}
    (x y : Model fmt) (mode : IEEERoundingMode) :
    (add x y (mode := mode) (status := true)).value = add x y (mode := mode) := by
  rw [← Internal.Status.add_eq, ← Internal.Directed.add_eq]
  unfold Internal.Status.add
  split <;> simp

/-- Subtraction with `status := true` delivers the value of subtraction in the same direction. -/
@[simp] theorem value_sub {fmt : FloatFormat}
    (x y : Model fmt) (mode : IEEERoundingMode) :
    (sub x y (mode := mode) (status := true)).value = sub x y (mode := mode) := by
  rw [← Internal.Directed.sub_eq]
  exact (value_add x (neg y) mode).trans (Internal.Directed.add_eq mode x (neg y)).symm

/--
Multiplication with `status := true` delivers the value of multiplication in the same direction.
-/
@[simp] theorem value_mul {fmt : FloatFormat}
    (x y : Model fmt) (mode : IEEERoundingMode) :
    (mul x y (mode := mode) (status := true)).value = mul x y (mode := mode) := by
  rw [← Internal.Status.mul_eq, ← Internal.Directed.mul_eq]
  unfold Internal.Status.mul
  split <;> simp

/-- Division with `status := true` delivers the value of division in the same direction. -/
@[simp] theorem value_div {fmt : FloatFormat}
    (x y : Model fmt) (mode : IEEERoundingMode) :
    (div x y (mode := mode) (status := true)).value = div x y (mode := mode) := by
  rw [← Internal.Status.div_eq, ← Internal.Directed.div_eq]
  cases mode <;> unfold Internal.Status.div Internal.Directed.div
  · split
    · rename_i dx dy hx hy
      simp [Internal.Nearest.div, DivBackend.word_eq_spec, Spec.div, hx, hy,
        Internal.Directed.roundRatScaled]
      by_cases hdy : dy.significand = 0 <;>
        by_cases hdx : dx.significand = 0 <;>
          simp [hdy, hdx]
    · simp
  all_goals
    split
    · rename_i dx dy hx hy
      have hxNaN := isNaN_eq_false_of_toDyadic?_some hx
      have hyNaN := isNaN_eq_false_of_toDyadic?_some hy
      have hchoose : chooseNaN2 x y = none :=
        (chooseNaN2_eq_none_iff x y).2 ⟨hxNaN, hyNaN⟩
      have hxInf := isInf_eq_false_of_toDyadic?_some hx
      have hyInf := isInf_eq_false_of_toDyadic?_some hy
      have hxFinite :=
        isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hxNaN hxInf
      have hyFinite :=
        isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hyNaN hyInf
      have hxExact := finiteDyadic_eq_of_toDyadic hxFinite hx
      have hyExact := finiteDyadic_eq_of_toDyadic hyFinite hy
      have hxZero := isZero_eq_beq_zero_of_toDyadic?_some hx
      have hyZero := isZero_eq_beq_zero_of_toDyadic?_some hy
      have hxSign := sign_eq_signBit_of_toDyadic?_some hx
      have hySign := sign_eq_signBit_of_toDyadic?_some hy
      have hsign :
          Bool.xor dx.negative dy.negative = (dx.negative != dy.negative) := by
        cases dx.negative <;> cases dy.negative <;> rfl
      simp [hchoose, hxInf, hyInf, hxExact, hyExact, hxZero, hyZero,
        ← hxSign, ← hySign]
      by_cases hdy : dy.significand = 0 <;>
        by_cases hdx : dx.significand = 0 <;>
          simp [hdy, hdx, hsign]
    · simp

/-- FMA with `status := true` delivers the value of FMA in the same direction. -/
@[simp] theorem value_fma {fmt : FloatFormat}
    (x y z : Model fmt) (mode : IEEERoundingMode) :
    (fma x y z (mode := mode) (status := true)).value = fma x y z (mode := mode) := by
  rw [← Internal.Status.fma_eq, ← Internal.Directed.fma_eq]
  unfold Internal.Status.fma
  split <;> simp

/--
Square root with `status := true` delivers the value of square root in the same direction.
-/
@[simp] theorem value_sqrt {fmt : FloatFormat}
    (x : Model fmt) (mode : IEEERoundingMode) :
    (sqrt x (mode := mode) (status := true)).value = sqrt x (mode := mode) := by
  rw [← Internal.Status.sqrt_eq, ← Internal.Directed.sqrt_eq]
  unfold Internal.Status.sqrt
  dsimp only
  split
  · split <;> simp [outcomeWithInvalid]
  · split
    · simp [outcomeWithInvalid]
    · split <;> simp [outcomeWithInvalid]

/-! ## Operation-specific exceptional status -/

/-- Finite addition reports its dyadic rounding status and ternary value. -/
theorem add_status_of_toDyadic
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (mode : IEEERoundingMode)
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy) :
    add x y (mode := mode) (status := true) =
      let exact := addDyadic dx dy
      let value := add x y (mode := mode)
      { value
        status := dyadicRoundingStatus fmt mode exact value
        ternary := dyadicTernary exact value } := by
  simp [← Internal.Status.add_eq, Internal.Status.add, Internal.Directed.add_eq,
    dyadicRoundingOutcome, hx, hy]

/--
Invalid-status classification for addition in every descriptor.

Exceptional operands raise invalid exactly for a signaling NaN or opposite-signed infinities when
no NaN was supplied. For finite operands the right side is the rounding status's own test on the
delivered sum, invalid only for a NaN that does not replace an overflow. In a conventional IEEE
format the rounded sum is never a NaN, and `add_invalid_of_isIEEE` states the flag from operand
classes alone. That the finite branch is false in the other encodings is not proved.
-/
theorem add_invalid
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    (add x y (mode := mode) (status := true)).status.invalid =
      match toDyadic? x, toDyadic? y with
      | some dx, some dy =>
          let exact := addDyadic dx dy
          let value := add x y (mode := mode)
          !dyadicRoundingOverflows fmt mode exact &&
            !isFinite value && !isInf value
      | _, _ =>
          isSNaN x || isSNaN y ||
            (!(isNaN x || isNaN y) &&
              (isInf x && isInf y && signBit x != signBit y)) := by
  cases hx : toDyadic? x <;> cases hy : toDyadic? y <;>
    simp [← Internal.Status.add_eq, Internal.Status.add, Internal.Directed.add_eq, hx, hy]

/-- Finite multiplication reports its dyadic rounding status and ternary value. -/
theorem mul_status_of_toDyadic
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (mode : IEEERoundingMode)
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy) :
    mul x y (mode := mode) (status := true) =
      let exact : Numerics.Dyadic :=
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      let value := mul x y (mode := mode)
      { value
        status := dyadicRoundingStatus fmt mode exact value
        ternary := dyadicTernary exact value } := by
  simp [← Internal.Status.mul_eq, Internal.Status.mul, Internal.Directed.mul_eq,
    dyadicRoundingOutcome, hx, hy]

/--
Invalid-status classification for multiplication in every descriptor.

Exceptional operands raise invalid exactly for a signaling NaN or an infinity-times-zero operation
without an input NaN. For finite operands the right side is the rounding status's own test on the
delivered product; `mul_invalid_of_isIEEE` shows it is false in a conventional IEEE format, and
the other encodings are not covered.
-/
theorem mul_invalid
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    (mul x y (mode := mode) (status := true)).status.invalid =
      match toDyadic? x, toDyadic? y with
      | some dx, some dy =>
          let exact : Numerics.Dyadic :=
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent }
          let value := mul x y (mode := mode)
          !dyadicRoundingOverflows fmt mode exact &&
            !isFinite value && !isInf value
      | _, _ =>
          isSNaN x || isSNaN y ||
            (!(isNaN x || isNaN y) &&
              ((isInf x && isZero y) || (isInf y && isZero x))) := by
  cases hx : toDyadic? x <;> cases hy : toDyadic? y <;>
    simp [← Internal.Status.mul_eq, Internal.Status.mul, Internal.Directed.mul_eq, hx, hy]

/-- Finite FMA reports its dyadic rounding status and ternary value. -/
theorem fma_status_of_toDyadic
    {fmt : FloatFormat} {x y z : Model fmt} {dx dy dz : Numerics.Dyadic}
    (mode : IEEERoundingMode)
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hz : toDyadic? z = some dz) :
    fma x y z (mode := mode) (status := true) =
      let product : Numerics.Dyadic :=
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      let exact := addDyadic product dz
      let value := fma x y z (mode := mode)
      { value
        status := dyadicRoundingStatus fmt mode exact value
        ternary := dyadicTernary exact value } := by
  simp [← Internal.Status.fma_eq, Internal.Status.fma, Internal.Directed.fma_eq,
    dyadicRoundingOutcome, hx, hy, hz]

/--
Invalid-status classification for fused multiply-add in every descriptor.

Exceptional operands use the IEEE signaling-NaN, infinity-times-zero, and opposite-infinity rules.
For the implementation-defined quiet-NaN case, this library raises invalid for infinity times zero
even when the addend is a quiet NaN, while an input NaN suppresses the opposite-infinity
condition. For finite operands the right side is the rounding status's own test on the singly
rounded result; `fma_invalid_of_isIEEE` shows it is false in a conventional IEEE format, and the
other encodings are not covered.
-/
theorem fma_invalid
    {fmt : FloatFormat} (x y z : Model fmt) (mode : IEEERoundingMode) :
    (fma x y z (mode := mode) (status := true)).status.invalid =
      match toDyadic? x, toDyadic? y, toDyadic? z with
      | some dx, some dy, some dz =>
          let product : Numerics.Dyadic :=
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent }
          let exact := addDyadic product dz
          let value := fma x y z (mode := mode)
          !dyadicRoundingOverflows fmt mode exact &&
            !isFinite value && !isInf value
      | _, _, _ =>
          let hasNaN := isNaN x || isNaN y || isNaN z
          let invalidProduct := (isInf x || isInf y) && (isZero x || isZero y)
          let productIsInf := (isInf x || isInf y) && !(isZero x || isZero y)
          let oppositeInfiniteAddend :=
            productIsInf && isInf z &&
              signBit z != Bool.xor (signBit x) (signBit y)
          isSNaN x || isSNaN y || isSNaN z ||
            invalidProduct || (!hasNaN && oppositeInfiniteAddend) := by
  cases hx : toDyadic? x <;> cases hy : toDyadic? y <;>
    cases hz : toDyadic? z <;> simp [← Internal.Status.fma_eq, Internal.Status.fma,
      Internal.Directed.fma_eq, hx, hy, hz]

/--
Finite division by a nonzero divisor reports its scaled-rational rounding status and ternary
value. A zero dividend gives the exact zero of the quotient sign with clear status.
-/
theorem div_status_of_toDyadic_nonzero
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (mode : IEEERoundingMode)
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hynonzero : dy.significand ≠ 0) :
    div x y (mode := mode) (status := true) =
      let sign := Bool.xor dx.negative dy.negative
      let exponentDifference := dx.exponent - dy.exponent
      let value :=
        Internal.Directed.roundRatScaled fmt mode sign dx.significand dy.significand
          exponentDifference
      { value
        status :=
          rationalRoundingStatusScaled fmt mode sign dx.significand dy.significand
            exponentDifference value
        ternary :=
          rationalTernaryScaled sign dx.significand dy.significand exponentDifference value } := by
  by_cases hxzero : dx.significand = 0
  · have hvalue :
        Internal.Directed.roundRatScaled fmt mode (Bool.xor dx.negative dy.negative)
            dx.significand dy.significand (dx.exponent - dy.exponent) =
          zero fmt (Bool.xor dx.negative dy.negative) := by
      rw [hxzero]
      cases mode <;>
        simp [Internal.Directed.roundRatScaled, roundRatNearestAwayScaled,
          roundRatMagnitudeDirectedScaled, hynonzero]
    have hfinite := isFinite_eq_true_of_isZero_eq_true _
      (isZero_zero fmt (Bool.xor dx.negative dy.negative))
    simp only [hvalue]
    simp only [← Internal.Status.div_eq, Internal.Status.div, hx, hy, hxzero, hynonzero,
      beq_self_eq_true, beq_iff_eq, ite_true, ite_false]
    cases mode <;>
      simp [rationalRoundingStatusScaled, rationalTernaryScaled, rationalRoundingOverflowsScaled,
        rationalNearestEvenOverflowsScaled, rationalNearestAwayOverflowsScaled,
        rationalTruncationOverflowsScaled, rationalMagnitudeOverflowsScaled,
        rationalEqualsDyadicScaled, Numerics.RationalBinary.compareDyadicScaled?,
        overflowMidpoint, overflowLimit, hfinite, hynonzero, Numerics.IEEEStatus.clear]
  simp [← Internal.Status.div_eq, Internal.Status.div, rationalRoundingOutcomeScaled, hx, hy,
    hxzero, hynonzero]

/--
Invalid-status classification for division in every descriptor.

The finite branch distinguishes zero-over-zero, which is invalid, an exact zero quotient, and
nonzero rational rounding, where the right side is the rounding status's own test on the delivered
quotient. Exceptional operands use the signaling-NaN and infinity-over-infinity rules.
`div_invalid_of_isIEEE` states the flag from operand classes alone in a conventional IEEE format;
for the other encodings the rounding branch is not shown to be false.
-/
theorem div_invalid
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    (div x y (mode := mode) (status := true)).status.invalid =
      match toDyadic? x, toDyadic? y with
      | some dx, some dy =>
          let sign := Bool.xor dx.negative dy.negative
          if dy.significand == 0 then
            dx.significand == 0
          else if dx.significand == 0 then
            false
          else
            let exponentDifference := dx.exponent - dy.exponent
            let value :=
              Internal.Directed.roundRatScaled fmt mode sign dx.significand dy.significand
                exponentDifference
            !rationalRoundingOverflowsScaled fmt mode sign dx.significand dy.significand
                exponentDifference &&
              !isFinite value && !isInf value
      | _, _ =>
          isSNaN x || isSNaN y ||
            (!(isNaN x || isNaN y) && (isInf x && isInf y)) := by
  cases hx : toDyadic? x <;> cases hy : toDyadic? y
  case some.some dx dy =>
    by_cases hxzero : dx.significand = 0 <;>
      by_cases hyzero : dy.significand = 0 <;>
      simp [← Internal.Status.div_eq, Internal.Status.div, hx, hy, hxzero, hyzero,
        Numerics.IEEEStatus.clear]
  all_goals
    simp only [hx, hy, ← Internal.Status.div_eq, Internal.Status.div,
      Internal.Directed.div_eq, outcomeWithInvalid_invalid]

/-! ### Invalid operations from operand classes

In a conventional IEEE format, rounding the exact result of finite operands always delivers a
number, possibly an infinity (`isNaN_add_eq_false_of_isFinite` and its siblings), so the rounding
status of a finite operation never reports invalid. The invalid flag is then determined by the
classes and signs of the operands alone, as IEEE 754-2019 §7.2 specifies; overflow is reported by
the `overflow` flag. -/

/-- A number is finite or an infinity, so the rounding status's invalid test fails on it. -/
private theorem not_isFinite_and_not_isInf_eq_false {fmt : FloatFormat} {x : Model fmt}
    (hnan : isNaN x = false) : (!isFinite x && !isInf x) = false := by
  cases hinf : isInf x
  · simp [isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnan hinf]
  · simp

/-- A decoded finite operand is neither a NaN, a signaling NaN, nor an infinity. -/
private theorem classes_of_toDyadic?_some {fmt : FloatFormat} {x : Model fmt}
    {d : Numerics.Dyadic} (hx : toDyadic? x = some d) :
    isNaN x = false ∧ isSNaN x = false ∧ isInf x = false := by
  have hnan := isNaN_eq_false_of_toDyadic?_some hx
  exact ⟨hnan, isSNaN_eq_false_of_isNaN_eq_false x hnan, isInf_eq_false_of_toDyadic?_some hx⟩

/-- A word without a dyadic decoding is not a zero. -/
private theorem isZero_eq_false_of_toDyadic?_eq_none {fmt : FloatFormat} {x : Model fmt}
    (hx : toDyadic? x = none) : isZero x = false := by
  cases hzero : isZero x
  · rfl
  · rw [toDyadic?_eq_zero_of_isZero_eq_true x hzero] at hx
    contradiction

/--
In a conventional IEEE format, addition raises invalid exactly for a signaling NaN operand or, when
no operand is a NaN, for infinities of opposite signs. Finite operands never raise it, in every
rounding direction.
-/
theorem add_invalid_of_isIEEE
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (x y : Model fmt) (mode : IEEERoundingMode) :
    (add x y (mode := mode) (status := true)).status.invalid =
      (isSNaN x || isSNaN y ||
        (!(isNaN x || isNaN y) && (isInf x && isInf y && signBit x != signBit y))) := by
  rw [add_invalid]
  cases hx : toDyadic? x <;> cases hy : toDyadic? y
  case some.some dx dy =>
    obtain ⟨-, hxs, hxi⟩ := classes_of_toDyadic?_some hx
    obtain ⟨-, hys, -⟩ := classes_of_toDyadic?_some hy
    have hvalue := not_isFinite_and_not_isInf_eq_false <| isNaN_add_eq_false_of_isFinite x y mode
      hfmt (isFinite_eq_true_of_toDyadic?_some hx) (isFinite_eq_true_of_toDyadic?_some hy)
    simp only [Bool.and_assoc, hvalue, Bool.and_false, hxs, hys, hxi, Bool.false_and,
      Bool.and_false, Bool.or_false]
  all_goals rfl

/--
In a conventional IEEE format, multiplication raises invalid exactly for a signaling NaN operand or,
when no operand is a NaN, for an infinity times a zero. Finite operands never raise it, in every
rounding direction.
-/
theorem mul_invalid_of_isIEEE
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (x y : Model fmt) (mode : IEEERoundingMode) :
    (mul x y (mode := mode) (status := true)).status.invalid =
      (isSNaN x || isSNaN y ||
        (!(isNaN x || isNaN y) && ((isInf x && isZero y) || (isInf y && isZero x)))) := by
  rw [mul_invalid]
  cases hx : toDyadic? x <;> cases hy : toDyadic? y
  case some.some dx dy =>
    obtain ⟨-, hxs, hxi⟩ := classes_of_toDyadic?_some hx
    obtain ⟨-, hys, hyi⟩ := classes_of_toDyadic?_some hy
    have hvalue := not_isFinite_and_not_isInf_eq_false <| isNaN_mul_eq_false_of_isFinite x y mode
      hfmt (isFinite_eq_true_of_toDyadic?_some hx) (isFinite_eq_true_of_toDyadic?_some hy)
    simp only [Bool.and_assoc, hvalue, Bool.and_false, hxs, hys, hxi, hyi, Bool.false_and,
      Bool.or_false]
  all_goals rfl

/--
In a conventional IEEE format, fused multiply-add raises invalid exactly as stated by the
exceptional branch of `fma_invalid`: a signaling NaN operand, an infinity times a zero, or, without
a NaN operand, an infinite product and an opposite infinite addend. Finite operands never raise it,
in every rounding direction.

An infinity times a zero raises invalid even when the addend is a quiet NaN. That is FloatLib's
policy, not a requirement of the standard: IEEE 754-2019 Section 7.2 leaves it implementation
defined whether `fma(0, ∞, c)` signals invalid when `c` is a quiet NaN, so another conforming
implementation may leave the flag clear there.
-/
theorem fma_invalid_of_isIEEE
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (x y z : Model fmt)
    (mode : IEEERoundingMode) :
    (fma x y z (mode := mode) (status := true)).status.invalid =
      let hasNaN := isNaN x || isNaN y || isNaN z
      let invalidProduct := (isInf x || isInf y) && (isZero x || isZero y)
      let productIsInf := (isInf x || isInf y) && !(isZero x || isZero y)
      let oppositeInfiniteAddend :=
        productIsInf && isInf z && signBit z != Bool.xor (signBit x) (signBit y)
      isSNaN x || isSNaN y || isSNaN z ||
        invalidProduct || (!hasNaN && oppositeInfiniteAddend) := by
  rw [fma_invalid]
  cases hx : toDyadic? x <;> cases hy : toDyadic? y <;> cases hz : toDyadic? z
  case some.some.some dx dy dz =>
    obtain ⟨-, hxs, hxi⟩ := classes_of_toDyadic?_some hx
    obtain ⟨-, hys, hyi⟩ := classes_of_toDyadic?_some hy
    obtain ⟨-, hzs, hzi⟩ := classes_of_toDyadic?_some hz
    have hvalue := not_isFinite_and_not_isInf_eq_false <| isNaN_fma_eq_false_of_isFinite x y z
      mode hfmt (isFinite_eq_true_of_toDyadic?_some hx) (isFinite_eq_true_of_toDyadic?_some hy)
      (isFinite_eq_true_of_toDyadic?_some hz)
    simp only [Bool.and_assoc, hvalue, Bool.and_false, hxs, hys, hzs, hxi, hyi, hzi,
      Bool.false_and, Bool.or_false]
  all_goals rfl

/--
In a conventional IEEE format, division raises invalid exactly for a signaling NaN operand or, when
no operand is a NaN, for two infinities or two zeros. A finite nonzero dividend over a zero divisor
raises divide-by-zero instead (`div_divideByZero`), and every other quotient of finite operands
rounds to a number, in every rounding direction.
-/
theorem div_invalid_of_isIEEE
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (x y : Model fmt) (mode : IEEERoundingMode) :
    (div x y (mode := mode) (status := true)).status.invalid =
      (isSNaN x || isSNaN y ||
        (!(isNaN x || isNaN y) && ((isInf x && isInf y) || (isZero x && isZero y)))) := by
  rw [div_invalid]
  cases hx : toDyadic? x <;> cases hy : toDyadic? y
  case some.some dx dy =>
    obtain ⟨hxn, hxs, hxi⟩ := classes_of_toDyadic?_some hx
    obtain ⟨hyn, hys, hyi⟩ := classes_of_toDyadic?_some hy
    rw [isZero_eq_beq_zero_of_toDyadic?_some hx, isZero_eq_beq_zero_of_toDyadic?_some hy]
    simp only [hxs, hys, hxn, hyn, hxi, hyi, Bool.false_or, Bool.or_false, Bool.not_false,
      Bool.true_and, Bool.false_and]
    by_cases hdy : dy.significand = 0
    · simp [hdy]
    · have hdy' : (dy.significand == 0) = false := by simpa using hdy
      by_cases hdx : dx.significand = 0
      · simp [hdy', hdx]
      · have hdx' : (dx.significand == 0) = false := by simpa using hdx
        have hvalue := not_isFinite_and_not_isInf_eq_false <|
          Internal.Directed.isNaN_roundRatScaled_eq_false fmt mode (Bool.xor dx.negative dy.negative)
            dx.significand dy.significand (dx.exponent - dy.exponent) hfmt hdy
        simp only [hdy', hdx', Bool.false_eq_true, ite_false, Bool.and_assoc, hvalue,
          Bool.and_false]
  all_goals
    first
      | simp [isZero_eq_false_of_toDyadic?_eq_none hx]
      | simp [isZero_eq_false_of_toDyadic?_eq_none hy]

/-- Division raises divide-by-zero exactly for a finite nonzero numerator over finite zero. -/
theorem div_divideByZero
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    (div x y (mode := mode) (status := true)).status.divideByZero =
      match toDyadic? x, toDyadic? y with
      | some dx, some dy => dx.significand != 0 && dy.significand == 0
      | _, _ => false := by
  cases hx : toDyadic? x <;> cases hy : toDyadic? y
  case some.some dx dy =>
    by_cases hxzero : dx.significand = 0 <;>
      by_cases hyzero : dy.significand = 0 <;>
      simp [← Internal.Status.div_eq, Internal.Status.div, hx, hy, hxzero, hyzero,
        Numerics.IEEEStatus.clear]
  all_goals
    simp only [hx, hy, ← Internal.Status.div_eq, Internal.Status.div,
      Internal.Directed.div_eq, outcomeWithInvalid_divideByZero]

/-! ### Square-root cases

Square root with `status := true` tests the sign bit first and decodes an input with a clear sign
bit once. The next theorems restate its outcome on NaNs, zeros, negative values, `+∞`, and
positive finite values. These cases cover every input.
-/

/-- A NaN delivers the square-root value and raises invalid only when it is signaling. -/
theorem sqrt_status_of_isNaN {fmt : FloatFormat} {x : Model fmt} (mode : IEEERoundingMode)
    (hnan : isNaN x = true) :
    sqrt x (mode := mode) (status := true) =
      outcomeWithInvalid (sqrt x (mode := mode)) (isSNaN x) := by
  cases hsign : signBit x
  · simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsign,
    toDyadic?_eq_none_of_isNaN hnan]
  · simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsign, hnan]

/-- A zero of either sign delivers the square-root value and raises nothing. -/
theorem sqrt_status_of_isZero {fmt : FloatFormat} {x : Model fmt} (mode : IEEERoundingMode)
    (hzero : isZero x = true) :
    sqrt x (mode := mode) (status := true) = outcomeWithInvalid (sqrt x (mode := mode)) false := by
  have hnan :=
    isNaN_eq_false_of_isFinite_eq_true x (isFinite_eq_true_of_isZero_eq_true x hzero)
  cases hsign : signBit x
  · simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsign,
    toDyadic?_eq_zero_of_isZero_eq_true x hzero]
  · simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsign, hnan,
    hzero]

/-- A negative value that is neither a NaN nor a zero, `-∞` included, raises invalid. -/
theorem sqrt_status_of_signBit {fmt : FloatFormat} {x : Model fmt} (mode : IEEERoundingMode)
    (hnan : isNaN x = false) (hzero : isZero x = false) (hsign : signBit x = true) :
    sqrt x (mode := mode) (status := true) = outcomeWithInvalid (sqrt x (mode := mode)) true := by
  simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hnan, hzero,
    hsign]

/-- `+∞` delivers the square-root value and raises nothing. -/
theorem sqrt_status_of_isInf {fmt : FloatFormat} {x : Model fmt} (mode : IEEERoundingMode)
    (hinf : isInf x = true) (hsign : signBit x = false) :
    sqrt x (mode := mode) (status := true) = outcomeWithInvalid (sqrt x (mode := mode)) false := by
  have hsnan := isSNaN_eq_false_of_isNaN_eq_false x (isNaN_eq_false_of_isInf_eq_true x hinf)
  simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsign,
    toDyadic?_eq_none_of_isInf_eq_true hinf, hsnan]

/--
On a finite input with a clear sign, the ternary value compares the squared delivery with the
radicand, the result is inexact exactly when that comparison is not `.eq`, and an inexact result
underflows when its encoding is zero or subnormal or its exact root lies below the underflow
boundary. A zero is delivered exactly, with ternary value `.eq`.
-/
theorem sqrt_status_of_toDyadic {fmt : FloatFormat} {x : Model fmt} {exact : Numerics.Dyadic}
    (mode : IEEERoundingMode) (hx : toDyadic? x = some exact)
    (hsign : exact.negative = false) :
    sqrt x (mode := mode) (status := true) =
      let value := sqrt x (mode := mode)
      let ternary := dyadicSqrtTernary exact value
      let inexact := ternary != .eq
      { value
        status :=
          { underflow :=
              inexact &&
                (isTinyAfterRounding value || dyadicSqrtIsTinyAfterRounding fmt mode exact)
            inexact }
        ternary } := by
  by_cases hzeroTrue : exact.significand = 0
  · have hxZero := isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hx hzeroTrue
    rw [sqrt_status_of_isZero mode hxZero,
      sqrt_of_isZero hxZero]
    have hternary : dyadicSqrtTernary exact x = .eq := by
      simp [dyadicSqrtTernary, hx, cmpDyadic, hzeroTrue]
    simp [outcomeWithInvalid, hternary, Numerics.IEEEStatus.clear]
  have hzero : exact.significand ≠ 0 := hzeroTrue
  have hsignBit : signBit x = false := (sign_eq_signBit_of_toDyadic?_some hx).symm.trans hsign
  have hbeq : (exact.significand == 0) = false := by simpa using hzero
  simp only [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsignBit,
    hx, hbeq, Bool.false_eq_true, ite_false]
  generalize dyadicSqrtTernary exact (sqrt x (mode := mode)) = ternary
  generalize isTinyAfterRounding (sqrt x (mode := mode)) = tiny
  by_cases hformat : fmt.fracWidth + 1 < fmt.exponentBias
  · rw [dyadicSqrtIsTinyAfterRounding_eq_false mode hformat hx hzero]
    cases ternary <;> cases tiny <;> simp [hformat]
  · cases ternary <;> cases tiny <;> simp [hformat]

/-- Square root raises invalid exactly for an sNaN or a negative nonzero non-NaN input. -/
theorem sqrt_invalid {fmt : FloatFormat}
    (x : Model fmt) (mode : IEEERoundingMode) :
    (sqrt x (mode := mode) (status := true)).status.invalid =
      (isSNaN x || (!isNaN x && signBit x && !isZero x)) := by
  by_cases hnan : isNaN x = true
  · rw [sqrt_status_of_isNaN mode hnan]
    simp [hnan]
  · have hnanFalse : isNaN x = false :=
      Bool.eq_false_of_not_eq_true hnan
    have hsnanFalse := isSNaN_eq_false_of_isNaN_eq_false x hnanFalse
    by_cases hzero : isZero x = true
    · rw [sqrt_status_of_isZero mode hzero]
      simp [hsnanFalse, hzero]
    · have hzeroFalse : isZero x = false :=
        Bool.eq_false_of_not_eq_true hzero
      cases hsign : signBit x
      · cases hdecode : toDyadic? x with
        | none => simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq,
          hsign, hdecode, hsnanFalse]
        | some exact =>
            have hexact : (exact.significand == 0) = false := by
              rw [← isZero_eq_beq_zero_of_toDyadic?_some hdecode]
              exact hzeroFalse
            simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsign,
              hdecode, hexact, hsnanFalse]
      · rw [sqrt_status_of_signBit mode hnanFalse hzeroFalse hsign]
        simp [hsnanFalse, hnanFalse, hzeroFalse]

/-- Dividing two finite zeros raises invalid. -/
theorem div_invalid_of_zero_div_zero {fmt : FloatFormat}
    {x y : Model fmt} {dx dy : Numerics.Dyadic} {mode : IEEERoundingMode}
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hxzero : dx.significand = 0) (hyzero : dy.significand = 0) :
    (div x y (mode := mode) (status := true)).status.invalid = true := by
  simp [← Internal.Status.div_eq, Internal.Status.div, hx, hy, hxzero, hyzero]

/-- Dividing a finite nonzero value by a finite zero raises divide-by-zero. -/
theorem div_divideByZero_of_nonzero_div_zero {fmt : FloatFormat}
    {x y : Model fmt} {dx dy : Numerics.Dyadic} {mode : IEEERoundingMode}
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hxnonzero : dx.significand ≠ 0) (hyzero : dy.significand = 0) :
    (div x y (mode := mode) (status := true)).status.divideByZero = true := by
  simp [← Internal.Status.div_eq, Internal.Status.div, hx, hy, hxnonzero, hyzero]

/-- The square root of a negative nonzero non-NaN value raises invalid. -/
theorem sqrt_invalid_of_negative_nonzero {fmt : FloatFormat}
    {x : Model fmt} {mode : IEEERoundingMode}
    (hnan : isNaN x = false) (hnegative : signBit x = true) (hnonzero : isZero x = false) :
    (sqrt x (mode := mode) (status := true)).status.invalid = true := by
  simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hnan, hnegative,
    hnonzero]

/-! ## Square-root inexactness -/

/--
Square root raises `inexact` exactly when its ternary value is not `.eq`, on every input. The
flag is computed from that value on a positive finite input, and the other cases raise neither.
-/
theorem sqrt_inexact_eq_ternary_bne_eq {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) :
    (sqrt x (mode := mode) (status := true)).status.inexact =
      ((sqrt x (mode := mode) (status := true)).ternary != .eq) := by
  rw [← Internal.Status.sqrt_eq]
  unfold Internal.Status.sqrt outcomeWithInvalid
  dsimp only
  split
  · split <;> split <;> rfl
  · split
    · split <;> rfl
    · split
      · rfl
      · rfl

/-- Square-root underflow implies inexactness. -/
theorem sqrt_inexact_of_underflow {fmt : FloatFormat} {x : Model fmt}
    {mode : IEEERoundingMode}
      (h : (sqrt x (mode := mode) (status := true)).status.underflow = true) :
    (sqrt x (mode := mode) (status := true)).status.inexact = true := by
  revert h
  rw [← Internal.Status.sqrt_eq]
  unfold Internal.Status.sqrt outcomeWithInvalid
  dsimp only
  split
  · split <;> split <;> simp [Numerics.IEEEStatus.clear]
  · split
    · split <;> simp [Numerics.IEEEStatus.clear]
    · split
      · simp [Numerics.IEEEStatus.clear]
      · intro h
        split at h <;> simp_all

/--
On a finite input with a clear sign bit, square root raises `inexact` exactly when the delivered
value is not the real square root of the input, in every rounding direction and for every
descriptor. A zero is delivered exactly.

The flag is computed as the ternary value's difference from `.eq`
(`sqrt_inexact_eq_ternary_bne_eq`), so on such an input the ternary value is `.eq`
exactly when the delivered value is the real square root.
-/
theorem sqrt_inexact_iff {fmt : FloatFormat} (mode : IEEERoundingMode)
    {x : Model fmt} (hfinite : isFinite x = true) (hsign : signBit x = false) :
    (sqrt x (mode := mode) (status := true)).status.inexact = true ↔
      toReal (sqrt x (mode := mode) (status := true)).value ≠ Real.sqrt (toReal x) := by
  by_cases hzeroTrue : isZero x = true
  · rw [sqrt_status_of_isZero mode hzeroTrue]
    simp [outcomeWithInvalid, Numerics.IEEEStatus.clear, sqrt_of_isZero hzeroTrue,
      toReal_eq_zero_of_isZero x hzeroTrue]
  have hzero : isZero x = false := Bool.eq_false_iff.mpr hzeroTrue
  have hvalue := toReal_sqrt_nonneg mode hfinite hsign
  have hxpos : 0 < toReal x := by
    have hnonneg := toReal_nonneg_of_signBit_eq_false hsign
    have hne : toReal x ≠ 0 := by
      intro h
      rw [← isZero_eq_true_iff_toReal_eq_zero x hfinite, hzero] at h
      contradiction
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  obtain ⟨exact, hexact⟩ := exists_toDyadic?_of_isFinite hfinite
  have hreal : toReal x = exact.toReal := by
    simp [toReal_eq, hexact]
  have hradicand : 0 ≤ exact.toReal := hreal ▸ hxpos.le
  have hinexact : (sqrt x (mode := mode) (status := true)).status.inexact =
      (dyadicSqrtTernary exact (sqrt x (mode := mode)) != .eq) := by
    rw [sqrt_status_of_toDyadic mode hexact
      ((sign_eq_signBit_of_toDyadic?_some hexact).trans hsign)]
  rw [hinexact, value_sqrt]
  cases hresult : isFinite (sqrt x (mode := mode))
  · rw [dyadicSqrtTernary_of_isFinite_eq_false exact hresult,
      toReal_eq_zero_of_isFinite_eq_false hresult]
    constructor
    · intro _
      exact (Real.sqrt_pos.mpr hxpos).ne
    · intro _
      rfl
  · rw [dyadicSqrtTernary_eq_compare _ hresult hvalue hradicand, ← hreal, bne_iff_ne, ne_eq,
      compare_eq_iff_eq]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
