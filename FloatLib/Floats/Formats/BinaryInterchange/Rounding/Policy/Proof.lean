/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Runtime

/-!
# Basic policy-rounding facts

This lightweight module contains the facts needed by arithmetic and conversion proofs: deterministic
nearest-even behavior, flush-to-zero behavior, IEEE dispatch, and overflow policy equations.

The independent proof that the general rational policy engine agrees with the directed dyadic
engine lives in `Rounding.Policy.Agreement`. Keeping that larger proof separate prevents ordinary
finite arithmetic and conversion modules from inheriting its directed-semantics dependency graph.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

namespace Policy

/-- Nearest-even quotient rounding does not inspect the entropy source. -/
theorem roundQuot_nearestEven_eq_zero (sign : Bool) (entropy num den : Nat) :
    roundQuot .nearestEven sign entropy num den =
      roundQuot .nearestEven sign 0 num den := by
  rfl

private theorem roundRatGeneralOfDenNeZero_nearestEven_eq_zero
    (fmt : FloatFormat) (entropy : Nat) (sign : Bool) (num den : Nat) (hden : den ≠ 0) :
    roundRatGeneralOfDenNeZero fmt QuantizationPolicy.nearestEven entropy sign num den hden =
      roundRatGeneralOfDenNeZero fmt QuantizationPolicy.nearestEven 0 sign num den hden := by
  unfold roundRatGeneralOfDenNeZero
  simp only [QuantizationPolicy.nearestEven, roundQuot_nearestEven_eq_zero]

/-- Nearest-even dyadic quantization is independent of the entropy argument. -/
theorem roundDyadic_nearestEven_eq_zero (fmt : FloatFormat) (entropy : Nat)
    (value : Numerics.Dyadic) :
    roundDyadic fmt QuantizationPolicy.nearestEven entropy value =
      roundDyadic fmt QuantizationPolicy.nearestEven 0 value :=
  rfl

/-- Nearest-even general quantization is independent of the entropy argument. -/
theorem roundDyadicGeneral_nearestEven_eq_zero (fmt : FloatFormat) (entropy : Nat)
    (value : Numerics.Dyadic) :
    roundDyadicGeneral fmt QuantizationPolicy.nearestEven entropy value =
      roundDyadicGeneral fmt QuantizationPolicy.nearestEven 0 value := by
  unfold roundDyadicGeneral
  cases value.exponent
  · exact roundRatGeneralOfDenNeZero_nearestEven_eq_zero _ _ _ _ _ _
  · exact roundRatGeneralOfDenNeZero_nearestEven_eq_zero _ _ _ _ _ _

/-- Flushing a subnormal result produces the format's corresponding zero. -/
theorem applyUnderflow_flush_of_subnormal (fmt : FloatFormat) (x : Model fmt)
    (hx : Model.isSubnormal x = true) :
    applyUnderflow fmt .flushToZero x = Model.zero fmt (Model.signBit x) := by
  simp [applyUnderflow, hx]

/-- Flush-to-zero leaves every non-subnormal encoding unchanged. -/
theorem applyUnderflow_flush_of_not_subnormal (fmt : FloatFormat) (x : Model fmt)
    (hx : Model.isSubnormal x = false) :
    applyUnderflow fmt .flushToZero x = x := by
  simp [applyUnderflow, hx]

/--
Default rational quantization is the canonical format-parameterized nearest-even rounder.

The entropy argument is irrelevant because nearest-even rounding is deterministic.
-/
theorem roundRat_nearestEven_eq_execFloat (fmt : FloatFormat) (entropy : Nat)
    (sign : Bool) (num den : Nat) (hden : den ≠ 0) :
    roundRat fmt QuantizationPolicy.nearestEven entropy sign num den =
      some (Model.roundRat fmt sign num den) := by
  simp [roundRat, QuantizationPolicy.nearestEven, hden]

/-- Default dyadic quantization is the canonical format-parameterized nearest-even rounder. -/
theorem roundDyadic_nearestEven_eq_execFloat (fmt : FloatFormat) (entropy : Nat)
    (value : Numerics.Dyadic) :
    roundDyadic fmt QuantizationPolicy.nearestEven entropy value =
      Model.roundDyadic fmt value :=
  rfl

/-- Embedding an IEEE direction into the policy vocabulary and back is the identity. -/
@[simp] theorem ieeeRoundingMode?_toRoundingMode (mode : IEEERoundingMode) :
    ieeeRoundingMode? mode.toRoundingMode = some mode := by
  cases mode <;> rfl

/-- A native-overflow, gradual-underflow policy built from an IEEE direction names that direction. -/
@[simp] theorem policyIEEERoundingMode?_toRoundingMode (mode : IEEERoundingMode) :
    policyIEEERoundingMode?
        { rounding := mode.toRoundingMode, overflow := .native, underflow := .gradual } =
      some mode := by
  cases mode <;> rfl

/-- Each embedded `IEEERoundingMode` dispatches to the directed engine. -/
theorem roundDyadic_toRoundingMode_eq_roundDyadicWithRounding (fmt : FloatFormat)
    (mode : IEEERoundingMode) (entropy : Nat) (value : Numerics.Dyadic) :
    roundDyadic fmt { rounding := mode.toRoundingMode, overflow := .native, underflow := .gradual }
        entropy value =
      roundDyadicWithRounding fmt mode value := by
  cases mode <;> rfl

/-- Native policy overflow is the shared directed overflow rule. -/
theorem overflowResult_native_eq_directedOverflow (fmt : FloatFormat) (rounding : RoundingMode)
    (sign : Bool) :
    overflowResult fmt .native rounding sign =
      directedOverflow fmt sign (overflowRoundsMagnitudeUp rounding sign) :=
  rfl

/-- Nearest rounding overflows to the format's native overflow value. -/
theorem overflowResult_native_nearestEven (fmt : FloatFormat) (sign : Bool) :
    overflowResult fmt .native .nearestEven sign = nativeOverflow fmt sign :=
  rfl

/-- Toward-zero rounding saturates to the largest finite magnitude with the requested sign. -/
theorem overflowResult_native_towardZero (fmt : FloatFormat) (sign : Bool) :
    overflowResult fmt .native .towardZero sign = maxFinite fmt sign :=
  rfl

/-- Positive-direction rounding selects native positive overflow and saturates negative overflow. -/
theorem overflowResult_native_towardPositive (fmt : FloatFormat) (sign : Bool) :
    overflowResult fmt .native .towardPositive sign =
      if sign then maxFinite fmt true else nativeOverflow fmt false := by
  cases sign <;> rfl

/-- Negative-direction rounding selects native negative overflow and saturates positive overflow. -/
theorem overflowResult_native_towardNegative (fmt : FloatFormat) (sign : Bool) :
    overflowResult fmt .native .towardNegative sign =
      if sign then nativeOverflow fmt true else maxFinite fmt false := by
  cases sign <;> rfl

/-- Saturating overflow ignores the rounding direction. -/
theorem overflowResult_saturate (fmt : FloatFormat) (rounding : RoundingMode) (sign : Bool) :
    overflowResult fmt .saturate rounding sign = maxFinite fmt sign :=
  rfl

end Policy

end FloatLib.Floats.Formats.BinaryInterchange.Model
