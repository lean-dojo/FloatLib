/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Conversion.Runtime
public import FloatLib.Numerics.Representations.FixedInt.Semantics.Basic
public import FloatLib.Floats.ExecFloat.Conversion.Runtime

/-!
# Bounded fixed-point conversion proofs

The fixed-integer codec theorems connect each conversion policy to its signed coefficient:
checked conversion preserves an in-range coefficient, wrapping takes centered reduction, and
saturation clamps to the signed range. These relations retain the complete outcome and status.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Numerics.Representations

namespace ExecFloat.BoundedFixedPoint
namespace Conversion

variable {radix : Radix} {fractionalDigits width : Nat}

/-- Wrapping delivers the centered remainder of the nearest-even coefficient. -/
theorem coefficient_ofRatWrapping (exact : Rat) :
    coefficient (ofRatWrapping exact :
      ExecFloat.BoundedFixedPoint radix fractionalDigits width) =
        (roundRatEven (exact * Formats.FixedPoint.scale radix fractionalDigits)).bmod
          (2 ^ width) :=
  FixedInt.toInt_ofInt _

/-- An in-range coefficient is preserved, including the sole zero-width coefficient. -/
theorem coefficient_ofCoefficient_of_inRange (stored : Int)
    (h : FixedInt.InRange width stored) :
    coefficient (ofCoefficient stored :
      ExecFloat.BoundedFixedPoint radix fractionalDigits width) = stored := by
  cases width with
  | zero =>
      have hzero : stored = 0 := by
        change 0 ≤ stored ∧ stored ≤ 0 at h
        exact le_antisymm h.2 h.1
      subst stored
      rfl
  | succ width =>
      exact FixedInt.toInt_ofInt_eq_self (Nat.succ_pos width) h

/-- Saturating conversion delivers the clamped nearest-even coefficient at every width. -/
theorem coefficient_ofRatSaturating (exact : Rat) :
    coefficient (ofRatSaturating exact :
      ExecFloat.BoundedFixedPoint radix fractionalDigits width) =
        FixedInt.clamp width
          (roundRatEven (exact * Formats.FixedPoint.scale radix fractionalDigits)) := by
  cases width with
  | zero =>
      simp [coefficient, ofRatSaturating, toCode, ofCode,
        Formats.FixedPoint.Bounded.coefficient, FixedInt.toInt, FixedInt.ofIntSaturating,
        FixedInt.ofInt, FixedInt.clamp, FixedInt.minValue, FixedInt.maxValue,
        Quantization.Saturating.clamp, show (BitVec.intMin 0).toInt = 0 from rfl]
  | succ width =>
      exact FixedInt.toInt_ofIntSaturating (Nat.succ_pos width) _

/-- Finite observations are handled by the selected bounded-overflow policy. -/
@[simp, grind =] theorem run_finite (policy : OverflowPolicy) (exact : Rat) :
    run (radix := radix) (fractionalDigits := fractionalDigits) (width := width)
        policy (.finite exact) =
      quantizeFinite policy exact :=
  rfl

/-- Bounded fixed point has no infinity code. -/
@[simp, grind =] theorem run_infinity (policy : OverflowPolicy) (negative : Bool) :
    run (radix := radix) (fractionalDigits := fractionalDigits) (width := width)
        policy (.infinity negative) =
      .failure (.infinity .source negative) :=
  rfl

/-- Bounded fixed point has no exceptional code. -/
@[simp, grind =] theorem run_exceptional
    (policy : OverflowPolicy) (exceptional : ExceptionalValue) :
    run (radix := radix) (fractionalDigits := fractionalDigits) (width := width)
        policy (.exceptional exceptional) =
      .failure (.exceptional .source exceptional) :=
  rfl

/-- The fixed-integer codec laws establish the independent coefficient and range clauses. -/
theorem implements_run :
    Quantization.Spec.Implements
      (spec (radix := radix) (fractionalDigits := fractionalDigits) (width := width))
      (run (radix := radix) (fractionalDigits := fractionalDigits) (width := width)) := by
  intro policy input
  cases input with
  | finite exact =>
      cases policy with
      | reject =>
          by_cases h : FixedInt.InRange width
              (Formats.FixedPoint.Bounded.coefficientOf radix fractionalDigits exact)
          · simp only [run, quantizeFinite, ofRat?, ite_eq_left h]
            exact ⟨⟨h, coefficient_ofCoefficient_of_inRange _ h⟩, rfl⟩
          · simp only [run, quantizeFinite, ofRat?, ite_eq_right h]
            exact ⟨rfl, h, rfl⟩
      | wrap => exact ⟨coefficient_ofRatWrapping exact, rfl⟩
      | saturate => exact ⟨coefficient_ofRatSaturating exact, rfl⟩
  | infinity negative => rfl
  | exceptional exceptional => rfl

private theorem coefficient_injective :
    Function.Injective (coefficient (radix := radix)
      (fractionalDigits := fractionalDigits) (width := width)) := by
  intro left right h
  apply Subtype.ext
  change left.toCode = right.toCode
  rw [← FixedInt.ofInt_toInt left.toCode, ← FixedInt.ofInt_toInt right.toCode]
  exact congrArg FixedInt.ofInt h

/-- The coefficient policy and full status determine a unique complete outcome. -/
theorem spec_deterministic :
    (spec (radix := radix) (fractionalDigits := fractionalDigits)
      (width := width)).Deterministic := by
  intro policy input left right hleft hright
  cases input with
  | finite exact =>
      cases left with
      | success leftValue leftStatus =>
          cases right with
          | success rightValue rightStatus =>
              obtain ⟨hleft, rfl⟩ := hleft
              obtain ⟨hright, rfl⟩ := hright
              have hcoefficient : coefficient leftValue = coefficient rightValue := by
                cases policy with
                | reject => exact hleft.2.trans hright.2.symm
                | wrap => exact hleft.trans hright.symm
                | saturate => exact hleft.trans hright.symm
              cases coefficient_injective hcoefficient
              rfl
          | failure rightReason =>
              obtain ⟨rfl, hout, _⟩ := hright
              exact (hout hleft.1.1).elim
      | failure leftReason =>
          cases right with
          | success rightValue rightStatus =>
              obtain ⟨rfl, hout, _⟩ := hleft
              exact (hout hright.1.1).elim
          | failure rightReason =>
              exact congrArg ConversionOutcome.failure (hleft.2.2.trans hright.2.2.symm)
  | infinity negative =>
      cases left <;> cases right <;> simp_all [spec]
  | exceptional exceptional =>
      cases left <;> cases right <;> simp_all [spec]

/-- The independent coefficient contract preserves the converter's complete word and status. -/
theorem spec_iff_eq_run (policy : OverflowPolicy) (input : NumericalValue Rat)
    (outcome : FloatLib.Floats.ExecFloat.ConversionOutcome
      (ExecFloat.BoundedFixedPoint radix fractionalDigits width)) :
    spec policy input outcome ↔ outcome = run policy input := by
  constructor
  · intro h
    exact spec_deterministic policy input outcome (run policy input) h
      (implements_run policy input)
  · rintro rfl
    exact implements_run policy input

/-- The installed decoder exposes the exact stored rational. -/
@[simp, grind =] theorem exactDecoder_run
    (value : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value =
      .finite (ExecFloat.BoundedFixedPoint.toRat value) :=
  rfl

/-- Checked conversion reports `outOfRange` exactly when the checked constructor fails. -/
@[grind =] theorem run_reject_eq (exact : Rat) :
    run (radix := radix) (fractionalDigits := fractionalDigits) (width := width)
        .reject (.finite exact) =
      match ExecFloat.BoundedFixedPoint.ofRat? exact with
      | some rounded => .success rounded (finiteStatus .reject exact rounded)
      | none => .failure .outOfRange :=
  rfl

end Conversion
end ExecFloat.BoundedFixedPoint
end FloatLib.Floats
