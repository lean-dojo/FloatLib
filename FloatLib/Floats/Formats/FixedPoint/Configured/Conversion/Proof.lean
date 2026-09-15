/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.FixedPoint.Configured.Proof
public import FloatLib.Floats.ExecFloat.Conversion.Runtime

/-!
# Exact fixed-point conversion proofs

The conversion contract exposes nearest-even coefficient selection, its half-unit error bound,
and the parity of a tie. The complete code and status remain uniquely determined.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.FixedPoint
namespace Conversion

variable {radix : Radix} {fractionalDigits : Nat}

/-- Finite rationals are rounded once to the destination's fixed grid. -/
@[simp, grind =] theorem run_finite (exact : Rat) :
    run (radix := radix) (fractionalDigits := fractionalDigits)
        () (.finite exact) =
      let rounded : ExecFloat.FixedPoint radix fractionalDigits :=
        ExecFloat.FixedPoint.roundRat exact
      .success rounded
        { inexact := ExecFloat.FixedPoint.toRat rounded != exact } :=
  rfl

/-- Integer rounding supplies the coefficient bound and tie rule in the conversion contract. -/
theorem implements_run :
    Quantization.Spec.Implements
      (spec (radix := radix) (fractionalDigits := fractionalDigits))
      (run (radix := radix) (fractionalDigits := fractionalDigits)) := by
  intro context input
  cases input with
  | finite exact =>
      exact ⟨coefficient_roundRat exact,
        roundRatEven_error_le_half (exact * scale radix fractionalDigits),
        roundRatEven_even_of_error_eq_half (exact * scale radix fractionalDigits), rfl⟩
  | infinity negative => rfl
  | exceptional exceptional => rfl

/-- The coefficient and status clauses determine the original complete conversion outcome. -/
theorem spec_iff_eq_run (context : Unit) (input : NumericalValue Rat)
    (outcome : FloatLib.Floats.ExecFloat.ConversionOutcome
      (ExecFloat.FixedPoint radix fractionalDigits)) :
    spec context input outcome ↔ outcome = run context input := by
  constructor
  · cases input with
    | finite exact =>
        cases outcome with
        | success rounded indicators =>
            rintro ⟨hcoefficient, _, _, rfl⟩
            have hrounded : rounded = ExecFloat.FixedPoint.roundRat exact := by
              apply Subtype.ext
              exact congrArg
                (fun stored : Int => (⟨stored⟩ : Formats.FixedPoint.Code radix fractionalDigits))
                hcoefficient
            subst rounded
            rfl
        | failure reason => exact False.elim
    | infinity negative =>
        cases outcome with
        | success rounded indicators => exact False.elim
        | failure reason =>
            rintro rfl
            rfl
    | exceptional exceptional =>
        cases outcome with
        | success rounded indicators => exact False.elim
        | failure reason =>
            rintro rfl
            rfl
  · rintro rfl
    exact implements_run context input

/-- Every admitted finite result is at least as close as every competing grid coefficient. -/
theorem coefficient_nearest_of_spec (exact : Rat)
    (rounded : ExecFloat.FixedPoint radix fractionalDigits)
    (indicators : FloatLib.Floats.ExecFloat.ConversionStatus)
    (h : spec () (.finite exact) (.success rounded indicators)) (candidate : Int) :
    |(coefficient rounded : Rat) - exact * scale radix fractionalDigits| ≤
      |(candidate : Rat) - exact * scale radix fractionalDigits| := by
  rw [h.1]
  exact roundRatEven_nearest _ candidate

/-- The installed decoder exposes the exact stored rational. -/
@[simp, grind =] theorem exactDecoder_run
    (value : ExecFloat.FixedPoint radix fractionalDigits) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value =
      .finite (ExecFloat.FixedPoint.toRat value) :=
  rfl

/-- Infinity is rejected because an exact fixed-point grid has no infinite code. -/
@[simp, grind =] theorem run_infinity (negative : Bool) :
    run (radix := radix) (fractionalDigits := fractionalDigits)
        () (.infinity negative) =
      .failure (.infinity .source negative) :=
  rfl

/-- Exceptional observations are rejected because exact fixed point has no reserved code. -/
@[simp, grind =] theorem run_exceptional (exceptional : ExceptionalValue) :
    run (radix := radix) (fractionalDigits := fractionalDigits)
        () (.exceptional exceptional) =
      .failure (.exceptional .source exceptional) :=
  rfl

end Conversion
end ExecFloat.FixedPoint
end FloatLib.Floats
