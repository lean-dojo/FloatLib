/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Proof.Core

/-!
# Constructors and projections for exact proof views

These definitions attach exact, total, or finite semantic evidence to an executable model and
move between the three proof-indexed views without changing its runtime bits.

The views let later theorems ask for precisely the exceptional-value hypothesis they need instead
of carrying a record of unrelated facts. Constructors and projections pass through the underlying
model value; their semantic proofs are erased.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

namespace AtExact

/-- Attach the exact total interpretation computed from an executable value. -/
@[inline] def ofCode {fmt : FloatFormat} (x : Model fmt) :
    AtExact fmt (exactValue x) :=
  ⟨x, rfl⟩

/-- Attach a known exact finite dyadic interpretation. -/
@[inline] def ofDyadic {fmt : FloatFormat} (x : Model fmt) (value : Numerics.Dyadic)
    (hvalue : toDyadic? x = some value) : AtExact fmt (.finite value) :=
  ⟨x, exactValue_eq_finite_of_toDyadic?_eq_some hvalue⟩

/-- The bundled executable value has its indexed exact interpretation. -/
@[simp] theorem denote {fmt : FloatFormat} {v : ExactValue} (x : AtExact fmt v) :
    exactValue x.1 = v :=
  x.2

/-- Forget exact encoding distinctions while retaining the same executable value. -/
@[inline] def toValue {fmt : FloatFormat} {v : ExactValue}
    (x : AtExact fmt v) : AtValue fmt v.toNumericalValue :=
  ⟨x.1,
    (toNumericalValue_eq_exactValue_toNumericalValue x.1).trans
      (congrArg ExactValue.toNumericalValue (denote x))⟩

/-- A finite exact refinement induces the corresponding real-valued refinement. -/
@[inline] def toAt {fmt : FloatFormat} {value : Numerics.Dyadic}
    (x : AtExact fmt (.finite value)) : At fmt value.toReal :=
  x.toValue

end AtExact

namespace OutcomeAt

/-- Attach the exact value and status computed by an executable IEEE outcome. -/
@[inline] def ofOutcome {fmt : FloatFormat} (outcome : IEEEOutcome fmt) :
    OutcomeAt fmt (exactValue outcome.value) outcome.status :=
  ⟨outcome, rfl, rfl⟩

/-- The bundled outcome's value has its indexed exact interpretation. -/
@[simp] theorem denote {fmt : FloatFormat} {v : ExactValue} {status : IEEEStatus}
    (outcome : OutcomeAt fmt v status) :
    exactValue outcome.1.value = v :=
  outcome.2.1

/-- The bundled outcome has its indexed IEEE exception status. -/
@[simp] theorem status_eq {fmt : FloatFormat} {v : ExactValue} {status : IEEEStatus}
    (outcome : OutcomeAt fmt v status) :
    outcome.1.status = status :=
  outcome.2.2

/-- Project the outcome's value to its exact proof-indexed view. -/
@[inline] def toAtExact {fmt : FloatFormat} {v : ExactValue} {status : IEEEStatus}
    (outcome : OutcomeAt fmt v status) : AtExact fmt v :=
  ⟨outcome.1.value, outcome.2.1⟩

end OutcomeAt

namespace AtValue

/-- Attach the exact total interpretation of an executable value. -/
@[inline] def ofCode {fmt : FloatFormat} (x : Model fmt) :
    AtValue fmt (toNumericalValue x) :=
  ⟨x, rfl⟩

/-- Attach the finite interpretation of an executable value known to be finite. -/
@[inline] def ofFinite {fmt : FloatFormat} (x : Model fmt)
    (hfinite : isFinite x = true) : AtValue fmt (.finite (toReal x)) :=
  ⟨x, toNumericalValue_of_isFinite x hfinite⟩

/-- Attach the signed-infinity interpretation of an executable value known to be infinite. -/
@[inline] def ofInf {fmt : FloatFormat} (x : Model fmt)
    (hinf : isInf x = true) : AtValue fmt (.infinity (signBit x)) :=
  ⟨x, by
    have hnan := isNaN_eq_false_of_isInf_eq_true x hinf
    simp [toNumericalValue, hnan, hinf]⟩

/-- Attach the payload-preserving interpretation of an executable value known to be a NaN. -/
@[inline] def ofNaN {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = true) :
    AtValue fmt (.exceptional (.nan (some (fracField x)))) :=
  ⟨x, by simp [toNumericalValue, hnan]⟩

/-- Positive infinity with its total interpretation in a conventional IEEE format. -/
@[inline] def posInf (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    AtValue fmt (.infinity false) :=
  ⟨Model.posInf fmt, by
    have hsupports :=
      FloatFormat.supportsInfinity_eq_true_of_isIEEE fmt hfmt
    simp [toNumericalValue, isNaN_posInf fmt hsupports,
      isInf_posInf fmt hsupports]⟩

/-- Negative infinity with its total interpretation in a conventional IEEE format. -/
@[inline] def negInf (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    AtValue fmt (.infinity true) :=
  ⟨Model.negInf fmt, by
    have hsupports :=
      FloatFormat.supportsInfinity_eq_true_of_isIEEE fmt hfmt
    simp [toNumericalValue, isNaN_negInf fmt hsupports,
      isInf_negInf fmt hsupports]⟩

/-- The bundled executable value has its indexed total interpretation. -/
@[simp] theorem denote {fmt : FloatFormat} {v : NumericalValue ℝ} (x : AtValue fmt v) :
    toNumericalValue x.1 = v :=
  x.2

/-- The bundled value has the same interpretation through the generic numerical-system adapter. -/
theorem numericalSystem_denote {fmt : FloatFormat} {v : NumericalValue ℝ}
    (x : AtValue fmt v) :
    (numericalSystem fmt).denote x.1 = v :=
  x.2

/-- A finite total refinement is the ordinary real-indexed refinement. -/
@[inline] def toAt {fmt : FloatFormat} {r : ℝ}
    (x : AtValue fmt (.finite r)) : At fmt r :=
  x

end AtValue

end Model
end FloatLib.Floats.Formats.BinaryInterchange
