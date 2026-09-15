/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
public import FloatLib.Floats.Formats.BinaryInterchange.Model.NumericalSystem
public import FloatLib.Numerics.Core.ExactSemantics

/-!
# Proof-indexed binary-interchange values

Erased proof views refine one executable `Model fmt` by its encoded interpretation or numerical
value. `AtExact` preserves the complete encoded interpretation, `AtValue` records the general
numerical value, and `At` is the finite real specialization. These are refinement views, not
additional runtime representations.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/--
An executable float bundled with a proof of its complete numerical interpretation.

This is a refinement view, not a second floating-point representation.
-/
abbrev AtValue (fmt : FloatFormat) (v : NumericalValue ℝ) :=
  (numericalSystem fmt).At v

/--
An executable float bundled with a proof of its finite real interpretation.

This is a refinement view, not a second floating-point representation.
-/
abbrev At (fmt : FloatFormat) (r : ℝ) :=
  (numericalSystem fmt).AtFinite r

namespace ExactValue

/-- Forget encoding distinctions and retain the general numerical-system interpretation. -/
noncomputable def toNumericalValue : ExactValue → NumericalValue ℝ
  | .finite value => .finite value.toReal
  | .infinity sign => .infinity sign
  | .nan _ _ payload => .exceptional (.nan (some payload))

end ExactValue

/--
Forgetting exact encoding distinctions agrees with the existing numerical-system interpretation.
-/
theorem toNumericalValue_eq_exactValue_toNumericalValue
    {fmt : FloatFormat} (x : Model fmt) :
    toNumericalValue x = (exactValue x).toNumericalValue := by
  cases hdecode : toDyadic? x with
  | some value =>
      have hnan := isNaN_eq_false_of_toDyadic?_some hdecode
      have hinf := isInf_eq_false_of_toDyadic?_some hdecode
      simp [toNumericalValue, exactValue, ExactValue.toNumericalValue, toReal_eq,
        hdecode, hnan, hinf]
  | none =>
      cases hinf : isInf x with
      | true =>
          have hnan := isNaN_eq_false_of_isInf_eq_true x hinf
          simp [toNumericalValue, exactValue, ExactValue.toNumericalValue,
            hdecode, hnan, hinf]
      | false =>
          have hnan : isNaN x = true := by
            cases h : isNaN x with
            | true => rfl
            | false =>
                have hfinite :=
                  isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x h hinf
                obtain ⟨value, hvalue⟩ :=
                  exists_toDyadic?_of_isFinite hfinite
                rw [hdecode] at hvalue
                contradiction
          simp [toNumericalValue, exactValue, ExactValue.toNumericalValue,
            hdecode, hnan, hinf]

/--
The richer exact interpretation of `Model` and its coherent forgetting map.

This capability is used only by proof-facing APIs. Executable kernels continue to call
`exactValue`, field decoders, and arithmetic functions directly.
-/
noncomputable def exactSemantics (fmt : FloatFormat) :
    ExactSemantics (numericalSystem fmt) where
  Exact := ExactValue
  decode := exactValue
  forget := ExactValue.toNumericalValue
  forget_decode x :=
    (toNumericalValue_eq_exactValue_toNumericalValue x).symm

/--
An executable float bundled with a proof of its complete exact interpretation.

This is the generic exact proof view specialized to `Model`. It preserves signed zero and
complete NaN metadata while retaining exactly one runtime `Model fmt`.
-/
abbrev AtExact (fmt : FloatFormat) (v : ExactValue) :=
  (exactSemantics fmt).At v

/--
An IEEE outcome bundled with proofs of both its complete value and its exception status.

The outcome remains the runtime data. Only the two indexing equalities are erased.
-/
abbrev OutcomeAt (fmt : FloatFormat) (v : ExactValue) (status : IEEEStatus) :=
  { outcome : IEEEOutcome fmt //
      exactValue outcome.value = v ∧ outcome.status = status }

end Model
end FloatLib.Floats.Formats.BinaryInterchange
