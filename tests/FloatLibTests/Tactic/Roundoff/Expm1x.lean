/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Tactic.Roundoff

/-!
# `roundoff` on programs that call `expm1x`

`ExecFloat.Binary.CorrectlyRounded.expm1x` rounds `exp x - 1 - x` once. These checks read the
generated statements: one call, a call on a rounded difference, whose error passes through the
function by its derivative `exp t - 1`, and a relative entropy in the stable form
`∑ p j * expm1x (lq j - lp j)`, a sum of nonnegative terms whose step budget is relative. A call
in another rounding attribute has the contract of that attribute: an exact value at most the
largest finite value, a finite result and the unit roundoff of the attribute. The closed forward
bound keeps the rounding of the function on its value as a whole, so it is relative to
`exp x - 1 - x` and not to the three terms.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffExpm1x

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics
open ExecFloat.Binary.CorrectlyRounded

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

local notation "real" => ExecFloat.Binary.toReal

local notation "finite " x => ExecFloat.Binary.isFinite x = true

local notation "u" => Model.unitRoundoffAt format

local notation "η" => Model.underflowErrorAt format

local notation "Θ" =>
  ((Model.Transcendentals.Certified.overflowThreshold format : ℚ) : ℝ)

local notation "Ω" => Model.toReal (Model.posMaxFinite format)

/-- One call: one rounding of the real function. -/
roundoff mixed theorem call_mixedError :=
  fun (x : Value) (hformat : format.isIEEE = true) => real (expm1x x)

example (x : Value) (hformat : format.isIEEE = true) (hx : finite x)
    (hrange : |Real.exp (real x) - 1 - real x| < Θ) :
    (finite (expm1x x)) ∧ MixedError (real (expm1x x)) (Real.exp (real x) - 1 - real x) u η :=
  call_mixedError x hformat ⟨hx, hrange⟩

/-- The absolute analysis: half a unit in the last place of the real value. -/
roundoff theorem call_error :=
  fun (x : Value) (hformat : format.isIEEE = true) => real (expm1x x)

example (x : Value) (hformat : format.isIEEE = true) :=
  show _ → |real (expm1x x) - (Real.exp (real x) - 1 - real x)| ≤ _ from call_error x hformat

/-- A call on a rounded difference: the rounding of the difference passes through the function
by the slope `exp (|s| + u |s|) - 1`, which is small where the difference is. -/
roundoff mixed theorem difference_mixedError :=
  fun (a b : Value) (hformat : format.isIEEE = true) => real (expm1x (a - b))

example (a b : Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _ (Real.exp (real a - real b) - 1 - (real a - real b)) u
    ((1 + u) * ((Real.exp (|real a - real b| + u * |real a - real b|) - 1) *
      (u * |real a - real b|)) + η) from difference_mixedError a b hformat

/-- A relative entropy in its stable form: a sum of nonnegative terms. -/
def entropy {n : Nat} (p lp lq : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => s + p j * expm1x (lq j - lp j)) 0

/-- The reference is the exact sum, and the sign of the function makes the step budget of the
sum relative to its partial sums. -/
roundoff mixed theorem entropy_mixedError :=
  fun {n : Nat} (p lp lq : Fin n → Value) (hformat : format.isIEEE = true)
      (hp : ∀ j, 0 ≤ real (p j)) =>
    real (entropy p lp lq)

example {n : Nat} (p lp lq : Fin n → Value) (hformat : format.isIEEE = true)
    (hp : ∀ j, 0 ≤ real (p j)) :=
  show _ → _ ∧ MixedError _ (List.foldl (fun reference j => reference +
      real (p j) * (Real.exp (real (lq j) - real (lp j)) - 1 - (real (lq j) - real (lp j))))
    0 (List.finRange n)) _ _ from entropy_mixedError p lp lq hformat hp

/-- The closed forward bound of one term. -/
roundoff closed theorem term_closed :=
  fun (p lp lq : Value) (hformat : format.isIEEE = true) => real (p * expm1x (lq - lp))

/-- The closed forward bound of one call is relative to the value of the function: the rounding
is not spread over the three terms of `exp x - 1 - x`, which cancel near zero. -/
roundoff closed theorem call_closed :=
  fun (x : Value) (hformat : format.isIEEE = true) => real (expm1x x)

example (x : Value) (hformat : format.isIEEE = true) (hx : finite x)
    (hrange : Real.exp (real x) - 1 - real x < Θ) :
    |real (expm1x x) - (Real.exp (real x) - 1 - real x)| ≤
      |Real.exp (real x) - 1 - real x| * u + η :=
  call_closed x hformat ⟨hx, hrange⟩

/-- The closed forward bound at a rounded difference: the error of the argument passes through
the function by its derivative, `(exp (|s| + e) - 1) * e`, and not through its three terms. -/
roundoff closed theorem difference_closed :=
  fun (a b : Value) (hformat : format.isIEEE = true) => real (expm1x (a - b))

example (a b : Value) (hformat : format.isIEEE = true) :=
  show _ → |real (expm1x (a - b)) - (Real.exp (real a - real b) - 1 - (real a - real b))| ≤
      (Real.exp (|real a - real b| + (|real a| * u + |real b| * u)) - 1) *
            (|real a| * u + |real b| * u) +
          (|Real.exp (real a - real b) - 1 - (real a - real b)| +
              (Real.exp (|real a - real b| + (|real a| * u + |real b| * u)) - 1) *
                (|real a| * u + |real b| * u)) * u +
        η
    from difference_closed a b hformat

/-- The same for `expm1`: its closed forward bound is relative to `exp x - 1`. -/
roundoff closed theorem expm1_closed :=
  fun (x : Value) (hformat : format.isIEEE = true) => real (expm1 x)

example (x : Value) (hformat : format.isIEEE = true) :=
  show _ → |real (expm1 x) - (Real.exp (real x) - 1)| ≤ |Real.exp (real x) - 1| * u + η
    from expm1_closed x hformat

/-- A call in another attribute has the contract of that attribute: the exact value is at most
the largest finite value, and the result is finite, with the unit roundoff of the attribute. -/
roundoff mixed theorem down_mixedError :=
  fun (x : Value) (hformat : format.isIEEE = true) => real (expm1x x (mode := .down))

example (x : Value) (hformat : format.isIEEE = true) (hx : finite x)
    (hrange : |Real.exp (real x) - 1 - real x| ≤ Ω) :
    (finite expm1x x (mode := .down)) ∧
      MixedError (real (expm1x x (mode := .down))) (Real.exp (real x) - 1 - real x)
        (Model.unitRoundoffIn format .down) (Model.underflowErrorIn format .down) :=
  down_mixedError x hformat ⟨hx, hrange⟩

/-- An upper bound of the function at a rounded difference: the error of the argument passes
through the function, and the call rounds upward. -/
roundoff mixed theorem up_mixedError :=
  fun (a b : Value) (hformat : format.isIEEE = true) => real (expm1x (a - b) (mode := .up))

example (a b : Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _ (Real.exp (real a - real b) - 1 - (real a - real b))
      (Model.unitRoundoffIn format .up) _ from up_mixedError a b hformat

/-- The attribute as a variable: every one of the six has the contract. -/
roundoff mixed theorem anyAttribute_mixedError :=
  fun (mode : Model.IEEERoundingMode) (x : Value) (hformat : format.isIEEE = true) =>
    real (expm1x x (mode := mode))

example (mode : Model.IEEERoundingMode) (x : Value) (hformat : format.isIEEE = true)
    (hx : finite x) (hrange : |Real.exp (real x) - 1 - real x| ≤ Ω) :
    MixedError (real (expm1x x (mode := mode))) (Real.exp (real x) - 1 - real x)
      (Model.unitRoundoffIn format mode) (Model.underflowErrorIn format mode) :=
  (anyAttribute_mixedError mode x hformat ⟨hx, hrange⟩).2

/-- The absolute analysis of a call rounded away from zero. -/
roundoff theorem away_error :=
  fun (x : Value) (hformat : format.isIEEE = true) => real (expm1x x (mode := .away))

example (x : Value) (hformat : format.isIEEE = true) :=
  show _ → |real (expm1x x (mode := .away)) - (Real.exp (real x) - 1 - real x)| ≤
      0 + (Model.unitRoundoffIn format .away * |Real.exp (real x) - 1 - real x| +
        Model.underflowErrorIn format .away)
    from away_error x hformat

/-- The closed forward bound of a call rounded downward. -/
roundoff closed theorem down_closed :=
  fun (x : Value) (hformat : format.isIEEE = true) => real (expm1x x (mode := .down))

example (x : Value) (hformat : format.isIEEE = true) (hx : finite x)
    (hrange : Real.exp (real x) - 1 - real x ≤ Ω) :
    |real (expm1x x (mode := .down)) - (Real.exp (real x) - 1 - real x)| ≤
      |Real.exp (real x) - 1 - real x| * Model.unitRoundoffIn format .down +
        Model.underflowErrorIn format .down :=
  down_closed x hformat ⟨hx, hrange⟩

/-- The mixed error of a call rounded downward from the theorem of the function, for a result
that is known to be finite: twice the unit roundoff of the format. -/
example (x : Value) (hformat : format.isIEEE = true) (hx : finite x)
    (hfinite : finite (expm1x x (mode := .down)))
    (hrange : Real.exp (real x) - 1 - real x < Θ) :
    MixedError (real (expm1x x (mode := .down))) (Real.exp (real x) - 1 - real x)
      (Model.unitRoundoffIn format .down) (Model.underflowErrorIn format .down) :=
  mixedError_toReal_expm1x hx .down hfinite hrange

end FloatLibTests.Conformance.BinaryInterchange.RoundoffExpm1x
