/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Tactic.Roundoff

/-!
# Control flow: a `match` and a branch, case by case

A `match` on index data, on the cases of an inductive type or on a stored input is analyzed
alternative by alternative. These checks read the generated statements in the four modes.

* Forward (`roundoff mixed theorem`, `roundoff theorem`): the reference, the budgets and the
  premise are each the `match` of those of the alternatives, so the statement keeps the shape of
  the program, also inside the step of a loop.
* Closed forward and backward: the statement is the `match` of the statements of the
  alternatives, each with its own premises and, backward, its own perturbations.
* A branch that binds the proof of its condition is a conjunction of the two cases in the closed
  and backward modes, and a branch on an index condition keeps one statement.

The refusals are checked with their messages: a `match` that binds a part of a computed number,
an alternative whose own analysis fails, and overlapping patterns in the closed modes.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffCases

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

local notation "real" => ExecFloat.Binary.toReal

local notation "finite " x => ExecFloat.Binary.isFinite x = true

local notation "u" => Model.unitRoundoffAt format

local notation "η" => Model.underflowErrorAt format

local notation "Ω" => Model.toReal (Model.posMaxFinite format)

/-! ## A match on a size -/

/-- The first entry times `d`, and `d` for the empty vector. -/
def head : (n : Nat) → (Fin n → Value) → Value → Value
  | 0, _, d => d
  | _ + 1, x, d => x 0 * d

/-- Forward, mixed: the reference, the budgets and the premise are matches on the size. -/
roundoff mixed theorem head_mixedError :=
  fun (n : Nat) (x : Fin n → Value) (d : Value) (hformat : format.isIEEE = true) =>
    real (head n x d)

/-- The empty vector: the stored `d`, exact, once `d` is finite. -/
example (x : Fin 0 → Value) (d : Value) (hformat : format.isIEEE = true) (hd : finite d) :
    (finite (head 0 x d)) ∧ MixedError (real (head 0 x d)) (real d) 0 0 :=
  head_mixedError 0 x d hformat hd

/-- A nonempty vector: one rounded product. -/
example (n : Nat) (x : Fin (n + 1) → Value) (d : Value) (hformat : format.isIEEE = true)
    (hx : finite (x 0)) (hd : finite d) (hrange : |real (x 0) * real d| ≤ Ω) :
    (finite (head (n + 1) x d)) ∧
      MixedError (real (head (n + 1) x d)) (real (x 0) * real d) u η :=
  head_mixedError (n + 1) x d hformat ⟨hx, hd, hrange⟩

/-- Forward, absolute. -/
roundoff theorem head_error :=
  fun (n : Nat) (x : Fin n → Value) (d : Value) (hformat : format.isIEEE = true) =>
    real (head n x d)

example (x : Fin 0 → Value) (d : Value) (hformat : format.isIEEE = true) :=
  show _ → |real (head 0 x d) - real d| ≤ _ from head_error 0 x d hformat

/-- Closed forward: the statement is the match of the statements of the alternatives. -/
roundoff closed theorem head_closed :=
  fun (n : Nat) (x : Fin n → Value) (d : Value) (hformat : format.isIEEE = true) =>
    real (head n x d)

example (x : Fin 0 → Value) (d : Value) (hformat : format.isIEEE = true) :
    |real (head 0 x d) - real d| ≤ 0 :=
  head_closed 0 x d hformat

example (n : Nat) (x : Fin (n + 1) → Value) (d : Value) (hformat : format.isIEEE = true)
    (hfinite : finite (x 0 * d)) :
    |real (head (n + 1) x d) - real (x 0) * real d| ≤ |real (x 0)| * u * |real d| + η :=
  head_closed (n + 1) x d hformat hfinite

/-- Backward: each alternative has its own perturbations. -/
roundoff (backward := true) theorem head_backward :=
  fun (n : Nat) (x : Fin n → Value) (d : Value) (hformat : format.isIEEE = true) =>
    real (head n x d)

/-- The empty vector takes no perturbation: the result is the stored `d`. -/
example (x : Fin 0 → Value) (d : Value) (hformat : format.isIEEE = true) :
    real (head 0 x d) = real d :=
  head_backward 0 x d hformat

example (n : Nat) (x : Fin (n + 1) → Value) (d : Value) (hformat : format.isIEEE = true)
    (hfinite : finite (x 0 * d)) :
    ∃ δ, |δ| ≤ u ∧ |real (head (n + 1) x d) - real (x 0) * (1 + δ) * real d| ≤ η :=
  head_backward (n + 1) x d hformat hfinite

/-- The mean of the entries, zero for the empty vector: a loop inside an alternative. -/
def mean : (n : Nat) → (Fin n → Value) → Value
  | 0, _ => 0
  | n + 1, x =>
    Fin.foldl (n + 1) (fun s j => s + x j) 0 / (ExecFloat.Binary.ofRat ((n + 1 : Nat) : ℚ) : Value)

/-- The forward statement of the mean is a match on the size, with the loop in its alternative. -/
roundoff mixed theorem mean_mixedError :=
  fun (n : Nat) (x : Fin n → Value) (hformat : format.isIEEE = true) => real (mean n x)

/-- The empty mean is exactly zero, with no premise. -/
example (x : Fin 0 → Value) (hformat : format.isIEEE = true) :
    (finite (mean 0 x)) ∧ MixedError (real (mean 0 x)) 0 0 0 :=
  mean_mixedError 0 x hformat trivial

/-- The reference of a nonempty mean is the real sum over the real size. -/
example (n : Nat) (x : Fin (n + 1) → Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _
    (List.foldl (fun s j => s + real (x j)) 0 (List.finRange (n + 1)) / ((n + 1 : Nat) : ℝ)) _ _
    from mean_mixedError (n + 1) x hformat

/-- The closed forward statement of the mean. -/
roundoff closed theorem mean_closed :=
  fun (n : Nat) (x : Fin n → Value) (hformat : format.isIEEE = true) => real (mean n x)

example (x : Fin 0 → Value) (hformat : format.isIEEE = true) : |real (mean 0 x) - 0| ≤ 0 :=
  mean_closed 0 x hformat

-- The alternative that divides by the size has no backward form: the size takes no perturbation.
-- The refusal is that of the alternative.
/--
error: roundoff: `real (ExecFloat.Binary.ofRat ↑(n + 1))` has no backward-error form: its rounding
cannot be moved onto the inputs, because `↑(n + 1)` takes no perturbation. Use
`roundoff mixed theorem` for a forward bound, or choose the perturbed inputs with
`(perturb := [...])`.
-/
#guard_msgs (whitespace := lax) in
roundoff (backward := true) theorem mean_backward :=
  fun (n : Nat) (x : Fin n → Value) (hformat : format.isIEEE = true) => real (mean n x)

/-! ## A match on the cases of an inductive type -/

/-- The cases that select a computation; one carries index data. -/
inductive Activation where
  /-- The value itself. -/
  | identity
  /-- Its square. -/
  | square
  /-- The value plus an offset; the slope is index data that the computation ignores. -/
  | affine (slope : Nat)

/-- The computation each case selects. -/
def activate : Activation → Value → Value → Value
  | .identity, x, _ => x
  | .square, x, _ => x * x
  | .affine _, x, b => x + b

/-- Forward, mixed, by the cases of the inductive type. -/
roundoff mixed theorem activate_mixedError :=
  fun (kind : Activation) (x b : Value) (hformat : format.isIEEE = true) =>
    real (activate kind x b)

example (x b : Value) (hformat : format.isIEEE = true) (hx : finite x) :
    (finite (activate .identity x b)) ∧ MixedError (real (activate .identity x b)) (real x) 0 0 :=
  activate_mixedError .identity x b hformat hx

example (x b : Value) (hformat : format.isIEEE = true) (hx : finite x)
    (hrange : |real x * real x| ≤ Ω) :
    (finite (activate .square x b)) ∧
      MixedError (real (activate .square x b)) (real x * real x) u η :=
  activate_mixedError .square x b hformat ⟨hx, hrange⟩

/-- A sum takes no underflow term. -/
example (slope : Nat) (x b : Value) (hformat : format.isIEEE = true) (hx : finite x)
    (hb : finite b) (hrange : |real x + real b| ≤ Ω) :
    (finite (activate (.affine slope) x b)) ∧
      MixedError (real (activate (.affine slope) x b)) (real x + real b) u 0 :=
  activate_mixedError (.affine slope) x b hformat ⟨hx, hb, hrange⟩

/-- Closed forward, by the cases. -/
roundoff closed theorem activate_closed :=
  fun (kind : Activation) (x b : Value) (hformat : format.isIEEE = true) =>
    real (activate kind x b)

example (slope : Nat) (x b : Value) (hformat : format.isIEEE = true)
    (hfinite : finite (x + b)) :
    |real (activate (.affine slope) x b) - (real x + real b)| ≤ |real x| * u + |real b| * u :=
  activate_closed (.affine slope) x b hformat hfinite

/-- Backward, by the cases: two perturbations for the sum, one for the square, none for the
identity. -/
roundoff (backward := true) theorem activate_backward :=
  fun (kind : Activation) (x b : Value) (hformat : format.isIEEE = true) =>
    real (activate kind x b)

example (x b : Value) (hformat : format.isIEEE = true) :
    real (activate .identity x b) = real x :=
  activate_backward .identity x b hformat

example (x b : Value) (hformat : format.isIEEE = true) (hfinite : finite (x * x)) :
    ∃ δ, |δ| ≤ u ∧ |real (activate .square x b) - real x * (1 + δ) * (real x * (1 + δ))| ≤ η :=
  activate_backward .square x b hformat hfinite

example (slope : Nat) (x b : Value) (hformat : format.isIEEE = true)
    (hfinite : finite (x + b)) :
    ∃ δx δb, |δx| ≤ u ∧ |δb| ≤ u ∧
      real (activate (.affine slope) x b) = real x * (1 + δx) + real b * (1 + δb) :=
  activate_backward (.affine slope) x b hformat hfinite

/-- A match inside the step of a loop. -/
def accumulate {n : Nat} (kind : Activation) (x : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => match kind with
    | .identity => s + x j
    | .square => s + x j * x j
    | .affine _ => s) 0

/-- Forward, mixed: the step of the reference and the budgets of a step are matches. -/
roundoff mixed theorem accumulate_mixedError :=
  fun {n : Nat} (kind : Activation) (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    real (accumulate kind x)

/-- The reference folds the match of the real steps: at a case, the real step of that case. -/
example {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _
    (List.foldl (fun reference j => reference + real (x j) * real (x j)) 0 (List.finRange n)) _ _
    from accumulate_mixedError .square x hformat

/-- A case that leaves the accumulator alone keeps the exact zero it starts from. -/
example {n : Nat} (slope : Nat) (x : Fin n → Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _ (List.foldl (fun reference _ => reference) 0 (List.finRange n)) _ _
    from accumulate_mixedError (.affine slope) x hformat

/-- Closed forward: the match is outside the loop, one closed bound for each case. -/
roundoff closed theorem accumulate_closed :=
  fun {n : Nat} (kind : Activation) (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    real (accumulate kind x)

example {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : finite (accumulate .identity x)) :
    |real (accumulate .identity x) - List.foldl (fun s j => s + real (x j)) 0 (List.finRange n)| ≤
      ∑ j, |real (x j)| * ((1 + u) ^ (n - 1 - (j : Nat) + 1) - 1) :=
  accumulate_closed .identity x hformat hfinite

/-! ## A match on a stored input -/

/-- A product with an optional stored weight. -/
def scaleBy (w : Option Value) (x : Value) : Value :=
  match w with
  | some v => v * x
  | none => x

/-- Forward, mixed: the weight a pattern binds is a stored input. -/
roundoff mixed theorem scaleBy_mixedError :=
  fun (w : Option Value) (x : Value) (hformat : format.isIEEE = true) => real (scaleBy w x)

example (v x : Value) (hformat : format.isIEEE = true) (hv : finite v) (hx : finite x)
    (hrange : |real v * real x| ≤ Ω) :
    (finite (scaleBy (some v) x)) ∧ MixedError (real (scaleBy (some v) x)) (real v * real x) u η :=
  scaleBy_mixedError (some v) x hformat ⟨hv, hx, hrange⟩

example (x : Value) (hformat : format.isIEEE = true) (hx : finite x) :
    (finite (scaleBy none x)) ∧ MixedError (real (scaleBy none x)) (real x) 0 0 :=
  scaleBy_mixedError none x hformat hx

/-- Backward: the weight carries the rounding of the product. -/
roundoff (backward := true) theorem scaleBy_backward :=
  fun (w : Option Value) (x : Value) (hformat : format.isIEEE = true) => real (scaleBy w x)

example (v x : Value) (hformat : format.isIEEE = true) (hfinite : finite (v * x)) :
    ∃ δ, |δ| ≤ u ∧ |real (scaleBy (some v) x) - real v * (1 + δ) * real x| ≤ η :=
  scaleBy_backward (some v) x hformat hfinite

/-- The value of an optional input is an input: its exponential is exact as a real value. -/
roundoff mixed theorem exp_get_mixedError :=
  fun (choice : Option Value) (h : choice.isSome) (hformat : format.isIEEE = true) =>
    Real.exp (real (choice.get h))

example (choice : Option Value) (h : choice.isSome) (hformat : format.isIEEE = true) :=
  show MixedError _ (Real.exp (real (choice.get h))) 0 0 from
    exp_get_mixedError choice h hformat

/-! ## Branches -/

/-- A branch that binds the proof of its condition, which an index of the read uses. -/
def first (n : Nat) (x : Fin n → Value) (d : Value) : Value :=
  if h : 0 < n then x ⟨0, h⟩ * d else d

/-- Forward, mixed: one statement whose reference and budgets branch. -/
roundoff mixed theorem first_mixedError :=
  fun (n : Nat) (x : Fin n → Value) (d : Value) (hformat : format.isIEEE = true) =>
    real (first n x d)

example (n : Nat) (x : Fin n → Value) (d : Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _ (if h : 0 < n then real (x ⟨0, h⟩) * real d else real d)
    (if 0 < n then u else 0) (if 0 < n then η else 0) from first_mixedError n x d hformat

/-- Closed forward: the conjunction of the two cases, each under its hypothesis. -/
roundoff closed theorem first_closed :=
  fun (n : Nat) (x : Fin n → Value) (d : Value) (hformat : format.isIEEE = true) =>
    real (first n x d)

example (n : Nat) (x : Fin n → Value) (d : Value) (hformat : format.isIEEE = true) :
    (∀ h : 0 < n, (finite (x ⟨0, h⟩ * d)) →
        |real (first n x d) - real (x ⟨0, h⟩) * real d| ≤ |real (x ⟨0, h⟩)| * u * |real d| + η) ∧
      (¬0 < n → |real (first n x d) - real d| ≤ 0) :=
  first_closed n x d hformat

/-- Backward: the conjunction of the two cases, each with its own perturbations. -/
roundoff (backward := true) theorem first_backward :=
  fun (n : Nat) (x : Fin n → Value) (d : Value) (hformat : format.isIEEE = true) =>
    real (first n x d)

example (n : Nat) (x : Fin n → Value) (d : Value) (hformat : format.isIEEE = true) :
    (∀ h : 0 < n, (finite (x ⟨0, h⟩ * d)) →
        ∃ δ, |δ| ≤ u ∧ |real (first n x d) - real (x ⟨0, h⟩) * (1 + δ) * real d| ≤ η) ∧
      (¬0 < n → real (first n x d) = real d) :=
  first_backward n x d hformat

/-- A branch on an index condition. -/
def scaled (n : Nat) (x d : Value) : Value :=
  if n = 0 then x else x * d

/-- Closed forward: one statement, whose reference and bound branch. -/
roundoff closed theorem scaled_closed :=
  fun (n : Nat) (x d : Value) (hformat : format.isIEEE = true) => real (scaled n x d)

example (n : Nat) (x d : Value) (hformat : format.isIEEE = true) (hfinite : finite (x * d)) :
    |real (scaled n x d) - if n = 0 then real x else real x * real d| ≤
      (if n = 0 then 0 else |real x| * u * |real d|) + if n = 0 then 0 else η :=
  scaled_closed n x d hformat hfinite

/-- Backward: one statement, whose perturbed reference branches. -/
roundoff (backward := true) theorem scaled_backward :=
  fun (n : Nat) (x d : Value) (hformat : format.isIEEE = true) => real (scaled n x d)

example (n : Nat) (x d : Value) (hformat : format.isIEEE = true) (hfinite : finite (x * d)) :
    ∃ δ, |δ| ≤ u ∧
      |real (scaled n x d) - if n = 0 then real x else real x * (real d * (1 + δ))| ≤
        if n = 0 then 0 else η :=
  scaled_backward n x d hformat hfinite

/-! ## A match on a computed value -/

/-- A match on an option computed by a branch: the branch is lifted out of the match, which then
reduces in each side. -/
def computedOption (x y : Value) : Value :=
  match (if ExecFloat.Binary.isNaN x then none else some (x * y)) with
  | some v => v + y
  | none => y

/-- The reference branches on the test and has no match. -/
roundoff mixed theorem computedOption_mixedError :=
  fun (x y : Value) (hformat : format.isIEEE = true) => real (computedOption x y)

example (x y : Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _
    (if ExecFloat.Binary.isNaN x = true then real y else real x * real y + real y) _ _ from
    computedOption_mixedError x y hformat

/-- A match on a test of a computed value binds nothing: it only chooses, and is kept. -/
def chosen (x y : Value) : Value :=
  match ExecFloat.Binary.isNaN (x * y) with
  | true => x
  | false => y

/-- The reference keeps the choice of the program. -/
roundoff mixed theorem chosen_mixedError :=
  fun (x y : Value) (hformat : format.isIEEE = true) => real (chosen x y)

example (x y : Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _ (match ExecFloat.Binary.isNaN (x * y) with
    | true => real x
    | false => real y) _ _ from chosen_mixedError x y hformat

/-- A match that binds the value in a sum computed by a step given as an input. -/
def partOf (step : Value → Value ⊕ Value) (x : Value) : Value :=
  match step x with
  | .inl a => a * x
  | .inr b => b

-- The pattern variables would be parts of a computed value, and the reference would keep them.
/--
error: roundoff: no numerical rule for the `match` on `step x`: it binds parts of a value computed
from numerical values, so the reference would keep them; match on index data or on a stored input
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem partOf_mixedError :=
  fun (step : Value → Value ⊕ Value) (x : Value) (hformat : format.isIEEE = true) =>
    real (partOf step x)

/-- A match that binds the value of an option computed by a step given as an input. -/
def valueOf (step : Value → Option Value) (x : Value) : Value :=
  match step x with
  | some v => v * x
  | none => x

-- A match on a computed option is read as a branch on the option being some, whose value needs
-- the computation of the option.
/--
error: roundoff: no numerical rule for optional producer step x; expose its computation or supply
an explicit bound
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem valueOf_mixedError :=
  fun (step : Value → Option Value) (x : Value) (hformat : format.isIEEE = true) =>
    real (valueOf step x)

/-! ## Overlapping patterns -/

/-- Alternatives whose patterns overlap: a later one holds only where the earlier ones fail. -/
def nested : (n : Nat) → Activation → Value → Value
  | 0, .identity, x => x
  | 0, _, x => x * x
  | _ + 1, .square, x => x + x
  | _ + 1, _, x => x

/-- Forward, mixed: the splitter of the matcher carries the facts that the earlier patterns fail. -/
roundoff mixed theorem nested_mixedError :=
  fun (n : Nat) (kind : Activation) (x : Value) (hformat : format.isIEEE = true) =>
    real (nested n kind x)

example (slope : Nat) (x : Value) (hformat : format.isIEEE = true) (hx : finite x)
    (hrange : |real x * real x| ≤ Ω) :
    (finite (nested 0 (.affine slope) x)) ∧
      MixedError (real (nested 0 (.affine slope) x)) (real x * real x) u η :=
  nested_mixedError 0 (.affine slope) x hformat ⟨hx, hrange⟩

example (n : Nat) (x : Value) (hformat : format.isIEEE = true) (hx : finite x) :
    (finite (nested (n + 1) .identity x)) ∧
      MixedError (real (nested (n + 1) .identity x)) (real x) 0 0 :=
  nested_mixedError (n + 1) .identity x hformat hx

-- The closed modes state each alternative at its patterns alone, where this match is stuck.
/--
error: roundoff: the alternatives of
  match 0, x✝, x with
  | 0, Activation.identity, x => x
  | 0, x, x_1 => x_1 * x_1
  | n.succ, Activation.square, x => x + x
  | n.succ, x, x_1 => x_1
overlap: at the patterns of one alternative the `match` does not reduce, because that alternative
holds only where the earlier ones fail. The closed forward and backward modes state each
alternative at its patterns alone. Use `roundoff mixed theorem` for a forward bound, or write the
alternatives with disjoint patterns.
-/
#guard_msgs (whitespace := lax) in
roundoff closed theorem nested_closed :=
  fun (n : Nat) (kind : Activation) (x : Value) (hformat : format.isIEEE = true) =>
    real (nested n kind x)

end FloatLibTests.Conformance.BinaryInterchange.RoundoffCases
