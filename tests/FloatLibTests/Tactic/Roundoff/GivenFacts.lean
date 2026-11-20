/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Rounding
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Tactic.Roundoff

/-!
# Finiteness facts about named parts of a program

A hypothesis that a named value of the program is finite is the finiteness of the operation that
the name stands for. `roundoff` uses it: the theorem it states has no premise for that operation,
and the tactic closes a goal whose hypothesis is written on the name. The same holds for a fact
written on the operation when the program names it, for a fact written with the function behind
an operator, such as `ExecFloat.mul x y` for `x * y`, and for a fact among the facts of other
operations.

Each `example` applies the generated theorem to the given facts and states what is left, so a
premise that comes back fails it.
-/

@[expose] public section

namespace FloatLibTests.Tactic.Roundoff.GivenFacts

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

variable [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "finite " v => ExecFloat.Binary.isFinite v = true
local notation "real " v => ExecFloat.Binary.toReal v

/-- A square under a name. -/
def squareOf (x : Value) : Value := x * x

/-- A sum under a name. -/
def denomOf (x y : Value) : Value := x + y

/-- Horner's rule under a name. -/
def hornerOf (a b c x : Value) : Value := (a * x + b) * x + c

/-- A scaled vector, as a function of the coordinate. -/
def scaleFn {n : Nat} (seed : Fin n → Value) (factor : Value) : Fin n → Value :=
  fun i => seed i * factor

/-- A sum of the descriptor model under a name. -/
def total (x y : Model format) : Model format := Model.add x y

/-- The fact about the named square is the finiteness of the product. -/
roundoff theorem square_error :=
  fun (x : Value) (hformat : format.isIEEE = true) (h : finite (squareOf x)) => real (squareOf x)

example (x : Value) (hformat : format.isIEEE = true) (h : finite (squareOf x)) :=
  show |(real (squareOf x)) - (real x) * (real x)| ≤ _ from square_error x hformat h

/-- The facts about the two squares and their named sum leave no premise. -/
roundoff theorem squares_error :=
  fun (x y : Value) (hformat : format.isIEEE = true) (hx : finite (squareOf x))
      (hy : finite (squareOf y)) (hs : finite (squareOf x + squareOf y)) =>
    real (squareOf x + squareOf y)

example (x y : Value) (hformat : format.isIEEE = true) (hx : finite (squareOf x))
    (hy : finite (squareOf y)) (hs : finite (squareOf x + squareOf y)) :=
  show |(real (squareOf x + squareOf y)) - ((real x) * (real x) + (real y) * (real y))| ≤ _ from
    squares_error x y hformat hx hy hs

/-- A fact about the whole program is the finiteness of its last operation: the three inner
steps stay premises. -/
roundoff theorem horner_error :=
  fun (a b c x : Value) (hformat : format.isIEEE = true) (h : finite (hornerOf a b c x)) =>
    real (hornerOf a b c x)

example (a b c x : Value) (hformat : format.isIEEE = true) (h : finite (hornerOf a b c x)) :=
  show (finite ((a * x + b) * x)) ∧ (finite (a * x + b)) ∧ (finite (a * x)) →
      |(real (hornerOf a b c x)) - (((real a) * (real x) + (real b)) * (real x) + (real c))| ≤ _
    from horner_error a b c x hformat h

/-- The fact on the operation serves a side condition that is stated on the name. -/
roundoff theorem quotient_error :=
  fun (x y z : Value) (hformat : format.isIEEE = true) (hden : finite (x + y))
      (hq : finite (z / (x + y))) => real (z / denomOf x y)

example (x y z : Value) (hformat : format.isIEEE = true) (hden : finite (x + y))
    (hq : finite (z / (x + y))) :=
  show (real (denomOf x y)) ≠ 0 ∧ ((real x) + (real y)) ≠ 0 →
      |(real (z / denomOf x y)) - (real z) / ((real x) + (real y))| ≤ _ from
    quotient_error x y z hformat hden hq

/-- A fact written with the function behind the operator is the finiteness of the operator. -/
roundoff theorem respelled_error :=
  fun (x y : Value) (hformat : format.isIEEE = true) (h : finite (ExecFloat.mul x y)) =>
    real (x * y)

example (x y : Value) (hformat : format.isIEEE = true) (h : finite (ExecFloat.mul x y)) :=
  show |(real (x * y)) - (real x) * (real y)| ≤ _ from respelled_error x y hformat h

/-- The fact about the named square is found among the facts of two other operations: only the
outer sum stays a premise. -/
roundoff theorem among_error :=
  fun (x y : Value) (hformat : format.isIEEE = true) (hsum : finite (denomOf x y))
      (hsquare : finite (squareOf x)) (hdifference : finite (x - y)) =>
    real (squareOf x + (x - y))

example (x y : Value) (hformat : format.isIEEE = true) (hsum : finite (denomOf x y))
    (hsquare : finite (squareOf x)) (hdifference : finite (x - y)) :=
  show (finite (squareOf x + (x - y))) →
      |(real (squareOf x + (x - y))) - ((real x) * (real x) + ((real x) - (real y)))| ≤ _ from
    among_error x y hformat hsum hsquare hdifference

/-- A fact about a name of another operation serves nothing: the product stays a premise. -/
roundoff theorem other_error :=
  fun (x y : Value) (hformat : format.isIEEE = true) (h : finite (denomOf x y)) => real (x * y)

example (x y : Value) (hformat : format.isIEEE = true) (h : finite (denomOf x y)) :=
  show (finite (x * y)) → |(real (x * y)) - (real x) * (real y)| ≤ _ from
    other_error x y hformat h

/-- The tactic closes a bound whose hypothesis is written on the named coordinate. -/
theorem scale_error {n : Nat} (seed : Fin n → Value) (factor : Value) (i : Fin n)
    (hformat : format.isIEEE = true) (hresult : finite (scaleFn seed factor i)) :
    |(real (scaleFn seed factor i)) - (real (seed i)) * (real factor)| ≤
      Model.halfUlpAt format ((real (seed i)) * (real factor)) := by
  roundoff

/-- The tactic closes a bound whose hypothesis is written with the function behind the
operator. -/
theorem respelled_square_error (x : Value) (hformat : format.isIEEE = true)
    (hresult : finite (ExecFloat.mul x x)) :
    |(real (squareOf x)) - (real x) * (real x)| ≤
      Model.halfUlpAt format ((real x) * (real x)) := by
  roundoff

/-- The same on the descriptor model. -/
theorem total_error (x y : Model format) (hformat : format.isIEEE = true)
    (hresult : Model.isFinite (total x y) = true) :
    |Model.toReal (total x y) - (Model.toReal x + Model.toReal y)| ≤
      Model.halfUlpAt format (Model.toReal x + Model.toReal y) := by
  roundoff

end FloatLibTests.Tactic.Roundoff.GivenFacts
