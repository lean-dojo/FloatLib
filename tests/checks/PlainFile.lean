/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Rounding
import FloatLib.Floats.Formats.BinaryInterchange.Configured
import FloatLib.Tactic.Roundoff

/-!
# A plain file states what a module states

A file that does not start with `module` loads the bodies of the private declarations of its
imports, which a module does not see. `roundoff` unfolds only what a module can unfold, so the
theorem it states has the same premises in both kinds of file. The statements here are among
those of `FloatLibTests.Tactic.Roundoff.GivenFacts`, which is a module, and
`tests/checks/plain-file.sh` elaborates this file as it is and fails on any message.

Each `example` applies the generated theorem to the given facts and states what is left, so a
premise that comes back fails it.
-/

namespace FloatLibTests.Checks.PlainFile

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

variable [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "finite " v => ExecFloat.Binary.isFinite v = true
local notation "real " v => ExecFloat.Binary.toReal v

/-- A square under a name. -/
def squareOf (x : Value) : Value := x * x

/-- Horner's rule under a name. -/
def hornerOf (a b c x : Value) : Value := (a * x + b) * x + c

/-- A scaled vector, as a function of the coordinate. -/
def scaleFn {n : Nat} (seed : Fin n → Value) (factor : Value) : Fin n → Value :=
  fun i => seed i * factor

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

/-- The tactic closes a bound whose hypothesis is written on the named coordinate. -/
theorem scale_error {n : Nat} (seed : Fin n → Value) (factor : Value) (i : Fin n)
    (hformat : format.isIEEE = true) (hresult : finite (scaleFn seed factor i)) :
    |(real (scaleFn seed factor i)) - (real (seed i)) * (real factor)| ≤
      Model.halfUlpAt format ((real (seed i)) * (real factor)) := by
  roundoff

end FloatLibTests.Checks.PlainFile
