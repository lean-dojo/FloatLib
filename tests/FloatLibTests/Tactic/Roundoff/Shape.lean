/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Tactic.Roundoff

/-!
# The shape of a generated bound

`#roundoff_shape` reads a generated mixed bound and says whether it is relative: whether its
absolute part is zero once the underflow allowance is. The two schedules of the target gradient of
cross-entropy are the motivating pair. `1 / (1 + s) - 1` keeps the absolute term
`(2 u + …) * |1 / (1 + s)|`, which does not shrink with the gradient, and the computed gradient is
exactly zero once `s` is below the unit roundoff. `-(s / (1 + s))` is relative. A dot product is
relative when its factors are nonnegative and not otherwise, a softmax weight is relative, and a
log-sum-exp is not, since the logarithm of a sum near one is small.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffShape

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- The target gradient of cross-entropy as `1 / (1 + s) - 1`. -/
roundoff mixed theorem gradient_subtracted :=
  fun (s : Value) (_hformat : format.isIEEE = true) (_hs : ExecFloat.Binary.isFinite s = true)
    (_hpos : 0 < ExecFloat.Binary.toReal s) =>
    ExecFloat.Binary.toReal (1 / (1 + s) - 1)

/-- The same gradient as `-(s / (1 + s))`. -/
roundoff mixed theorem gradient_divided :=
  fun (s : Value) (_hformat : format.isIEEE = true) (_hs : ExecFloat.Binary.isFinite s = true)
    (_hpos : 0 < ExecFloat.Binary.toReal s) =>
    ExecFloat.Binary.toReal (-(s / (1 + s)))

/--
info: `gradient_subtracted`: not relative. Without the underflow allowance its absolute part keeps a term that does not scale with the exact result:
  (1 + Model.unitRoundoffAt format) *
    (((1 + Model.unitRoundoffAt format) * (Model.unitRoundoffAt format / (1 - Model.unitRoundoffAt format)) +
        Model.unitRoundoffAt format) *
      |1 / (1 + ExecFloat.Binary.toReal s)|)
-/
#guard_msgs (info, whitespace := lax) in
#roundoff_shape gradient_subtracted

/--
info: `gradient_divided`: relative. Without the underflow allowance its absolute part is zero, so the bound scales with the exact result.
-/
#guard_msgs (info, whitespace := lax) in
#roundoff_shape gradient_divided

/-- A dot product of factors of any sign. -/
roundoff mixed theorem dot_signed :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s + x j * y j) (0 : Value))

/-- A dot product of nonnegative factors. -/
roundoff mixed theorem dot_nonneg :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true)
    (hx : ∀ j, 0 ≤ ExecFloat.Binary.toReal (x j)) (hy : ∀ j, 0 ≤ ExecFloat.Binary.toReal (y j)) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s + x j * y j) (0 : Value))

/--
info: `dot_signed`: not relative. Without the underflow allowance its absolute part keeps a term that does not scale with the exact result:
  List.foldAbsolute (fun s j => s + x j * y j)
    (fun reference value => reference + ExecFloat.Binary.toReal (x value) * ExecFloat.Binary.toReal (y value))
    (fun accumulator reference relative absolute value => Model.unitRoundoffAt format)
    (fun accumulator reference relative absolute value =>
      (1 + Model.unitRoundoffAt format) *
        (relative * |reference| + absolute +
          Model.unitRoundoffAt format * |ExecFloat.Binary.toReal (x value) * ExecFloat.Binary.toReal (y value)|))
    0 0 0 0 (List.finRange n)
-/
#guard_msgs (info, whitespace := lax) in
#roundoff_shape dot_signed

/--
info: `dot_nonneg`: relative. Without the underflow allowance its absolute part is zero, so the bound scales with the exact result.
-/
#guard_msgs (info, whitespace := lax) in
#roundoff_shape dot_nonneg

/-- The sum of the correctly rounded exponentials of a function on `Fin n`. -/
def expSum {n : Nat} (x : Fin n → Value) : Value :=
  Fin.foldl n (fun s i => s + ExecFloat.Binary.CorrectlyRounded.exp (x i)) 0

/-- A softmax weight: a quotient of positive values. -/
roundoff mixed theorem softmax_weight :=
  fun {n : Nat} (x : Fin (n + 1) → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (ExecFloat.Binary.CorrectlyRounded.exp (x 0) / expSum x)

/--
info: `softmax_weight`: relative. Without the underflow allowance its absolute part is zero, so the bound scales with the exact result.
-/
#guard_msgs (info, whitespace := lax) in
#roundoff_shape softmax_weight

open Lean Elab Command in
-- The shape is also a value that a harness can read.
run_cmd do
  let shape (name : Name) : CommandElabM Bool := do
    let info ← getConstInfo name
    return (← liftTermElabM <| Roundoff.boundShape info.type) matches .relative
  unless (← shape ``gradient_divided) && !(← shape ``gradient_subtracted) &&
      (← shape ``dot_nonneg) && !(← shape ``dot_signed) && (← shape ``softmax_weight) do
    throwError "unexpected shape of a generated bound"

end FloatLibTests.Conformance.BinaryInterchange.RoundoffShape
