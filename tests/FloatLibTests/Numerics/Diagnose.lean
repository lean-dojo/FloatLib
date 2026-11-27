/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Interval.Outward
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Codecs
public import FloatLib.Numerics.Enclosure.Expression.Backends
public import FloatLib.Numerics.Enclosure.Expression.Diagnose
public import FloatLib.Numerics.Enclosure.Expression.Extensions

meta import FloatLib.Numerics.Enclosure.Expression.Backends
meta import FloatLib.Numerics.Enclosure.Expression.Diagnose

/-!
# Diagnoses of interval evaluations

Each example is one evaluation that `Expr.diagnose` explains, decided by the kernel: an overflow
in binary64, a divisor whose enclosure contains zero, a logarithm outside its domain, a registered
call, a variable without an interval, and an operand with an infinite end. One runs as compiled
code. The last examples read the evaluation off a diagnosis, for one expression and for every
expression.
-/

@[expose] public section

namespace FloatLibTests.Numerics.Diagnose

open FloatLib.Numerics FloatLib.Numerics.Interval
open FloatLib.Floats.Formats.BinaryInterchange

/-- Binary64 endpoints, rounded outward by `ExecFloat.Binary.intervalRounding`. -/
def binary64 :=
  Backend.ofRounding (FloatLib.Floats.ExecFloat.Binary.intervalRounding
    (format := FloatFormat.binary64) (plan := .wide))

/-- `2 ^ 1023` is a binary64 number, and `2 ^ 1024` is beyond the largest finite one. That power
has no finite upper end, so the backend rejects it, and the report gives its operand `[2, 2]`. -/
example : ((Expr.unary (.pow 1023) (.const 2)).diagnose binary64 (fun _ => none)).value?.isSome ∧
    ((Expr.unary (.pow 1024) (.const 2)).diagnose binary64 (fun _ => none)).obstruction? =
      some (.rejected (.unary (.pow 1024) (.const 2)) [⟨2, 2⟩]) := by
  decide +kernel

/-- `1 / x` for `x` in `[-1, 1]`, on the grid of quarters: the divisor's enclosure contains zero.
The report decodes the operands from the grid, `1` as `[1, 1]` and `x` as `[-1, 1]`. -/
example : ((Expr.binary .div (.const 1) (.var 0)).diagnose (Backend.binaryGrid { precision := 2 })
    (fun _ => some ⟨-4, 4⟩)).obstruction? =
      some (.rejected (.binary .div (.const 1) (.var 0)) [⟨1, 1⟩, ⟨-1, 1⟩]) := by
  decide +kernel

/-- `log x + 1 / y` with `x` in `[0, 1]` and `y` in `[-1, 1]`: both operations fail, and the report
is the first one in evaluation order, the logarithm of an argument that reaches zero. -/
example : ((Expr.binary .add (.unary .log (.var 0)) (.binary .div (.const 1) (.var 1))).diagnose
    (Backend.rational {}) (fun i => [⟨0, 1⟩, ⟨-1, 1⟩][i]?)).obstruction? =
      some (.rejected (.unary .log (.var 0)) [⟨0, 1⟩]) := by
  decide +kernel

/-- A registered logarithm, `call 0`, rejects `[0, 1]`, and the report is the call with its decoded
argument. When its argument is `1 / x` for `x` in `[-1, 1]`, the division fails first and is the
report. -/
example :
    ((Expr.call 0 [.var 0]).diagnose
      (Backend.withExtensions (Backend.rational {}) {} [Backend.elementaryExtension .log])
      (fun _ => some ⟨0, 1⟩)).obstruction? = some (.rejected (.call 0 [.var 0]) [⟨0, 1⟩]) ∧
    ((Expr.call 0 [.binary .div (.const 1) (.var 0)]).diagnose
      (Backend.withExtensions (Backend.rational {}) {} [Backend.elementaryExtension .log])
      (fun _ => some ⟨-1, 1⟩)).obstruction? =
        some (.rejected (.binary .div (.const 1) (.var 0)) [⟨1, 1⟩, ⟨-1, 1⟩]) := by
  decide +kernel

/-- `x * z` where the environment holds intervals for `x` and `y` only. -/
example : ((Expr.binary .mul (.var 0) (.var 2)).diagnose (Backend.rational {})
    (fun i => [⟨1, 2⟩, ⟨3, 4⟩][i]?)).obstruction? = some (.missingVariable 2) := by
  decide +kernel

/-- `x + 1` for `x` in `[1, ∞]` in binary64: the infinite end has no rational value, so the
backend rejects the sum and the report says that an operand end does not decode. -/
example : ((Expr.binary .add (.var 0) (.const 1)).diagnose binary64
    (fun _ => some ⟨FloatLib.Floats.ExecFloat.Binary.ofModel (Model.posOne FloatFormat.binary64),
      FloatLib.Floats.ExecFloat.Binary.ofModel (Model.posInf FloatFormat.binary64)⟩)).obstruction? =
      some (.undecodable (.binary .add (.var 0) (.const 1))) := by
  decide +kernel

/-- A product with a factor that is exactly zero is zero, here `0 * (1 / x)` on a box that
contains `x = 0`: the diagnosis is the success that `Expr.evalZero?` has. -/
example : (Expr.binary .mul (.const 0) (.binary .div (.const 1) (.var 0))).diagnose
    (Backend.rational {}) (fun _ => some ⟨-1, 1⟩) = .success ⟨0, 0⟩ := by
  decide +kernel

-- The diagnosis has compiled code: the compiler evaluates this one, not the kernel.
#guard ((Expr.binary .div (.const 1) (.var 0)).diagnose (Backend.binaryGrid { precision := 2 })
    (fun _ => some ⟨-4, 4⟩)).obstruction? ==
  some (.rejected (.binary .div (.const 1) (.var 0)) [⟨1, 1⟩, ⟨-1, 1⟩])

/-- A success that the kernel decides is the result of the evaluation
(`Expr.diagnose_eq_success_iff`). -/
example : (Expr.binary .add (.var 0) (.const 1)).evalZero? (Backend.rational {})
    (fun _ => some ⟨0, 1⟩) = some ⟨1, 2⟩ :=
  Expr.diagnose_eq_success_iff.mp (by decide +kernel)

/-- For every expression, backend and environment, an evaluation without a result has a failure
as its diagnosis. -/
example {α : Type} (e : Expr) (B : Backend α) (env : Nat → Option (Interval α))
    (h : e.evalZero? B env = none) : ∃ obstruction, e.diagnose B env = .failure obstruction := by
  cases hd : e.diagnose B env with
  | success I => simp [Expr.diagnose_eq_success_iff.mp hd] at h
  | failure obstruction => exact ⟨obstruction, rfl⟩

end FloatLibTests.Numerics.Diagnose
