/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Recommended.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Enclosure.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Recommended.Proof

/-!
# The certified decimal functions return correctly rounded results

For every decimal format and every member of `Function`, a result that `Certified.apply`
returns is valid in the format and finite (`valid_of_apply_eq_some`,
`isFinite_of_apply_eq_some`), and its real value is the nearest-even rounding of the real
function at the real value of the operand (`toReal_of_apply_eq_some`), so it is within half a
unit in the last place of it (`error_le_half_ulp_of_apply_eq_some`). The statements say
nothing about when a result is returned: `none` is always allowed.

All of these follow from three theorems about `unary`, the function of one operand that an
expression gives (`unary_cases`, `valid_of_unary_eq_some`, `isFinite_of_unary_eq_some`,
`toReal_of_unary_eq_some`). `toReal_of_exp_eq_some`, `toReal_of_log_eq_some`,
`toReal_of_compound_eq_some` and `toReal_of_powr_eq_some` are the same statement for `exp`,
`log`, `compound` and `powr`.

The proof is the one for binary formats with the decimal acceptance test: `Function.eval_expr`
shows that the enclosed expression denotes the function, and the enclosure of
`Numerics.Interval` contains its value.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified

open FloatLib.Numerics
open BinaryInterchange.Model.Transcendentals.CorrectlyRounded (Function)

/-- An enclosure that settles encloses the number its expression denotes. -/
theorem exists_enclosure_of_settle_eq_some {f : Format} {expression : Interval.Expr}
    {target : ℝ} (htarget : expression.eval (fun _ => 0) = target)
    {config : Interval.Backend.Config} {result : Datum}
    (h : settle f expression config = some result) :
    ∃ interval : RationalInterval, interval.Contains target ∧
      Enclosure.round? f interval = some result := by
  unfold settle at h
  split at h
  · exact absurd h (by simp)
  · next bounds hbounds =>
    refine ⟨_, ?_, h⟩
    rw [Numerics.Enclosure.BinaryGrid.contains_toRationalInterval, ← htarget]
    exact Interval.Expr.containsReal_eval? expression
      (Interval.Backend.binaryGrid_sound config) (env := fun _ => none) (by simp) hbounds

/--
A result of `unary` came from an enclosure of the expression at the exact value of a valid
operand: for an expression that denotes `real argument` wherever it is given, an interval that
contains `real argument` settled the result.
-/
theorem unary_cases {f : Format} {expression : ℚ → Option (Interval.Expr × Bool)} {real : ℚ → ℝ}
    (hreal : ∀ argument enclosed slow, expression argument = some (enclosed, slow) →
      enclosed.eval (fun _ => 0) = real argument)
    {input result : Datum} (h : unary f expression input = some result) :
    input.Valid f ∧ ∃ argument : ℚ, input.toRat? = some argument ∧
      (expression argument).isSome = true ∧
      ∃ interval : RationalInterval, interval.Contains (real argument) ∧
        Enclosure.round? f interval = some result := by
  unfold unary at h
  split_ifs at h with hvalid
  refine ⟨hvalid, ?_⟩
  split at h
  · exact absurd h (by simp)
  · next argument hargument =>
    split at h
    · exact absurd h (by simp)
    · next enclosed slow hexpression =>
      obtain ⟨config, -, hconfig⟩ := List.exists_of_findSome?_eq_some h
      exact ⟨argument, hargument, by simp [hexpression],
        exists_enclosure_of_settle_eq_some (hreal argument enclosed slow hexpression) hconfig⟩

/-- A result of `unary` is representable in the format. -/
theorem valid_of_unary_eq_some {f : Format} {expression : ℚ → Option (Interval.Expr × Bool)}
    {input result : Datum} (h : unary f expression input = some result) : result.Valid f := by
  obtain ⟨_, _, _, _, _, _, hround⟩ :=
    unary_cases (real := fun argument =>
      ((expression argument).map fun pair => pair.1.eval fun _ => 0).getD 0)
      (fun _ _ _ hexpression => by simp [hexpression]) h
  exact Enclosure.valid_of_round?_eq_some hround

/-- A result of `unary` is finite. -/
theorem isFinite_of_unary_eq_some {f : Format} {expression : ℚ → Option (Interval.Expr × Bool)}
    {input result : Datum} (h : unary f expression input = some result) :
    result.isFinite = true := by
  obtain ⟨_, _, _, _, _, _, hround⟩ :=
    unary_cases (real := fun argument =>
      ((expression argument).map fun pair => pair.1.eval fun _ => 0).getD 0)
      (fun _ _ _ hexpression => by simp [hexpression]) h
  exact Enclosure.isFinite_of_round?_eq_some hround

/--
**A certified function of one operand is correctly rounded.** For an expression that denotes
`real argument` wherever it is given, the real value of a result of `unary` is the nearest-even
rounding into the format of `real` at the real value of the operand.
-/
theorem toReal_of_unary_eq_some {f : Format} {expression : ℚ → Option (Interval.Expr × Bool)}
    {real : ℝ → ℝ}
    (hreal : ∀ argument enclosed slow, expression argument = some (enclosed, slow) →
      enclosed.eval (fun _ => 0) = real argument)
    {input result : Datum} (h : unary f expression input = some result) :
    toReal result = roundAt f (real (toReal input)) := by
  obtain ⟨_, argument, hargument, _, _, hcontains, hround⟩ :=
    unary_cases (real := fun argument => real argument) hreal h
  rw [toReal_of_toRat?_eq_some hargument]
  exact Enclosure.toReal_eq_roundAt_of_round?_eq_some hcontains hround

/-- A zero datum is finite and denotes zero. -/
theorem zero_facts {input : Datum} (hzero : input.isZero = true) :
    input.isFinite = true ∧ toReal input = 0 := by
  cases input with
  | finite s c q =>
      have hc : c = 0 := by simpa [Datum.isZero] using hzero
      simp [hc, Datum.isFinite, toReal, Datum.toRat?]
  | infinity s => simp [Datum.isZero] at hzero
  | nan s t p => simp [Datum.isZero] at hzero

/--
A result of `apply` is a valid zero operand that the function fixes, or a result of `unary` for
the expression of the function on its domain.
-/
theorem apply_cases {f : Format} {function : Function} {input result : Datum}
    (h : apply f function input = some result) :
    (input.Valid f ∧ input.isZero = true ∧ function.vanishesAtZero = true ∧ result = input) ∨
      unary f (fun argument =>
        if function.Domain argument ∧ function.enclosable (2 ^ 16) argument = true then
          some (function.expr argument, function.hasLogarithm)
        else none) input = some result := by
  unfold apply at h
  split_ifs at h with hzero
  · exact .inl ⟨hzero.1, hzero.2.1, hzero.2.2, (Option.some.inj h).symm⟩
  · exact .inr h

/-- The expression that `apply` encloses denotes the function. -/
private theorem eval_of_domain (function : Function) (argument : ℚ) (enclosed : Interval.Expr)
    (slow : Bool)
    (h : (if function.Domain argument ∧ function.enclosable (2 ^ 16) argument = true then
        some (function.expr argument, function.hasLogarithm)
      else none) = some (enclosed, slow)) :
    enclosed.eval (fun _ => 0) = function.real argument := by
  split_ifs at h with hdomain
  cases Option.some.inj h
  exact Function.eval_expr function hdomain.1 _

/-- A returned result is representable in the format. -/
theorem valid_of_apply_eq_some {f : Format} {function : Function} {input result : Datum}
    (h : apply f function input = some result) : result.Valid f := by
  rcases apply_cases h with ⟨hvalid, _, _, rfl⟩ | hunary
  · exact hvalid
  · exact valid_of_unary_eq_some hunary

/-- A returned result is finite. -/
theorem isFinite_of_apply_eq_some {f : Format} {function : Function} {input result : Datum}
    (h : apply f function input = some result) : result.isFinite = true := by
  rcases apply_cases h with ⟨_, hzero, _, rfl⟩ | hunary
  · exact (zero_facts hzero).1
  · exact isFinite_of_unary_eq_some hunary

/--
**A certified decimal function is correctly rounded.** The real value of a returned result is
the nearest-even rounding into the format of the real function at the real value of the
operand.
-/
theorem toReal_of_apply_eq_some {f : Format} {function : Function} {input result : Datum}
    (h : apply f function input = some result) :
    toReal result = roundAt f (function.real (toReal input)) := by
  rcases apply_cases h with ⟨_, hzero, hvanishes, rfl⟩ | hunary
  · rw [(zero_facts hzero).2, Function.real_zero_of_vanishesAtZero hvanishes, roundAt_zero]
  · exact toReal_of_unary_eq_some (real := function.real) (eval_of_domain function) hunary

/-- A returned result is within half a decimal unit in the last place of the real function. -/
theorem error_le_half_ulp_of_apply_eq_some {f : Format} {function : Function}
    {input result : Datum} (h : apply f function input = some result) :
    |toReal result - function.real (toReal input)| ≤
      Flocq.ulp decimalRadix (fexpOf f) (function.real (toReal input)) / 2 := by
  rw [toReal_of_apply_eq_some h]
  exact roundAt_error_le_half_ulp f _

/-- A returned exponential is the nearest-even rounding of the real exponential. -/
theorem toReal_of_exp_eq_some {f : Format} {input result : Datum}
    (h : exp f input = some result) : toReal result = roundAt f (Real.exp (toReal input)) := by
  refine toReal_of_unary_eq_some (real := Real.exp) ?_ h
  intro argument enclosed slow hexpression
  split_ifs at hexpression
  cases Option.some.inj hexpression
  simp [Interval.Expr.eval, Interval.UnaryOp.eval]

/-- A returned logarithm is the nearest-even rounding of the real natural logarithm. -/
theorem toReal_of_log_eq_some {f : Format} {input result : Datum}
    (h : log f input = some result) : toReal result = roundAt f (Real.log (toReal input)) := by
  refine toReal_of_unary_eq_some (real := Real.log) ?_ h
  intro argument enclosed slow hexpression
  split_ifs at hexpression
  cases Option.some.inj hexpression
  simp [Interval.Expr.eval, Interval.UnaryOp.eval]

open BinaryInterchange.Model.Transcendentals.CorrectlyRounded in
/-- A returned `compound` is the nearest-even rounding of `(1 + x) ^ n`. -/
theorem toReal_of_compound_eq_some {f : Format} {input result : Datum} {n : ℤ}
    (h : compound f input n = some result) :
    toReal result = roundAt f ((1 + toReal input) ^ (n : ℝ)) := by
  refine toReal_of_unary_eq_some (real := fun x => (1 + x) ^ (n : ℝ)) ?_ h
  intro rate enclosed slow hexpression
  split_ifs at hexpression with henclosable
  cases Option.some.inj hexpression
  have hbase : (0 : ℚ) < 1 + rate := by
    simpa [powerEnclosable] using (of_decide_eq_true henclosable).1
  rw [eval_powerExpr hbase]
  push_cast
  rfl

open BinaryInterchange.Model.Transcendentals.CorrectlyRounded in
/-- A returned `powr` is the nearest-even rounding of the real power. -/
theorem toReal_of_powr_eq_some {f : Format} {base exponent result : Datum}
    (h : powr f base exponent = some result) :
    toReal result = roundAt f (toReal base ^ toReal exponent) := by
  unfold powr at h
  split_ifs at h
  split at h
  · exact absurd h (by simp)
  · next power hpower =>
    rw [toReal_of_toRat?_eq_some hpower]
    refine toReal_of_unary_eq_some (real := fun x => x ^ (power : ℝ)) ?_ h
    intro argument enclosed slow hexpression
    split_ifs at hexpression with henclosable
    cases Option.some.inj hexpression
    exact eval_powerExpr (by simpa [powerEnclosable] using (of_decide_eq_true henclosable).1) _ _

end FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified
