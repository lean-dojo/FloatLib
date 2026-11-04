/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Rational.Runtime

/-!
# Refinement with separate degree and precision

An enclosure has two sources of error. A wider grid reduces rounding error and more series terms
reduce truncation error, so raising only the degree can leave an enclosure straddling the same
rounding boundary indefinitely.

After a failed check, the search tries twice the degree and one extra working bit. If the interval
width then shrinks by at most a factor of four, the next attempt doubles the working precision
instead (at least one bit) and keeps the degree fixed. Doubling a degree of zero gives zero, so a
search started at degree zero would only ever change the precision. Callers start at a positive
degree, and the certified transcendental kernels promote zero to one. All of this is a heuristic for
choosing work. Acceptance always uses the supplied checker, and the witness theorem below doesn't
assume convergence.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalInterval

namespace Internal

/-- Remember the previous failed width when choosing the next refinement step. -/
@[specialize] def refine {α : Type} (enclose : Nat → Nat → RationalInterval)
    (check : RationalInterval → Option α) (degree precision : Nat)
    (previousWidth : Option ℚ) : Nat → Option α
  | 0 => none
  | steps + 1 =>
      let interval := enclose degree precision
      match check interval with
      | some result => some result
      | none =>
          let width := interval.hi - interval.lo
          if previousWidth.any (fun previous => decide (previous ≤ 4 * width)) then
            refine enclose check degree (max 1 (2 * precision)) none steps
          else
            refine enclose check (2 * degree) (precision + 1) (some width) steps

end Internal

/--
Try at most `steps` enclosures, increasing degree or precision according to the observed width. Each
attempt evaluates `enclose` at its current degree and precision, and `refine` returns the first
value that `check` accepts.

The first attempt uses the supplied degree and precision as given. A successful check returns at
once, and an exhausted budget returns `none`. Since the degree is doubled, it grows only from a
positive start, and with `degree = 0` every attempt uses degree zero.
-/
@[specialize] def refine {α : Type} (enclose : Nat → Nat → RationalInterval)
    (check : RationalInterval → Option α) (degree precision steps : Nat) : Option α :=
  Internal.refine enclose check degree precision none steps

@[simp] theorem refine_zero {α : Type} (enclose : Nat → Nat → RationalInterval)
    (check : RationalInterval → Option α) (degree precision : Nat) :
    refine enclose check degree precision 0 = none := rfl

private theorem exists_of_internal_refine_eq_some {α : Type}
    {enclose : Nat → Nat → RationalInterval} {check : RationalInterval → Option α}
    {degree precision steps : Nat} {previousWidth : Option ℚ} {result : α}
    (hresult : Internal.refine enclose check degree precision previousWidth steps = some result) :
    ∃ degree precision, check (enclose degree precision) = some result := by
  induction steps generalizing degree precision previousWidth with
  | zero => simp [Internal.refine] at hresult
  | succ steps ih =>
      simp only [Internal.refine] at hresult
      split at hresult
      · rename_i value haccept
        exact ⟨degree, precision, Option.some.inj hresult ▸ haccept⟩
      · split at hresult <;> exact ih hresult

/-- Every returned value was accepted from an enclosure at an actual degree and precision. -/
theorem exists_of_refine_eq_some {α : Type}
    {enclose : Nat → Nat → RationalInterval} {check : RationalInterval → Option α}
    {degree precision steps : Nat} {result : α}
    (hresult : refine enclose check degree precision steps = some result) :
    ∃ degree precision, check (enclose degree precision) = some result :=
  exists_of_internal_refine_eq_some hresult

end FloatLib.Numerics.RationalInterval
