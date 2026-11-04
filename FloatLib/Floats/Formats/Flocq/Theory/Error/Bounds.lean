/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Core
import Mathlib.Algebra.Order.Algebra

/-!
# Floating-Point Error Bounds

One rounding step in FloatLib’s Flocq-style model has both an absolute and a relative error bound.
The absolute one comes first: `Theory.Rounding.Core` proves a half-ULP bound for every rounding
function satisfying `ValidRndToNearest`. From it we get the relative-error forms, including the
factorization $\operatorname{fl}(x)=x(1+\delta)$. To bound the error of a single rounded operation
such as `round rnd (x + y)`, apply `error_bound_ulp` at the exact expression.

You won't find bounds for dot products, matrix operations, or backward stability here. Those need
a concrete evaluation order and format hypotheses, so they belong with the algorithm in question.

## References

- N. J. Higham, "Accuracy and Stability of Numerical Algorithms", SIAM, 2nd ed., 2002.
- D. Goldberg, "What Every Computer Scientist Should Know About Floating-Point Arithmetic",
  ACM Computing Surveys, 1991.
- IEEE Std 754-2019, "IEEE Standard for Floating-Point Arithmetic" (for the intended meaning of
  rounding modes and ULP terminology).
-/

@[expose] public section


namespace FloatLib.Floats.Formats.Flocq.ErrorBounds

open FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/-! ## Single Operation Error Bounds -/

/--
Relative error for a nonzero exact value.

The proof argument prevents a computation with a nonzero error at exact value zero from being
misreported as having zero relative error. Use an absolute-error statement when the exact value may
vanish.
-/
noncomputable def relativeError (exact computed : ℝ) (_ : exact ≠ 0) : ℝ :=
  abs (computed - exact) / abs exact

/--
Relative error bound for a single `round` step (ULP form).

This is the “divide the half-ULP absolute bound by `|x|`” version of the classic rounding model.
It is often the easiest lemma to use when a proof is naturally phrased in relative terms.
-/
theorem relative_error_round_ulp (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) (hx : x ≠ 0) :
    relativeError x (round (β := β) (fexp := fexp) rnd x) hx ≤
      ulp β fexp x / (2 * abs x) := by
  calc
    relativeError x (round (β := β) (fexp := fexp) rnd x) hx ≤
        (ulp β fexp x / 2) / abs x :=
      div_le_div_of_nonneg_right
        (error_bound_ulp (β := β) (fexp := fexp) (rnd := rnd) x) (abs_nonneg x)
    _ = ulp β fexp x / (2 * abs x) := by rw [div_div]

/--
A relative-error bound gives the multiplicative model: a result `r` within relative error `B` of a
nonzero `x` is `x * (1 + δ)` for some `|δ| ≤ B`.
-/
theorem exists_delta_of_relativeError_le {x r B : ℝ} (hx : x ≠ 0)
    (h : relativeError x r hx ≤ B) : ∃ δ : ℝ, abs δ ≤ B ∧ r = x * (1 + δ) := by
  refine ⟨(r - x) / x, ?_, ?_⟩
  · rw [abs_div]
    exact h
  · field_simp [hx]
    ring

/--
Relative error factorisation for rounding, with a ULP-based bound.

This is the standard model $\operatorname{fl}(x)=x(1+\delta)$, with $|\delta|$ bounded using the
ULP at $x$. Zero rounds to itself, with $\delta = 0$.
-/
theorem round_relative_error_ulp (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) :
    ∃ δ : ℝ,
      abs δ ≤ ulp β fexp x / (2 * abs x) ∧
      round (β := β) (fexp := fexp) rnd x = x * (1 + δ) := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, by simp, by simp [round_zero]⟩
  · exact exists_delta_of_relativeError_le hx (relative_error_round_ulp rnd x hx)

end FloatLib.Floats.Formats.Flocq.ErrorBounds
