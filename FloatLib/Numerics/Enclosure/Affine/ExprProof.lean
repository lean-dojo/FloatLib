/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Affine.Expr
public import FloatLib.Numerics.Enclosure.Affine.ModelProof
public import FloatLib.Numerics.Enclosure.Expression.CheckProof

/-!
# Affine ranges contain the values of the expression

The proof goes from the box to the noise box. At a noise assignment `ε`, coordinate `i` of the
box with interval `I` is the point `recenter box ε i`, the center of `I` plus its radius times
`ε i`. A compiled model represents the value of the expression at every assignment that agrees
with `recenter box ε` on the coordinates of the box, for every `ε` with `|ε i| ≤ 1` for all `i`
(`Expr.represents_affineModel?`). For a point `x` of the box, `unitNoise box x` is such a noise
assignment (`abs_unitNoise_le_one`) whose recentered point is `x` (`recenter_unitNoise_eq`), so
the model represents the value at `x` (`Expr.represents_unitNoise`), and `AffineModel.mem_range`
puts that value into the range.

The compiler rejects registered calls, so these statements hold for every table of registered
functions.

## Main results

* `Expr.represents_affineModel?`: a compiled model represents the value of the expression.
* `Expr.represents_unitNoise`: the same at the noise assignment of a point of the box.
* `Expr.containsReal_affineRange?`: a successful affine range contains the value of the
  expression at every real point of the box.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.Affine

open FloatLib.Numerics.Interval (Box Expr containsReal_some_iff)

/-- The point of the box at the noise assignment `ε`: coordinate `i` with interval `I` is
`(I.lo + I.hi) / 2 + (I.hi - I.lo) / 2 * ε i`, and a coordinate that the box does not bound is
`0`. -/
noncomputable def recenter (box : Box) (ε : Nat → ℝ) (i : Nat) : ℝ :=
  match box[i]? with
  | some I => ((I.lo : ℝ) + I.hi) / 2 + ((I.hi : ℝ) - I.lo) / 2 * ε i
  | none => 0

/-- The noise assignment of a point `x`: coordinate `i` with interval `I` is
`(2 * x i - I.lo - I.hi) / (I.hi - I.lo)`, which is `0` when `I` is a point, and a coordinate that
the box does not bound is `0`. -/
noncomputable def unitNoise (box : Box) (x : Nat → ℝ) (i : Nat) : ℝ :=
  match box[i]? with
  | some I => (2 * x i - I.lo - I.hi) / ((I.hi : ℝ) - I.lo)
  | none => 0

/-- At a point of the box, recentering the noise of the point gives back each coordinate that the
box bounds. -/
theorem recenter_unitNoise_eq {box : Box} {x : Nat → ℝ} (hx : box.ContainsReal x) {i : Nat}
    {I : Interval ℚ} (hI : box[i]? = some I) : recenter box (unitNoise box x) i = x i := by
  obtain ⟨hlo, hhi⟩ := (containsReal_some_iff I (x i)).1 (hx i I hI)
  simp only [recenter, unitNoise, hI]
  rcases eq_or_ne ((I.hi : ℝ) - I.lo) 0 with hwidth | hwidth
  · rw [hwidth, div_zero, zero_div, zero_mul, add_zero]
    linarith
  · field_simp
    ring

/-- The noise of a point of the box lies in `[-1, 1]` at every coordinate. -/
theorem abs_unitNoise_le_one {box : Box} {x : Nat → ℝ} (hx : box.ContainsReal x) (i : Nat) :
    |unitNoise box x i| ≤ 1 := by
  cases hI : box[i]? with
  | none => simp [unitNoise, hI]
  | some I =>
    obtain ⟨hlo, hhi⟩ := (containsReal_some_iff I (x i)).1 (hx i I hI)
    simp only [unitNoise, hI]
    rw [abs_div, abs_of_nonneg (sub_nonneg.2 (hlo.trans hhi))]
    exact div_le_one_of_le₀ (abs_le.2 ⟨by linarith, by linarith⟩) (sub_nonneg.2 (hlo.trans hhi))

/-- `variableForm i I` evaluates to the center of `I` plus its radius times `ε i`. -/
theorem eval_variableForm (i : Nat) (I : Interval ℚ) (ε : Nat → ℝ) :
    (variableForm i I).eval ε = ((I.lo : ℝ) + I.hi) / 2 + ((I.hi : ℝ) - I.lo) / 2 * ε i := by
  simp only [variableForm, AffineForm.eval_add, AffineForm.eval_const, AffineForm.eval_scale,
    AffineForm.eval_noise, Kernel.Q.divPow2_eq, Kernel.Q.add_eq, Kernel.Q.sub_eq, pow_one,
    Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat]

/-- A compiled model represents the value of the expression at the noise assignment `ε`, when
`|ε i| ≤ 1` for all `i` and the variable values agree with `recenter box ε` on the coordinates of
the box. -/
theorem Expr.represents_affineModel? {e : Expr} {box : Box} {m : AffineModel}
    (h : Expr.affineModel? e box = some m) {ε : Nat → ℝ} (hε : ∀ i, |ε i| ≤ 1)
    {values : Nat → ℝ} (hvalues : ∀ i I, box[i]? = some I → values i = recenter box ε i)
    (functions : Nat → List ℝ → ℝ) : m.Represents ε (e.eval values functions) := by
  revert m
  refine Expr.rec
    (motive_1 := fun e => ∀ {m}, Expr.affineModel? e box = some m →
      m.Represents ε (e.eval values functions))
    (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ trivial (fun _ _ _ _ => trivial) e
  · intro q m h
    cases Option.some.inj h
    exact AffineModel.represents_const q ε
  · intro i m h
    rw [Expr.affineModel?, Kernel.Seq.nth?_eq] at h
    obtain ⟨I, hI, rfl⟩ := Option.map_eq_some_iff.1 h
    have hvalue : (Expr.var i).eval values functions = (variableForm i I).eval ε := by
      rw [eval_variableForm, Expr.eval, hvalues i I hI, recenter, hI]
    rw [hvalue]
    exact AffineModel.represents_ofAffine _ ε
  · intro op a ha m h
    cases op <;> simp only [Expr.affineModel?, reduceCtorEq] at h
    · obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.1 h
      exact (ha hA).neg
    · obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.1 h
      exact (ha hA).pow _ hε
  · intro op a b ha hb m h
    cases op <;> simp only [Expr.affineModel?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, reduceCtorEq] at h
    · obtain ⟨A, hA, B, hB, rfl⟩ := h
      exact (ha hA).add (hb hB)
    · obtain ⟨A, hA, B, hB, rfl⟩ := h
      exact (ha hA).sub (hb hB)
    · obtain ⟨A, hA, B, hB, rfl⟩ := h
      exact (ha hA).mul (hb hB) hε
  · intro op a b c ha hb hc m h
    cases op
    simp only [Expr.affineModel?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨A, hA, B, hB, C, hC, rfl⟩ := h
    exact ((ha hA).mul (hb hB) hε).add (hc hC)
  · intro index args _ m h
    simp [Expr.affineModel?] at h

/-- A compiled model represents the value of the expression at every real point `x` of the box,
at the noise assignment `unitNoise box x`. -/
theorem Expr.represents_unitNoise {e : Expr} {box : Box} {m : AffineModel}
    (h : Expr.affineModel? e box = some m) {x : Nat → ℝ} (hx : box.ContainsReal x)
    (functions : Nat → List ℝ → ℝ) : m.Represents (unitNoise box x) (e.eval x functions) :=
  Expr.represents_affineModel? h (abs_unitNoise_le_one hx)
    (fun _ _ hJ => (recenter_unitNoise_eq hx hJ).symm) functions

/-- A successful affine range contains the value of the expression at every real point of the
box, for every table of registered functions. -/
theorem Expr.containsReal_affineRange? {e : Expr} {box : Box} {I : Interval ℚ}
    (h : Expr.affineRange? e box = some I) {x : Nat → ℝ} (hx : box.ContainsReal x)
    (functions : Nat → List ℝ → ℝ) : I.ContainsReal some (e.eval x functions) := by
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 h
  exact AffineModel.mem_range (Expr.represents_unitNoise hm hx functions)
    (abs_unitNoise_le_one hx)

end FloatLib.Numerics.Enclosure.Affine
