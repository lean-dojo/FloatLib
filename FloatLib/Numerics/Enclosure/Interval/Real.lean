/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Proof
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Basic.Real.Basic

/-!
# Real meaning of rationally computed endpoint enclosures

Rational endpoint calculations enclose arbitrary real members of an interval, not just rational
samples. The rounding interface still accepts only executable rationals. Its endpoint bounds
are embedded into the reals after the computation, so no real-number rounding oracle is needed.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

variable {α : Type*}

/-- Interpret finite rational endpoints as a closed interval of real numbers. -/
def ContainsReal (decode : α → Option ℚ) (I : Interval α) (x : ℝ) : Prop :=
  I.Contains (fun a => (decode a).map (fun q => (q : ℝ))) x

/-- A successful finite decoder supplies the real endpoint inequalities. -/
theorem containsReal_iff_of_decode? {decode : α → Option ℚ}
    {I : Interval α} {a : Interval ℚ} (ha : I.decode? decode = some a) (x : ℝ) :
    I.ContainsReal decode x ↔ (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ) := by
  rcases (decode?_eq_some_iff decode I a).1 ha with ⟨hlo, hhi⟩
  simp [ContainsReal, Contains, hlo, hhi]

/-- Rational outward rounding encloses every real between the exact rational bounds. -/
theorem containsReal_encloseInterval? (R : OutwardRounding α ℚ)
    {a : Interval ℚ} {I : Interval α} (h : encloseInterval? R a = some I)
    {x : ℝ} (hx : (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)) :
    I.ContainsReal R.decode x := by
  cases hlo : R.enclose? a.lo with
  | none => simp [encloseInterval?, hlo] at h
  | some lo =>
    cases hhi : R.enclose? a.hi with
    | none => simp [encloseInterval?, hlo, hhi] at h
    | some hi =>
      simp [encloseInterval?, hlo, hhi] at h
      subst I
      obtain ⟨a₁, a₂, ha₁, _, ha, _⟩ := R.sound hlo
      obtain ⟨b₁, b₂, _, hb₂, _, hb⟩ := R.sound hhi
      have hal : (a₁ : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast ha
      have hbu : (a.hi : ℝ) ≤ (b₂ : ℝ) := by exact_mod_cast hb
      exact ⟨(a₁ : ℝ), (b₂ : ℝ), by simp [ha₁], by simp [hb₂],
        hal.trans hx.1, hx.2.trans hbu⟩

/-- Lift a rational endpoint enclosure whose interpreted bounds enclose the desired real image. -/
theorem containsReal_liftUnary? (R : OutwardRounding α ℚ)
    (f : Interval ℚ → Interval ℚ) (g : ℝ → ℝ)
    (hf : ∀ (a : Interval ℚ) (x : ℝ), (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ) →
      ((f a).lo : ℝ) ≤ g x ∧ g x ≤ ((f a).hi : ℝ))
    {I K : Interval α} (h : liftUnary? R f I = some K)
    {x : ℝ} (hx : I.ContainsReal R.decode x) : K.ContainsReal R.decode (g x) := by
  cases ha : I.decode? R.decode with
  | none => simp [liftUnary?, ha] at h
  | some a =>
    exact containsReal_encloseInterval? R (by simpa [liftUnary?, ha] using h)
      (hf a x ((containsReal_iff_of_decode? ha x).1 hx))

/-- Lift a rational binary endpoint enclosure to arbitrary real members of its input intervals. -/
theorem containsReal_liftBinary? (R : OutwardRounding α ℚ)
    (f : Interval ℚ → Interval ℚ → Interval ℚ) (g : ℝ → ℝ → ℝ)
    (hf : ∀ (a b : Interval ℚ) (x y : ℝ),
      (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ) → (b.lo : ℝ) ≤ y ∧ y ≤ (b.hi : ℝ) →
      ((f a b).lo : ℝ) ≤ g x y ∧ g x y ≤ ((f a b).hi : ℝ))
    {I J K : Interval α} (h : liftBinary? R f I J = some K)
    {x y : ℝ} (hx : I.ContainsReal R.decode x) (hy : J.ContainsReal R.decode y) :
    K.ContainsReal R.decode (g x y) := by
  cases ha : I.decode? R.decode with
  | none => simp [liftBinary?, ha] at h
  | some a =>
    cases hb : J.decode? R.decode with
    | none => simp [liftBinary?, ha, hb] at h
    | some b =>
      exact containsReal_encloseInterval? R (by simpa [liftBinary?, ha, hb] using h)
        (hf a b x y ((containsReal_iff_of_decode? ha x).1 hx)
          ((containsReal_iff_of_decode? hb y).1 hy))

/-- Successful negation encloses the negative of every represented real. -/
theorem containsReal_neg? (R : OutwardRounding α ℚ) {I K : Interval α}
    (h : neg? R I = some K) {x : ℝ} (hx : I.ContainsReal R.decode x) :
    K.ContainsReal R.decode (-x) := by
  apply containsReal_liftUnary? R _ (- ·) ?_ h hx
  intro a x hx
  simpa using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

/-- Successful rational endpoint addition encloses sums of arbitrary real members. -/
theorem containsReal_add? (R : OutwardRounding α ℚ) {I J K : Interval α}
    (h : add? R I J = some K) {x y : ℝ}
    (hx : I.ContainsReal R.decode x) (hy : J.ContainsReal R.decode y) :
    K.ContainsReal R.decode (x + y) := by
  apply containsReal_liftBinary? R _ (· + ·) ?_ h hx hy
  intro a b x y hx hy
  simpa using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

/-- Successful rational endpoint subtraction encloses differences of arbitrary real members. -/
theorem containsReal_sub? (R : OutwardRounding α ℚ) {I J K : Interval α}
    (h : sub? R I J = some K) {x y : ℝ}
    (hx : I.ContainsReal R.decode x) (hy : J.ContainsReal R.decode y) :
    K.ContainsReal R.decode (x - y) := by
  apply containsReal_liftBinary? R _ (· - ·) ?_ h hx hy
  intro a b x y hx hy
  simpa using And.intro (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

/-- Successful rational four-corner multiplication encloses products of arbitrary real members. -/
theorem containsReal_mul? (R : OutwardRounding α ℚ) {I J K : Interval α}
    (h : mul? R I J = some K) {x y : ℝ}
    (hx : I.ContainsReal R.decode x) (hy : J.ContainsReal R.decode y) :
    K.ContainsReal R.decode (x * y) := by
  apply containsReal_liftBinary? R _ (· * ·) ?_ h hx hy
  intro a b x y hx hy
  simpa [minOfFour, maxOfFour] using
    mul_bounds_Icc (a.lo : ℝ) a.hi b.lo b.hi x y hx hy

/-- Successful rational four-corner division encloses quotients of arbitrary real members. -/
theorem containsReal_div? (R : OutwardRounding α ℚ) {I J K : Interval α}
    (h : div? R I J = some K) {x y : ℝ}
    (hx : I.ContainsReal R.decode x) (hy : J.ContainsReal R.decode y) :
    K.ContainsReal R.decode (x / y) := by
  cases ha : I.decode? R.decode with
  | none => simp [div?, ha] at h
  | some a =>
    cases hb : J.decode? R.decode with
    | none => simp [div?, ha, hb] at h
    | some b =>
      by_cases hzero : b.hi < 0 ∨ 0 < b.lo
      · simp only [div?, ha, hb, ite_eq_left hzero] at h
        apply containsReal_encloseInterval? R h
        have hzeroReal : (b.hi : ℝ) < 0 ∨ 0 < (b.lo : ℝ) := by exact_mod_cast hzero
        simpa [minOfFour, maxOfFour] using
          div_bounds_Icc (a.lo : ℝ) a.hi b.lo b.hi x y
            ((containsReal_iff_of_decode? ha x).1 hx)
            ((containsReal_iff_of_decode? hb y).1 hy) hzeroReal
      · simp [div?, ha, hb, hzero] at h

end FloatLib.Numerics.Interval
