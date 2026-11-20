/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.FormProof
public import FloatLib.Numerics.Enclosure.Expression.Constraint

/-!
# Soundness of constraint refutations

`Constraint.Holds` is the real meaning of a constraint at an assignment of its variables, and
`Constraint.refutes_sound` says that a certificate accepted by `Constraint.refutes` excludes every
real assignment of the box: the constraint holds at none of them. The proof is one induction on
the certificate. A leaf is `Expr.checkZero_sound`, and a cut covers its box whatever the cut point.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

variable {functions : Nat → List ℝ → ℝ}

/-- The real meaning of a constraint at an assignment of its variables. -/
def Constraint.Holds (c : Constraint) (values : Nat → ℝ)
    (functions : Nat → List ℝ → ℝ := fun _ _ => 0) : Prop :=
  match c with
  | .fails relation e => ¬ relation.Holds (e.eval values functions)
  | .form true f => f.eval values functions < 0
  | .form false f => f.eval values functions ≤ 0
  | .and a b => a.Holds values functions ∧ b.Holds values functions
  | .or a b => a.Holds values functions ∨ b.Holds values functions

/-- A conjunction holds when both parts hold. -/
theorem Constraint.holds_and {a b : Constraint} {values : Nat → ℝ}
    (ha : a.Holds values functions) (hb : b.Holds values functions) :
    (Constraint.and a b).Holds values functions :=
  ⟨ha, hb⟩

/-- A disjunction holds when its left part holds. -/
theorem Constraint.holds_or_left {a : Constraint} (b : Constraint) {values : Nat → ℝ}
    (ha : a.Holds values functions) : (Constraint.or a b).Holds values functions :=
  Or.inl ha

/-- A disjunction holds when its right part holds. -/
theorem Constraint.holds_or_right (a : Constraint) {b : Constraint} {values : Nat → ℝ}
    (hb : b.Holds values functions) : (Constraint.or a b).Holds values functions :=
  Or.inr hb

/-- `a ≤ b` is the atom `0 ≤ e` for an expression `e` whose value is `b - a`. -/
theorem Constraint.holds_of_le {e : Expr} {values : Nat → ℝ} {a b : ℝ}
    (heq : b - a = e.eval values functions) (h : a ≤ b) :
    (Constraint.fails .negative e).Holds values functions := by
  change ¬ e.eval values functions < 0
  rw [← heq]
  exact not_lt.mpr (sub_nonneg.mpr h)

/-- `a < b` is the atom `0 < e` for an expression `e` whose value is `b - a`. -/
theorem Constraint.holds_of_lt {e : Expr} {values : Nat → ℝ} {a b : ℝ}
    (heq : b - a = e.eval values functions) (h : a < b) :
    (Constraint.fails .nonpositive e).Holds values functions := by
  change ¬ e.eval values functions ≤ 0
  rw [← heq]
  exact not_le.mpr (sub_pos.mpr h)

/-- Anything holds under a false hypothesis: the constraint of a contradictory part. -/
theorem Constraint.holds_of_false (c : Constraint) (values : Nat → ℝ)
    (functions : Nat → List ℝ → ℝ) (h : False) : c.Holds values functions :=
  h.elim

/-- A form whose value is `a - b + μ * (c - d)` is nonpositive when `a ≤ b`, `c ≤ d` and
`0 ≤ μ`. With `μ = 0` it is the form of one comparison. -/
theorem Constraint.holds_form_of_le {f : Form} {values : Nat → ℝ} {a b c d μ : ℝ}
    (heq : a - b + μ * (c - d) = f.eval values functions) (h : a ≤ b) (hμ : 0 ≤ μ)
    (h' : c ≤ d) : (Constraint.form false f).Holds values functions := by
  change f.eval values functions ≤ 0
  rw [← heq]
  exact add_nonpos (sub_nonpos.2 h) (mul_nonpos_of_nonneg_of_nonpos hμ (sub_nonpos.2 h'))

/-- A form whose value is `a - b + μ * (c - d)` is negative when `a < b`, `c ≤ d` and
`0 ≤ μ`. -/
theorem Constraint.holds_form_of_lt {f : Form} {values : Nat → ℝ} {a b c d μ : ℝ}
    (heq : a - b + μ * (c - d) = f.eval values functions) (h : a < b) (hμ : 0 ≤ μ)
    (h' : c ≤ d) : (Constraint.form true f).Holds values functions := by
  change f.eval values functions < 0
  rw [← heq]
  exact add_neg_of_neg_of_nonpos (sub_neg.2 h)
    (mul_nonpos_of_nonneg_of_nonpos hμ (sub_nonpos.2 h'))

/-- A constraint that holds has every conjunct on its paths. -/
theorem Constraint.holds_conjunct {c a : Constraint} {values : Nat → ℝ} {path : List Bool}
    (h : c.conjunct? path = some a) (hc : c.Holds values functions) : a.Holds values functions := by
  induction path generalizing c with
  | nil =>
    cases Option.some.inj h
    exact hc
  | cons side path ih =>
    cases c with
    | and l r =>
      cases side with
      | false => exact ih (by simpa [conjunct?] using h) hc.1
      | true => exact ih (by simpa [conjunct?] using h) hc.2
    | fails relation e => cases side <;> simp [conjunct?] at h
    | form strict f => cases side <;> simp [conjunct?] at h
    | or l r => cases side <;> simp [conjunct?] at h

/-- A nonpositive form with an accepted matrix and a coordinate that cannot vanish on the box
holds at no real assignment of the box. -/
theorem Constraint.not_holds_of_excluded {α : Type*} {B : Backend α} (hB : B.Sound functions)
    {f : Form} {box : Box} (hdefinite : f.definiteOn B true box = true)
    (hexcluded : f.excluded box = true) {values : Nat → ℝ} (hbox : box.ContainsReal values) :
    ¬ (Constraint.form false f).Holds values functions := by
  intro hc
  obtain ⟨s, hs, hsExcluded⟩ := List.any_eq_true.1 hexcluded
  exact Shift.excluded_sound hsExcluded hbox
    (Form.vanishes_of_definiteOn hB hdefinite hbox hc s hs)

/--
The bound of a variable on a sublevel set. If `a ≤ b`, and the form of
`a - b + λ * (e ^ 2 - x ^ 2)` has an accepted matrix on a box and a coordinate that cannot vanish
there, then `x` lies strictly between `-e` and `e` at every real assignment of the box: the form
is positive, so `λ * (x ^ 2 - e ^ 2) < a - b ≤ 0`.
-/
theorem Constraint.abs_lt_of_form {α : Type*} {B : Backend α} (hB : B.Sound functions)
    {f : Form} {box : Box} (hdefinite : f.definiteOn B true box = true)
    (hexcluded : f.excluded box = true) {values : Nat → ℝ} (hbox : box.ContainsReal values)
    {a b x lam e : ℝ} (heq : a - b + lam * (e ^ 2 - x ^ 2) = f.eval values functions)
    (hab : a ≤ b) (hlam : 0 < lam) (he : 0 ≤ e) : -e < x ∧ x < e := by
  have hpos : 0 < f.eval values functions :=
    not_le.1 (not_holds_of_excluded hB hdefinite hexcluded hbox)
  rw [← heq] at hpos
  have hsq : x ^ 2 < e ^ 2 := by
    apply sub_pos.1
    apply (mul_pos_iff_of_pos_left hlam).1
    exact hpos.trans_le (add_le_of_nonpos_left (sub_nonpos.2 hab))
  exact abs_lt.1 (abs_lt_of_sq_lt_sq hsq he)

/--
The bound of a variable on a sublevel set that it touches. If `a ≤ b`, and the form of
`a - b + λ * (e ^ 2 - x ^ 2)` has a positive semidefinite matrix on a box, then `x` lies between
`-e` and `e` at every real assignment of the box: the form is nonnegative, so
`λ * (x ^ 2 - e ^ 2) ≤ a - b ≤ 0`.
-/
theorem Constraint.abs_le_of_form {α : Type*} {B : Backend α} (hB : B.Sound functions)
    {f : Form} {box : Box} (hsemidefinite : f.definiteOn B false box = true)
    {values : Nat → ℝ} (hbox : box.ContainsReal values) {a b x lam e : ℝ}
    (heq : a - b + lam * (e ^ 2 - x ^ 2) = f.eval values functions)
    (hab : a ≤ b) (hlam : 0 < lam) (he : 0 ≤ e) : -e ≤ x ∧ x ≤ e := by
  have hnonneg := Form.nonneg_of_definiteOn hB hsemidefinite hbox
  rw [← heq] at hnonneg
  have hsq : x ^ 2 ≤ e ^ 2 := by
    apply sub_nonneg.1
    apply (mul_nonneg_iff_of_pos_left hlam).1
    exact hnonneg.trans (add_le_of_nonpos_left (sub_nonpos.2 hab))
  exact abs_le.1 (abs_le_of_sq_le_sq hsq he)

/-- Every real assignment of a box belongs to one of the two parts of a cut. -/
theorem Box.containsReal_cut {box : Box} {i : Nat} {point : ℚ} {parts : Box × Box}
    (h : box.cut i point = some parts) {values : Nat → ℝ} (hbox : box.ContainsReal values) :
    parts.1.ContainsReal values ∨ parts.2.ContainsReal values := by
  unfold Box.cut at h
  rw [Kernel.Seq.nth?_eq] at h
  cases hi : box[i]? with
  | none => simp [hi] at h
  | some I =>
    rw [hi] at h
    cases Option.some.inj h
    obtain ⟨hlo, hhi⟩ := (containsReal_some_iff I _).1 (hbox i I hi)
    by_cases hpoint : values i ≤ (point : ℝ)
    · exact Or.inl (Box.containsReal_set hbox ((containsReal_some_iff _ _).2 ⟨hlo, hpoint⟩))
    · exact Or.inr (Box.containsReal_set hbox
        ((containsReal_some_iff _ _).2 ⟨le_of_lt (lt_of_not_ge hpoint), hhi⟩))

/-- Every real assignment of a box belongs to one of its two halves. -/
theorem Box.containsReal_halve {box : Box} {i : Nat} {parts : Box × Box}
    (h : box.halve i = some parts) {values : Nat → ℝ} (hbox : box.ContainsReal values) :
    parts.1.ContainsReal values ∨ parts.2.ContainsReal values := by
  rw [Box.halve_eq] at h
  cases hi : box[i]? with
  | none => simp [hi] at h
  | some I =>
    rw [hi] at h
    exact Box.containsReal_cut h hbox

/--
A constraint with an accepted certificate holds at no real assignment of the box.

The check depends on the backend, the constraint, the certificate and the rational box only. The
real assignment and its membership in the box enter this theorem alone.
-/
theorem Constraint.refutes_sound {α : Type*} {B : Backend α} (hB : B.Sound functions)
    (r : Refutation) {c : Constraint} {box : Box} (h : c.refutes B r box = true)
    {values : Nat → ℝ} (hbox : box.ContainsReal values) : ¬ c.Holds values functions := by
  induction r generalizing c box with
  | atom depth =>
    cases c with
    | fails relation e =>
      exact fun hc => hc (e.checkZero_sound hB (by simpa [refutes] using h) hbox)
    | _ => simp [refutes] at h
  | left r ih =>
    cases c with
    | and a b => exact fun hc => ih (by simpa [refutes] using h) hbox hc.1
    | _ => simp [refutes] at h
  | right r ih =>
    cases c with
    | and a b => exact fun hc => ih (by simpa [refutes] using h) hbox hc.2
    | _ => simp [refutes] at h
  | both l r ihl ihr =>
    cases c with
    | or a b =>
      have hboth : Constraint.refutes B l a box = true ∧ Constraint.refutes B r b box = true := by
        simpa [refutes] using h
      exact fun hc => hc.elim (ihl hboth.1 hbox) (ihr hboth.2 hbox)
    | _ => simp [refutes] at h
  | definite =>
    cases c with
    | form strict f =>
      cases strict with
      | true =>
        exact fun hc => absurd (Form.nonneg_of_definiteOn hB (by simpa [refutes] using h) hbox)
          (not_le.2 hc)
      | false =>
        have hboth : f.definiteOn B true box = true ∧ f.excluded box = true := by
          simpa [refutes] using h
        exact not_holds_of_excluded hB hboth.1 hboth.2 hbox
    | _ => simp [refutes] at h
  | pin path r ih =>
    intro hc
    rw [refutes] at h
    cases hpath : c.conjunct? path with
    | none => simp [hpath] at h
    | some a =>
      cases a with
      | form strict f =>
        cases strict with
        | true => simp [hpath] at h
        | false =>
          have hboth : f.definiteOn B true box = true ∧
              (f.excluded box = true ∨ Constraint.refutes B r c (f.pinned box) = true) := by
            simpa [hpath] using h
          have hform := holds_conjunct hpath hc
          rcases hboth.2 with hexcluded | hrest
          · exact not_holds_of_excluded hB hboth.1 hexcluded hbox hform
          · exact ih hrest (Form.containsReal_pinned hbox
              (Form.vanishes_of_definiteOn hB hboth.1 hbox hform)) hc
      | _ => simp [hpath] at h
  | bisect i l u ihl ihu =>
    cases hparts : box.halve i with
    | none => simp [refutes, hparts] at h
    | some parts =>
      have hboth : Constraint.refutes B l c parts.1 = true ∧
          Constraint.refutes B u c parts.2 = true := by
        simpa [refutes, hparts] using h
      rcases Box.containsReal_halve hparts hbox with hlower | hupper
      · exact ihl hboth.1 hlower
      · exact ihu hboth.2 hupper
  | cut i point l u ihl ihu =>
    cases hparts : box.cut i point with
    | none => simp [refutes, hparts] at h
    | some parts =>
      have hboth : Constraint.refutes B l c parts.1 = true ∧
          Constraint.refutes B u c parts.2 = true := by
        simpa [refutes, hparts] using h
      rcases Box.containsReal_cut hparts hbox with hlower | hupper
      · exact ihl hboth.1 hlower
      · exact ihu hboth.2 hupper

end FloatLib.Numerics.Interval
