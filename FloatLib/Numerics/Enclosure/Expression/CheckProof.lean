/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Check
public import FloatLib.Numerics.Enclosure.Expression.Real

/-!
# Certified inequality checks and adaptive subdivision

Rational input boxes denote sets of arbitrary real assignments. Endpoint enclosure preserves
these sets, and backend soundness carries their values through expression evaluation. A successful
upper-bound test therefore proves the requested inequality throughout a box.

Every midpoint split covers its parent. Induction on the subdivision depth combines successful
checks of both children without assuming that any sampled point represents the entire box.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- Real meaning of the two relations accepted by the executable checker. -/
def Relation.Holds (relation : Relation) (value : ℝ) : Prop :=
  match relation with
  | .nonpositive => value ≤ 0
  | .negative => value < 0

/-- A real assignment respects every supplied rational coordinate interval. -/
def Box.ContainsReal (box : Box) (values : Nat → ℝ) : Prop :=
  ∀ (i : Nat) (I : Interval ℚ), box[i]? = some I → I.ContainsReal some (values i)

/-- An empty box places no restrictions on the real environment. -/
@[simp]
theorem Box.containsReal_nil (values : Nat → ℝ) : Box.ContainsReal [] values := by
  intro i I h
  simp at h

/-- Separate the first coordinate's bounds from the shifted tail environment. -/
@[simp]
theorem Box.containsReal_cons_iff (I : Interval ℚ) (box : Box) (values : Nat → ℝ) :
    Box.ContainsReal (I :: box) values ↔
      ((I.lo : ℝ) ≤ values 0 ∧ values 0 ≤ (I.hi : ℝ)) ∧
        box.ContainsReal (fun i => values (i + 1)) := by
  constructor
  · intro h
    refine ⟨(containsReal_some_iff I _).1 (h 0 I rfl), ?_⟩
    intro i J hJ
    exact h (i + 1) J (by simpa using hJ)
  · rintro ⟨head, tail⟩ i J hJ
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hJ
      subst J
      exact (containsReal_some_iff I _).2 head
    | succ i => exact tail i J (by simpa using hJ)

/-- Build box membership one coordinate at a time from real bounds. -/
theorem Box.containsReal_cons {I : Interval ℚ} {box : Box} {values : Nat → ℝ}
    (head : (I.lo : ℝ) ≤ values 0 ∧ values 0 ≤ (I.hi : ℝ))
    (tail : box.ContainsReal (fun i => values (i + 1))) :
    Box.ContainsReal (I :: box) values :=
  (Box.containsReal_cons_iff I box values).2 ⟨head, tail⟩

/-- Enclosing rational endpoints contains every real between them. -/
theorem Backend.containsReal_encloseInterval? {α : Type*} {B : Backend α}
    (hB : B.Sound) {I : Interval ℚ} {J : Interval α}
    (h : B.encloseInterval? I = some J) {x : ℝ} (hx : I.ContainsReal some x) :
    J.ContainsReal B.decode x := by
  cases hlo : B.const? I.lo with
  | none => simp [Backend.encloseInterval?, hlo] at h
  | some lower =>
    cases hhi : B.const? I.hi with
    | none => simp [Backend.encloseInterval?, hlo, hhi] at h
    | some upper =>
      simp [Backend.encloseInterval?, hlo, hhi] at h
      subst J
      obtain ⟨a, _, ha, _, hax, _⟩ := hB.const hlo
      obtain ⟨_, b, _, hb, _, hxb⟩ := hB.const hhi
      obtain ⟨hlo', hhi'⟩ := (containsReal_some_iff I x).1 hx
      exact ⟨a, b, ha, hb, hax.trans hlo', hhi'.trans hxb⟩

/-- Successful box enclosure supplies sound values for every coordinate in the interval list. -/
theorem Box.containsReal_enclose? {α : Type*} {B : Backend α} (hB : B.Sound)
    {box : Box} {intervals : List (Interval α)} (h : box.enclose? B = some intervals)
    {values : Nat → ℝ} (hbox : box.ContainsReal values) :
    ∀ (i : Nat) (I : Interval α),
      intervals[i]? = some I → I.ContainsReal B.decode (values i) := by
  induction box generalizing intervals values with
  | nil =>
    simp [Box.enclose?] at h
    subst intervals
    intro i I hI
    simp at hI
  | cons J tail ih =>
    cases hJ : B.encloseInterval? J with
    | none => simp [Box.enclose?, hJ] at h
    | some K =>
      cases ht : Box.enclose? tail B with
      | none => simp [Box.enclose?, hJ, ht] at h
      | some rest =>
        simp [Box.enclose?, hJ, ht] at h
        subst intervals
        obtain ⟨head, tail⟩ := (Box.containsReal_cons_iff J _ values).1 hbox
        intro i I hI
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hI
          subst I
          exact Backend.containsReal_encloseInterval? hB hJ
            ((containsReal_some_iff J _).2 head)
        | succ i => exact ih ht tail i I (by simpa using hI)

/-- A checked upper bound implies the corresponding relation for every smaller real number. -/
theorem Relation.holds_of_check {relation : Relation} {hi : ℚ}
    (h : relation.check hi = true) {x : ℝ} (hx : x ≤ (hi : ℝ)) :
    relation.Holds x := by
  cases relation with
  | nonpositive =>
    have hhi : hi ≤ 0 := of_decide_eq_true h
    exact hx.trans (by exact_mod_cast hhi)
  | negative =>
    have hhi : hi < 0 := of_decide_eq_true h
    exact hx.trans_lt (by exact_mod_cast hhi)

/-- A successful leaf check establishes the inequality for every real assignment in its box. -/
theorem Expr.checkBox_sound {α : Type*} (e : Expr) {B : Backend α} (hB : B.Sound)
    {relation : Relation} {box : Box} (h : e.checkBox B relation box = true)
    {values : Nat → ℝ} (hbox : box.ContainsReal values) :
    relation.Holds (e.eval values) := by
  cases hbox' : box.enclose? B with
  | none => simp [Expr.checkBox, hbox'] at h
  | some intervals =>
    cases heval : e.eval? B (fun i => intervals[i]?) with
    | none => simp [Expr.checkBox, hbox', heval] at h
    | some I =>
      cases hhi : B.decode I.hi with
      | none => simp [Expr.checkBox, hbox', heval, hhi] at h
      | some hi =>
        have hcheck : relation.check hi = true := by
          simpa [Expr.checkBox, hbox', heval, hhi] using h
        obtain ⟨_, upper, _, hu, _, hx⟩ :=
          e.containsReal_eval? hB (Box.containsReal_enclose? hB hbox' hbox) heval
        have hu' : (hi : ℝ) = upper := by simpa [hhi] using hu
        exact Relation.holds_of_check hcheck (by simpa [hu'] using hx)

/-- Replacing a coordinate preserves membership when the new interval contains its value. -/
theorem Box.containsReal_set {box : Box} {values : Nat → ℝ}
    (hbox : box.ContainsReal values) {i : Nat} {I : Interval ℚ}
    (hI : I.ContainsReal some (values i)) :
    Box.ContainsReal (box.set i I) values := by
  intro j J hJ
  by_cases hij : i = j
  · subst j
    rw [List.getElem?_set] at hJ
    by_cases hi : i < box.length
    · simp [hi] at hJ
      subst J
      exact hI
    · simp [hi] at hJ
  · exact hbox j J (by simpa [List.getElem?_set_ne hij] using hJ)

/-- Every real assignment in a split box belongs to at least one of its two children. -/
theorem Box.containsReal_bisect? {box left right : Box}
    (h : box.bisect? = some (left, right)) {values : Nat → ℝ}
    (hbox : box.ContainsReal values) :
    left.ContainsReal values ∨ right.ContainsReal values := by
  cases hw : box.widest? with
  | none => simp [Box.bisect?, hw] at h
  | some selected =>
    rcases selected with ⟨i, width⟩
    cases hi : box[i]? with
    | none => simp [Box.bisect?, hw, hi] at h
    | some I =>
      by_cases hwidth : I.lo < I.hi
      · simp [Box.bisect?, hw, hi, hwidth] at h
        rcases h with ⟨rfl, rfl⟩
        obtain ⟨hlo, hhi⟩ := (containsReal_some_iff I _).1 (hbox i I hi)
        by_cases hmid : values i ≤ (((I.lo + I.hi) / 2 : ℚ) : ℝ)
        · exact Or.inl (Box.containsReal_set hbox
            ((containsReal_some_iff _ _).2 ⟨hlo, hmid⟩))
        · exact Or.inr (Box.containsReal_set hbox
            ((containsReal_some_iff _ _).2 ⟨le_of_lt (lt_of_not_ge hmid), hhi⟩))
      · simp [Box.bisect?, hw, hi, hwidth] at h

/--
A successful adaptive check proves the real inequality throughout the original rational box.

The computation depends only on the backend, expression, rational box, relation, and depth.
The real environment and its membership proof enter only this theorem.
-/
theorem Expr.check_sound {α : Type*} (e : Expr) {B : Backend α} (hB : B.Sound)
    {relation : Relation} {box : Box} {depth : Nat}
    (h : e.check B relation box depth = true) {values : Nat → ℝ}
    (hbox : box.ContainsReal values) : relation.Holds (e.eval values) := by
  induction depth generalizing box with
  | zero =>
    exact e.checkBox_sound hB (by simpa [Expr.check] using h) hbox
  | succ depth ih =>
    by_cases hleaf : e.checkBox B relation box = true
    · exact e.checkBox_sound hB hleaf hbox
    · cases hsplit : box.bisect? with
      | none => simp [Expr.check, hleaf, hsplit] at h
      | some children =>
        rcases children with ⟨left, right⟩
        have hc : e.check B relation left depth = true ∧
            e.check B relation right depth = true := by
          simpa [Expr.check, hleaf, hsplit] using h
        rcases Box.containsReal_bisect? hsplit hbox with hl | hr
        · exact ih hc.1 hl
        · exact ih hc.2 hr

end FloatLib.Numerics.Interval
