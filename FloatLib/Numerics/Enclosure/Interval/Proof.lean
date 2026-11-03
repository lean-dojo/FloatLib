/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Runtime

/-!
# Soundness of partial, representation-independent interval arithmetic

Every enclosure theorem retains the successful-result hypothesis. Failed decoding, unavailable
outward rounding, and zero-crossing division are not interpreted as valid finite enclosures, and
`div?_eq_none_of_contains_zero` shows that division rejects every denominator range containing
zero.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

variable {α β : Type*}

/-- Successful interval decoding determines each endpoint interpretation. -/
theorem decode?_eq_some_iff (decode : α → Option β) (I : Interval α) (a : Interval β) :
    I.decode? decode = some a ↔ decode I.lo = some a.lo ∧ decode I.hi = some a.hi := by
  cases I with
  | mk lo hi =>
    cases a with
    | mk a b =>
      cases hlo : decode lo <;> cases hhi : decode hi <;> simp [decode?, hlo, hhi]

variable [LinearOrder β]

/-- After successful decoding, membership is the ordinary closed-interval predicate. -/
theorem contains_iff_of_decode? {decode : α → Option β} {I : Interval α} {a : Interval β}
    (ha : I.decode? decode = some a) (x : β) :
    I.Contains decode x ↔ a.lo ≤ x ∧ x ≤ a.hi := by
  rcases (decode?_eq_some_iff decode I a).1 ha with ⟨hlo, hhi⟩
  simp [Contains, hlo, hhi]

/--
A successful outward rounding of an exact endpoint pair decodes to a lower endpoint at most the
exact lower bound and an upper endpoint at least the exact upper bound.
-/
theorem decode_bounds_of_encloseInterval? (R : OutwardRounding α β) {a : Interval β}
    {I : Interval α} (h : encloseInterval? R a = some I) :
    ∃ lo hi, R.decode I.lo = some lo ∧ R.decode I.hi = some hi ∧ lo ≤ a.lo ∧ a.hi ≤ hi := by
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
      exact ⟨a₁, b₂, ha₁, hb₂, ha, hb⟩

/-- Outward rounding of the endpoint pair encloses every member of the exact interval. -/
theorem contains_encloseInterval? (R : OutwardRounding α β) {a : Interval β} {I : Interval α}
    (h : encloseInterval? R a = some I) {x : β} (hx : a.lo ≤ x ∧ x ≤ a.hi) :
    I.Contains R.decode x := by
  obtain ⟨lo, hi, hlo, hhi, hlower, hupper⟩ := decode_bounds_of_encloseInterval? R h
  exact ⟨lo, hi, hlo, hhi, hlower.trans hx.1, hx.2.trans hupper⟩

/-- A unary lift succeeds exactly when its input decodes and the exact image rounds outward. -/
theorem liftUnary?_eq_some_iff (R : OutwardRounding α β) (f : Interval β → Interval β)
    {I K : Interval α} :
    liftUnary? R f I = some K ↔
      ∃ a, I.decode? R.decode = some a ∧ encloseInterval? R (f a) = some K := by
  unfold liftUnary?
  cases I.decode? R.decode <;> simp

/-- A binary lift succeeds exactly when both inputs decode and the exact image rounds outward. -/
theorem liftBinary?_eq_some_iff (R : OutwardRounding α β)
    (f : Interval β → Interval β → Interval β) {I J K : Interval α} :
    liftBinary? R f I J = some K ↔
      ∃ a b, I.decode? R.decode = some a ∧ J.decode? R.decode = some b ∧
        encloseInterval? R (f a b) = some K := by
  unfold liftBinary?
  cases I.decode? R.decode <;> cases J.decode? R.decode <;> simp

/-- Any sound exact unary endpoint enclosure lifts through partial outward rounding. -/
theorem contains_liftUnary? (R : OutwardRounding α β) (f : Interval β → Interval β)
    (g : β → β)
    (hf : ∀ (a : Interval β) (x : β), a.lo ≤ x ∧ x ≤ a.hi →
      (f a).lo ≤ g x ∧ g x ≤ (f a).hi)
    {I K : Interval α} (h : liftUnary? R f I = some K)
    {x : β} (hx : I.Contains R.decode x) : K.Contains R.decode (g x) := by
  obtain ⟨a, ha, hK⟩ := (liftUnary?_eq_some_iff R f).1 h
  exact contains_encloseInterval? R hK (hf a x ((contains_iff_of_decode? ha x).1 hx))

/-- Any sound exact binary endpoint enclosure lifts through partial outward rounding. -/
theorem contains_liftBinary? (R : OutwardRounding α β)
    (f : Interval β → Interval β → Interval β) (g : β → β → β)
    (hf : ∀ (a b : Interval β) (x y : β),
      a.lo ≤ x ∧ x ≤ a.hi → b.lo ≤ y ∧ y ≤ b.hi →
      (f a b).lo ≤ g x y ∧ g x y ≤ (f a b).hi)
    {I J K : Interval α} (h : liftBinary? R f I J = some K)
    {x y : β} (hx : I.Contains R.decode x) (hy : J.Contains R.decode y) :
    K.Contains R.decode (g x y) := by
  obtain ⟨a, b, ha, hb, hK⟩ := (liftBinary?_eq_some_iff R f).1 h
  exact contains_encloseInterval? R hK
    (hf a b x y ((contains_iff_of_decode? ha x).1 hx) ((contains_iff_of_decode? hb y).1 hy))

variable [Field β] [IsStrictOrderedRing β]

omit [IsStrictOrderedRing β] in
/--
Division succeeds exactly when both inputs decode, the denominator range lies strictly on one
side of zero, and the four-corner quotient bounds round outward.
-/
theorem div?_eq_some_iff (R : OutwardRounding α β) {I J K : Interval α} :
    div? R I J = some K ↔
      ∃ a b, I.decode? R.decode = some a ∧ J.decode? R.decode = some b ∧
        (b.hi < 0 ∨ 0 < b.lo) ∧
        encloseInterval? R
          ⟨minOfFour (a.lo / b.lo) (a.lo / b.hi) (a.hi / b.lo) (a.hi / b.hi),
            maxOfFour (a.lo / b.lo) (a.lo / b.hi) (a.hi / b.lo) (a.hi / b.hi)⟩ = some K := by
  unfold div?
  cases I.decode? R.decode <;> cases J.decode? R.decode <;> simp

/-- Every successful negation encloses the exact negative value. -/
theorem contains_neg? (R : OutwardRounding α β) {I K : Interval α}
    (h : neg? R I = some K) {x : β} (hx : I.Contains R.decode x) :
    K.Contains R.decode (-x) :=
  contains_liftUnary? R _ _ (fun _ _ hx => ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩) h hx

/-- Every successful addition encloses the exact sum. -/
theorem contains_add? (R : OutwardRounding α β) {I J K : Interval α}
    (h : add? R I J = some K) {x y : β}
    (hx : I.Contains R.decode x) (hy : J.Contains R.decode y) :
    K.Contains R.decode (x + y) :=
  contains_liftBinary? R _ _
    (fun _ _ _ _ hx hy => ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩) h hx hy

/-- Every successful subtraction encloses the exact difference. -/
theorem contains_sub? (R : OutwardRounding α β) {I J K : Interval α}
    (h : sub? R I J = some K) {x y : β}
    (hx : I.Contains R.decode x) (hy : J.Contains R.decode y) :
    K.Contains R.decode (x - y) :=
  contains_liftBinary? R _ _
    (fun _ _ _ _ hx hy => ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩) h hx hy

/-- Every successful four-corner multiplication encloses the exact product. -/
theorem contains_mul? (R : OutwardRounding α β) {I J K : Interval α}
    (h : mul? R I J = some K) {x y : β}
    (hx : I.Contains R.decode x) (hy : J.Contains R.decode y) :
    K.Contains R.decode (x * y) := by
  apply contains_liftBinary? R _ (· * ·) ?_ h hx hy
  intro a b x y hx hy
  exact mul_bounds_Icc a.lo a.hi b.lo b.hi x y hx hy

omit [IsStrictOrderedRing β] in
/-- A denominator range containing zero is rejected by division, including a zero endpoint. -/
theorem div?_eq_none_of_contains_zero (R : OutwardRounding α β) {I J : Interval α}
    (hzero : J.Contains R.decode 0) : div? R I J = none := by
  cases ha : I.decode? R.decode with
  | none => simp [div?, ha]
  | some a =>
    cases hb : J.decode? R.decode with
    | none => simp [div?, ha, hb]
    | some b =>
      obtain ⟨hlo, hhi⟩ := (contains_iff_of_decode? hb 0).mp hzero
      simp [div?, ha, hb, not_lt_of_ge hlo, not_lt_of_ge hhi]

/--
Every successful division encloses the exact quotient. The denominator is then nonzero:
`div?_eq_none_of_contains_zero` rejects every denominator range containing zero.
-/
theorem contains_div? (R : OutwardRounding α β) {I J K : Interval α}
    (h : div? R I J = some K) {x y : β}
    (hx : I.Contains R.decode x) (hy : J.Contains R.decode y) :
    K.Contains R.decode (x / y) := by
  obtain ⟨a, b, ha, hb, hzero, hK⟩ := (div?_eq_some_iff R).1 h
  exact contains_encloseInterval? R hK
    (div_bounds_Icc a.lo a.hi b.lo b.hi x y
      ((contains_iff_of_decode? ha x).1 hx) ((contains_iff_of_decode? hb y).1 hy) hzero)

end FloatLib.Numerics.Interval
