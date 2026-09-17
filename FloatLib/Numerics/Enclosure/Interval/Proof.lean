/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Runtime

/-!
# Soundness of partial, representation-independent interval arithmetic

Every theorem retains the successful-result hypothesis. Failed decoding, unavailable outward
rounding, and zero-crossing division are not interpreted as valid finite enclosures.
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

/-- Outward rounding of the endpoint pair encloses every member of the exact interval. -/
theorem contains_encloseInterval? (R : OutwardRounding α β) {a : Interval β} {I : Interval α}
    (h : encloseInterval? R a = some I) {x : β} (hx : a.lo ≤ x ∧ x ≤ a.hi) :
    I.Contains R.decode x := by
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
      exact ⟨a₁, b₂, ha₁, hb₂, ha.trans hx.1, hx.2.trans hb⟩

/-- Any sound exact unary endpoint enclosure lifts through partial outward rounding. -/
theorem contains_liftUnary? (R : OutwardRounding α β) (f : Interval β → Interval β)
    (g : β → β)
    (hf : ∀ (a : Interval β) (x : β), a.lo ≤ x ∧ x ≤ a.hi →
      (f a).lo ≤ g x ∧ g x ≤ (f a).hi)
    {I K : Interval α} (h : liftUnary? R f I = some K)
    {x : β} (hx : I.Contains R.decode x) : K.Contains R.decode (g x) := by
  cases ha : I.decode? R.decode with
  | none => simp [liftUnary?, ha] at h
  | some a =>
    exact contains_encloseInterval? R (by simpa [liftUnary?, ha] using h)
      (hf a x ((contains_iff_of_decode? ha x).1 hx))

/-- Any sound exact binary endpoint enclosure lifts through partial outward rounding. -/
theorem contains_liftBinary? (R : OutwardRounding α β)
    (f : Interval β → Interval β → Interval β) (g : β → β → β)
    (hf : ∀ (a b : Interval β) (x y : β),
      a.lo ≤ x ∧ x ≤ a.hi → b.lo ≤ y ∧ y ≤ b.hi →
      (f a b).lo ≤ g x y ∧ g x y ≤ (f a b).hi)
    {I J K : Interval α} (h : liftBinary? R f I J = some K)
    {x y : β} (hx : I.Contains R.decode x) (hy : J.Contains R.decode y) :
    K.Contains R.decode (g x y) := by
  cases ha : I.decode? R.decode with
  | none => simp [liftBinary?, ha] at h
  | some a =>
    cases hb : J.decode? R.decode with
    | none => simp [liftBinary?, ha, hb] at h
    | some b =>
      exact contains_encloseInterval? R (by simpa [liftBinary?, ha, hb] using h)
        (hf a b x y ((contains_iff_of_decode? ha x).1 hx)
          ((contains_iff_of_decode? hb y).1 hy))

variable [Field β] [IsStrictOrderedRing β]

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

/-- Successful division certifies a nonzero denominator range and encloses the exact quotient. -/
theorem contains_div? (R : OutwardRounding α β) {I J K : Interval α}
    (h : div? R I J = some K) {x y : β}
    (hx : I.Contains R.decode x) (hy : J.Contains R.decode y) :
    K.Contains R.decode (x / y) := by
  cases ha : I.decode? R.decode with
  | none => simp [div?, ha] at h
  | some a =>
    cases hb : J.decode? R.decode with
    | none => simp [div?, ha, hb] at h
    | some b =>
      by_cases hzero : b.hi < 0 ∨ 0 < b.lo
      · simp only [div?, ha, hb, ite_eq_left hzero] at h
        exact contains_encloseInterval? R h
          (div_bounds_Icc a.lo a.hi b.lo b.hi x y
            ((contains_iff_of_decode? ha x).1 hx) ((contains_iff_of_decode? hb y).1 hy) hzero)
      · simp [div?, ha, hb, hzero] at h

end FloatLib.Numerics.Interval
