/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Basic
public import FloatLib.Numerics.Kernel.QProof
public import FloatLib.Numerics.Kernel.SeqProof

/-!
# Checking real inequalities on rational boxes

`Expr.check` evaluates an interval expression and checks its decoded upper bound against zero. If
that's inconclusive, it can split the widest positive-width input interval at its exact rational
midpoint, and then both children must succeed. Precision and elementary-function approximation
settings belong to the backend. The checker controls only the subdivision depth.

Each input coordinate comes with rational bounds. A missing variable, a failed endpoint conversion,
or a rejected operation makes a leaf fail. `CheckProof` proves that a successful check establishes
the inequality for every real assignment in the original box.

The definitions branch with `casesOn` on Booleans and options and read a variable with
`Kernel.Seq.nth?`, which Lean's kernel evaluates in fewer steps than `if`, `match`, `do` and the
indexing notation. Each has a theorem that states it in the ordinary notation: `Relation.check_def`,
`Backend.encloseInterval?_def`, `Box.enclose?_nil`, `Box.enclose?_cons`, `Box.widest?_nil`,
`Box.widest?_cons`, `Box.bisect?_def`, `Expr.checkBox_def`, `Expr.check_def`.

`Expr.checkZero` is the same check on the evaluation with the zero rule (`Expr.evalZero?`): a
product with a factor that is exactly zero, and a quotient with such a numerator, need no
enclosure of the other operand. It passes every box that `Expr.check` passes
(`Expr.checkZero_of_check`). Both are instances of one leaf check on a given evaluation
(`Box.checkWith`) and of one subdivision on a given leaf check (`Box.checkAdaptive`).
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- Rational bounds for variables numbered from zero. -/
abbrev Box := List (Interval ℚ)

/-- Whether the expression must be nonpositive or strictly negative throughout the box. -/
inductive Relation where
  /-- The expression is at most zero. -/
  | nonpositive
  /-- The expression is below zero. -/
  | negative
  deriving DecidableEq, Repr

/-- Test a rational upper bound against zero, by the sign of its numerator's comparison. -/
def Relation.check (relation : Relation) (hi : ℚ) : Bool :=
  match relation with
  | .nonpositive => Kernel.Q.le hi 0
  | .negative => Kernel.Q.lt hi 0

/-- The test of an upper bound, as decisions of the two order relations. -/
theorem Relation.check_def (relation : Relation) (hi : ℚ) :
    relation.check hi =
      match relation with
      | .nonpositive => decide (hi ≤ 0)
      | .negative => decide (hi < 0) := by
  cases relation <;> simp [Relation.check]

/--
Enclose both rational endpoints and keep the outward-facing bounds
(`Backend.encloseInterval?_def`).
-/
def Backend.encloseInterval? {α : Type*} (B : Backend α)
    (I : Interval ℚ) : Option (Interval α) :=
  Option.casesOn (motive := fun _ => Option (Interval α)) (B.const? I.lo) none
    (fun lower => Option.casesOn (motive := fun _ => Option (Interval α)) (B.const? I.hi) none
      (fun upper => some ⟨lower.lo, upper.hi⟩))

/-- The enclosure of an interval fails when either endpoint fails. -/
theorem Backend.encloseInterval?_def {α : Type*} (B : Backend α) (I : Interval ℚ) :
    B.encloseInterval? I = (do
      let lower ← B.const? I.lo
      let upper ← B.const? I.hi
      pure ⟨lower.lo, upper.hi⟩) := by
  unfold Backend.encloseInterval?
  cases B.const? I.lo <;> cases B.const? I.hi <;> rfl

/-- Enclose every coordinate, failing if either endpoint of any coordinate cannot be enclosed. -/
def Box.enclose? {α : Type*} (box : Box) (B : Backend α) :
    Option (List (Interval α)) :=
  match box with
  | [] => some []
  | I :: tail =>
    Option.casesOn (motive := fun _ => Option (List (Interval α))) (B.encloseInterval? I) none
      (fun J => Option.casesOn (motive := fun _ => Option (List (Interval α)))
        (Box.enclose? tail B) none (fun rest => some (J :: rest)))

/-- The empty box encloses to the empty list. -/
theorem Box.enclose?_nil {α : Type*} (B : Backend α) : Box.enclose? [] B = some [] := by
  rw [Box.enclose?]

/-- A box encloses coordinate by coordinate, and a failed coordinate fails the box. -/
theorem Box.enclose?_cons {α : Type*} (I : Interval ℚ) (tail : Box) (B : Backend α) :
    Box.enclose? (I :: tail) B = (do
      let J ← B.encloseInterval? I
      let rest ← Box.enclose? tail B
      pure (J :: rest)) := by
  rw [Box.enclose?]
  cases B.encloseInterval? I <;> cases Box.enclose? tail B <;> rfl

/--
Index and width of the widest positive-width coordinate, taking the first one on a tie
(`Box.widest?_nil`, `Box.widest?_cons`). A coordinate has positive width when
`Kernel.Q.lt I.lo I.hi`, and its width `Kernel.Q.sub I.hi I.lo` is computed only to compare it
with a later coordinate.
-/
def Box.widest? (box : Box) : Option (Nat × ℚ) :=
  match box with
  | [] => none
  | I :: tail =>
    Bool.casesOn (motive := fun _ => Option (Nat × ℚ)) (Kernel.Q.lt I.lo I.hi)
      (Option.casesOn (motive := fun _ => Option (Nat × ℚ)) (Box.widest? tail) none
        (fun later => some (Nat.succ later.1, later.2)))
      (Option.casesOn (motive := fun _ => Option (Nat × ℚ)) (Box.widest? tail)
        (some (0, Kernel.Q.sub I.hi I.lo))
        (fun later =>
          Bool.casesOn (motive := fun _ => Option (Nat × ℚ))
            (Kernel.Q.lt (Kernel.Q.sub I.hi I.lo) later.2)
            (some (0, Kernel.Q.sub I.hi I.lo)) (some (Nat.succ later.1, later.2))))

/-- The empty box has no coordinate to split. -/
theorem Box.widest?_nil : Box.widest? [] = none := by
  rw [Box.widest?]

/--
The widest coordinate of a box with one more coordinate in front: the new coordinate when its
width is positive and no later coordinate is wider, and the widest later coordinate otherwise.
-/
theorem Box.widest?_cons (I : Interval ℚ) (tail : Box) :
    Box.widest? (I :: tail) =
      (let later := (Box.widest? tail).map (fun (i, width) => (i + 1, width))
       let width := I.hi - I.lo
       if 0 < width then
         match later with
         | none => some (0, width)
         | some (i, other) => if width < other then some (i, other) else some (0, width)
       else later) := by
  have hpos : Kernel.Q.lt I.lo I.hi = decide (0 < I.hi - I.lo) := by
    rw [Kernel.Q.lt_eq_decide]
    exact decide_eq_decide.2 sub_pos.symm
  rw [Box.widest?, hpos]
  simp only [Kernel.Q.sub_eq, Kernel.Q.lt_eq_decide]
  by_cases hwidth : 0 < I.hi - I.lo
  · rw [decide_eq_true hwidth, ite_eq_left hwidth]
    cases Box.widest? tail with
    | none => rfl
    | some later =>
      obtain ⟨i, other⟩ := later
      change Bool.casesOn (motive := fun _ => Option (Nat × ℚ)) (decide (I.hi - I.lo < other))
        (some (0, I.hi - I.lo)) (some (Nat.succ i, other)) =
          if I.hi - I.lo < other then some (i + 1, other) else some (0, I.hi - I.lo)
      by_cases hless : I.hi - I.lo < other
      · rw [decide_eq_true hless, ite_eq_left hless]
      · rw [decide_eq_false hless, ite_eq_right hless]
  · rw [decide_eq_false hwidth, ite_eq_right hwidth]
    cases Box.widest? tail with
    | none => rfl
    | some later => rfl

/--
Bisect the widest positive-width coordinate at its exact rational midpoint (`Box.bisect?_def`).

The two closed children share the midpoint and cover the original box. The midpoint
`Kernel.Q.divPow2 (Kernel.Q.add I.lo I.hi) 1` is `(I.lo + I.hi) / 2` (`Kernel.Q.divPow2_eq`,
`Kernel.Q.add_eq`).
-/
def Box.bisect? (box : Box) : Option (Box × Box) :=
  Option.casesOn (motive := fun _ => Option (Box × Box)) box.widest? none
    (fun selected =>
      Option.casesOn (motive := fun _ => Option (Box × Box)) (Kernel.Seq.nth? box selected.1) none
        (fun I =>
          Bool.casesOn (motive := fun _ => Option (Box × Box)) (Kernel.Q.lt I.lo I.hi) none
            ((fun mid => some (box.set selected.1 ⟨I.lo, mid⟩, box.set selected.1 ⟨mid, I.hi⟩))
              (Kernel.Q.divPow2 (Kernel.Q.add I.lo I.hi) 1))))

/-- The bisection: the widest coordinate, read from the box, is cut at its midpoint. -/
theorem Box.bisect?_def (box : Box) :
    box.bisect? = (do
      let (i, _) ← box.widest?
      let I ← box[i]?
      if I.lo < I.hi then
        let mid := (I.lo + I.hi) / 2
        pure (box.set i ⟨I.lo, mid⟩, box.set i ⟨mid, I.hi⟩)
      else none) := by
  unfold Box.bisect?
  cases box.widest? with
  | none => rfl
  | some selected =>
    obtain ⟨i, width⟩ := selected
    change Option.casesOn (motive := fun _ => Option (Box × Box)) (Kernel.Seq.nth? box i) none
        (fun I => Bool.casesOn (motive := fun _ => Option (Box × Box)) (Kernel.Q.lt I.lo I.hi)
          none
          (some (box.set i ⟨I.lo, Kernel.Q.divPow2 (Kernel.Q.add I.lo I.hi) 1⟩,
            box.set i ⟨Kernel.Q.divPow2 (Kernel.Q.add I.lo I.hi) 1, I.hi⟩))) =
      (box[i]?).bind (fun I =>
        if I.lo < I.hi then
          some (box.set i ⟨I.lo, (I.lo + I.hi) / 2⟩, box.set i ⟨(I.lo + I.hi) / 2, I.hi⟩)
        else none)
    rw [Kernel.Seq.nth?_eq]
    cases box[i]? with
    | none => rfl
    | some I =>
      change Bool.casesOn (motive := fun _ => Option (Box × Box)) (Kernel.Q.lt I.lo I.hi) none
        (some (box.set i ⟨I.lo, Kernel.Q.divPow2 (Kernel.Q.add I.lo I.hi) 1⟩,
          box.set i ⟨Kernel.Q.divPow2 (Kernel.Q.add I.lo I.hi) 1, I.hi⟩)) =
        if I.lo < I.hi then
          some (box.set i ⟨I.lo, (I.lo + I.hi) / 2⟩, box.set i ⟨(I.lo + I.hi) / 2, I.hi⟩)
        else none
      rw [Kernel.Q.lt_eq_decide, Kernel.Q.divPow2_eq, Kernel.Q.add_eq, pow_one]
      by_cases hwidth : I.lo < I.hi
      · rw [decide_eq_true hwidth, ite_eq_left hwidth]
      · rw [decide_eq_false hwidth, ite_eq_right hwidth]

/--
The check of one box on a given evaluation of the expression: enclose the box, evaluate, decode
the upper endpoint and test it (`Box.checkWith_def`). `Expr.checkBox` is this check on
`Expr.eval?`, and `Expr.checkBoxZero` on `Expr.evalZero?`.
-/
def Box.checkWith {α : Type*} (B : Backend α) (relation : Relation)
    (evaluate : (Nat → Option (Interval α)) → Option (Interval α)) (box : Box) : Bool :=
  Option.casesOn (motive := fun _ => Bool) (box.enclose? B) false
    (fun intervals =>
      Option.casesOn (motive := fun _ => Bool)
        (evaluate (fun i => Kernel.Seq.nth? intervals i)) false
        (fun I => Option.casesOn (motive := fun _ => Bool) (B.decode I.hi) false
          (fun hi => relation.check hi)))

/-- The check of one box on a given evaluation, in the ordinary notation. -/
theorem Box.checkWith_def {α : Type*} (B : Backend α) (relation : Relation)
    (evaluate : (Nat → Option (Interval α)) → Option (Interval α)) (box : Box) :
    box.checkWith B relation evaluate =
      match box.enclose? B with
      | none => false
      | some intervals =>
        match evaluate (fun i => intervals[i]?) with
        | none => false
        | some I =>
          match B.decode I.hi with
          | none => false
          | some hi => relation.check hi := by
  unfold Box.checkWith
  cases box.enclose? B with
  | none => rfl
  | some intervals =>
    change Option.casesOn (motive := fun _ => Bool)
      (evaluate (fun i => Kernel.Seq.nth? intervals i)) false _ = _
    simp only [Kernel.Seq.nth?_eq]
    cases evaluate (fun i => intervals[i]?) with
    | none => rfl
    | some I =>
      change Option.casesOn (motive := fun _ => Bool) (B.decode I.hi) false
        (fun hi => relation.check hi) =
          match B.decode I.hi with
          | none => false
          | some hi => relation.check hi
      cases B.decode I.hi <;> rfl

/--
Check one box using the decoded upper endpoint of a successful expression evaluation
(`Expr.checkBox_def`).
-/
def Expr.checkBox {α : Type*} (e : Expr) (B : Backend α)
    (relation : Relation) (box : Box) : Bool :=
  Option.casesOn (motive := fun _ => Bool) (box.enclose? B) false
    (fun intervals =>
      Option.casesOn (motive := fun _ => Bool)
        (e.eval? B (fun i => Kernel.Seq.nth? intervals i)) false
        (fun I => Option.casesOn (motive := fun _ => Bool) (B.decode I.hi) false
          (fun hi => relation.check hi)))

/-- The check of one box: enclose the box, evaluate, decode the upper endpoint and test it. -/
theorem Expr.checkBox_def {α : Type*} (e : Expr) (B : Backend α)
    (relation : Relation) (box : Box) :
    e.checkBox B relation box =
      match box.enclose? B with
      | none => false
      | some intervals =>
        match e.eval? B (fun i => intervals[i]?) with
        | none => false
        | some I =>
          match B.decode I.hi with
          | none => false
          | some hi => relation.check hi :=
  Box.checkWith_def B relation (e.eval? B) box

/--
Check a real inequality, subdividing inconclusive boxes up to the supplied depth
(`Expr.check_def`).

Depth zero performs a single interval evaluation. A split succeeds only when both children
succeed, including when the original evaluation rejected an operation's domain.
-/
def Expr.check {α : Type*} (e : Expr) (B : Backend α) (relation : Relation) :
    Box → Nat → Bool
  | box, 0 => e.checkBox B relation box
  | box, depth + 1 =>
    Bool.casesOn (motive := fun _ => Bool) (e.checkBox B relation box)
      (Option.casesOn (motive := fun _ => Bool) box.bisect? false
        (fun children =>
          Bool.casesOn (motive := fun _ => Bool) (e.check B relation children.1 depth) false
            (e.check B relation children.2 depth)))
      true

/-- The adaptive check: the box passes, or it is split and both halves pass at one depth less. -/
theorem Expr.check_def {α : Type*} (e : Expr) (B : Backend α)
    (relation : Relation) (box : Box) (depth : Nat) :
    e.check B relation box depth =
      if e.checkBox B relation box then true
      else
        match depth with
        | 0 => false
        | depth + 1 =>
          match box.bisect? with
          | none => false
          | some (left, right) =>
            e.check B relation left depth && e.check B relation right depth := by
  cases depth with
  | zero =>
    rw [Expr.check]
    cases e.checkBox B relation box <;> rfl
  | succ depth =>
    rw [Expr.check]
    cases e.checkBox B relation box with
    | true => rfl
    | false =>
      change Option.casesOn (motive := fun _ => Bool) box.bisect? false _ = _
      cases box.bisect? with
      | none => rfl
      | some children =>
        obtain ⟨left, right⟩ := children
        change Bool.casesOn (motive := fun _ => Bool) (e.check B relation left depth) false
          (e.check B relation right depth) =
            (e.check B relation left depth && e.check B relation right depth)
        cases e.check B relation left depth <;> rfl

/-! ## The check with the zero rule -/

/--
Check a box with a given leaf check, subdividing inconclusive boxes up to the supplied depth:
the box passes, or it is split and both halves pass at one depth less. `Expr.check` is this
check on the leaf `Expr.checkBox` (`Expr.check_eq_checkAdaptive`).
-/
def Box.checkAdaptive (leaf : Box → Bool) : Box → Nat → Bool
  | box, 0 => leaf box
  | box, depth + 1 =>
    Bool.casesOn (motive := fun _ => Bool) (leaf box)
      (Option.casesOn (motive := fun _ => Bool) box.bisect? false
        (fun children =>
          Bool.casesOn (motive := fun _ => Bool) (Box.checkAdaptive leaf children.1 depth) false
            (Box.checkAdaptive leaf children.2 depth)))
      true

/-- The adaptive check is the subdivision on the leaf check of one box. -/
theorem Expr.check_eq_checkAdaptive {α : Type*} (e : Expr) (B : Backend α)
    (relation : Relation) (box : Box) (depth : Nat) :
    e.check B relation box depth = Box.checkAdaptive (e.checkBox B relation) box depth := by
  induction depth generalizing box with
  | zero => rfl
  | succ depth ih =>
    rw [Expr.check, Box.checkAdaptive]
    simp only [ih]

/--
Check one box as `Expr.checkBox` does, on the evaluation with the zero rule (`Expr.evalZero?`):
a product with a factor that is exactly zero, and a quotient with such a numerator, need no
enclosure of the other operand.
-/
def Expr.checkBoxZero {α : Type*} (e : Expr) (B : Backend α)
    (relation : Relation) (box : Box) : Bool :=
  box.checkWith B relation (e.evalZero? B)

/--
Check a real inequality as `Expr.check` does, on the evaluation with the zero rule
(`Expr.evalZero?`), subdividing inconclusive boxes up to the supplied depth. It passes every
box that `Expr.check` passes (`Expr.checkZero_of_check`).
-/
def Expr.checkZero {α : Type*} (e : Expr) (B : Backend α) (relation : Relation) (box : Box)
    (depth : Nat) : Bool :=
  Box.checkAdaptive (e.checkBoxZero B relation) box depth

/-- A leaf check that passes wherever another one does passes the same subdivisions. -/
theorem Box.checkAdaptive_mono {leaf stronger : Box → Bool}
    (h : ∀ box, leaf box = true → stronger box = true) {box : Box} {depth : Nat}
    (hcheck : Box.checkAdaptive leaf box depth = true) :
    Box.checkAdaptive stronger box depth = true := by
  induction depth generalizing box with
  | zero => exact h box hcheck
  | succ depth ih =>
    rw [Box.checkAdaptive] at hcheck ⊢
    cases hleaf : leaf box with
    | true => rw [h box hleaf]
    | false =>
      rw [hleaf] at hcheck
      cases stronger box with
      | true => rfl
      | false =>
        cases hsplit : box.bisect? with
        | none => rw [hsplit] at hcheck; exact hcheck
        | some children =>
          rw [hsplit] at hcheck
          change Bool.casesOn (motive := fun _ => Bool)
            (Box.checkAdaptive leaf children.1 depth) false
            (Box.checkAdaptive leaf children.2 depth) = true at hcheck
          change Bool.casesOn (motive := fun _ => Bool)
            (Box.checkAdaptive stronger children.1 depth) false
            (Box.checkAdaptive stronger children.2 depth) = true
          cases hleft : Box.checkAdaptive leaf children.1 depth with
          | false => rw [hleft] at hcheck; exact absurd hcheck Bool.false_ne_true
          | true =>
            rw [hleft] at hcheck
            rw [ih hleft]
            exact ih hcheck

/-- A box that passes the leaf check passes the leaf check with the zero rule. -/
theorem Expr.checkBoxZero_of_checkBox {α : Type*} (e : Expr) {B : Backend α}
    {relation : Relation} {box : Box} (h : e.checkBox B relation box = true) :
    e.checkBoxZero B relation box = true := by
  unfold Expr.checkBox at h
  unfold Expr.checkBoxZero Box.checkWith
  cases hbox : box.enclose? B with
  | none => rw [hbox] at h; exact h
  | some intervals =>
    rw [hbox] at h
    change Option.casesOn (motive := fun _ => Bool)
      (e.eval? B (fun i => Kernel.Seq.nth? intervals i)) false _ = true at h
    change Option.casesOn (motive := fun _ => Bool)
      (e.evalZero? B (fun i => Kernel.Seq.nth? intervals i)) false _ = true
    cases heval : e.eval? B (fun i => Kernel.Seq.nth? intervals i) with
    | none => rw [heval] at h; exact absurd h Bool.false_ne_true
    | some I =>
      rw [heval] at h
      rw [e.evalZero?_of_eval? B _ heval]
      exact h

/-- A box that passes the adaptive check passes the adaptive check with the zero rule. -/
theorem Expr.checkZero_of_check {α : Type*} (e : Expr) {B : Backend α}
    {relation : Relation} {box : Box} {depth : Nat} (h : e.check B relation box depth = true) :
    e.checkZero B relation box depth = true :=
  Box.checkAdaptive_mono (fun _ hleaf => e.checkBoxZero_of_checkBox hleaf)
    (by rwa [← Expr.check_eq_checkAdaptive])

end FloatLib.Numerics.Interval

namespace FloatLib.Numerics.Interval.Relation

/-- Reconstruct a `Relation` constructor from its constructor index. -/
add_decl_doc ofNat_ctorIdx

end FloatLib.Numerics.Interval.Relation
