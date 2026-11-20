/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Range
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof
public import FloatLib.Numerics.Enclosure.Expression.ConstraintProof
public import FloatLib.Numerics.Enclosure.Expression.ExtensionsProof

/-!
# Soundness of enclosures with infinite ends

`Range.Contains` is the set of real members of a range: an end that is missing bounds nothing.
`Expr.contains_range` says that the range of an expression contains its value at every real
assignment in the ranges of the variables, for a sound backend with rational endpoints whose
decoder is the identity, and a table of names that the registered functions bear out
(`Range.NamesSound`). `Constraint.not_holds_of_failsOn` is the same for a constraint: when
`Constraint.failsOn` accepts a box of ranges, the constraint holds at no real assignment of the
box.

The proofs follow the operations of `Range` one by one. A rule for a monotone function uses the
backend's enclosure at one rational point and the monotonicity of the real function.

## Main statements

* `Range.contains_unary`, `Range.contains_binary`, `Range.contains_ternary`, `Range.contains_call`:
  the operations.
* `Expr.contains_range`: the evaluation.
* `Constraint.not_holds_of_failsOn`: the check of a constraint on a box of ranges.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

variable {functions : Nat → List ℝ → ℝ}

namespace Range

/-- The real members of a range: the numbers that are at least its lower end and at most its
upper end, where it has them. -/
def Contains (R : Range) (x : ℝ) : Prop :=
  (∀ a, R.lo = some a → (a : ℝ) ≤ x) ∧ (∀ b, R.hi = some b → x ≤ (b : ℝ))

/-- A real assignment respects every range of a box. -/
def BoxContains (box : List Range) (values : Nat → ℝ) : Prop :=
  ∀ (i : Nat) (R : Range), box[i]? = some R → R.Contains (values i)

/-- A table of the registered calls that are unary operations: where entry `index` names an
operation, the registered function `index` at one argument is the real function of that
operation. -/
def NamesSound (names : List (Option UnaryOp)) (functions : Nat → List ℝ → ℝ) : Prop :=
  ∀ (index : Nat) (op : UnaryOp), names[index]? = some (some op) →
    ∀ x : ℝ, functions index [x] = op.eval x

/-- The empty table names no call. -/
theorem namesSound_nil : NamesSound [] (extensionValues []) := by
  intro index op h
  simp at h

/-- Add the name of one more registered function to matching tables. -/
theorem NamesSound.cons {names : List (Option UnaryOp)} {functions : List (List ℝ → ℝ)}
    (h : NamesSound names (extensionValues functions)) {name : Option UnaryOp}
    {f : List ℝ → ℝ} (hf : ∀ op, name = some op → ∀ x : ℝ, f [x] = op.eval x) :
    NamesSound (name :: names) (extensionValues (f :: functions)) := by
  intro index op hindex x
  cases index with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hindex
    exact hf op hindex x
  | succ index => exact h index op (by simpa using hindex) x

/-- The real function of a unary operation, registered with one argument, has the name of the
operation. -/
theorem named (op : UnaryOp) :
    ∀ op', some op = some op' → ∀ x : ℝ, RealFunction.apply (n := 1) op.eval [x] = op'.eval x := by
  intro op' h x
  cases h
  rfl

/-- A registered function without a name: nothing is claimed about it. -/
theorem unnamed (f : List ℝ → ℝ) :
    ∀ op, (none : Option UnaryOp) = some op → ∀ x : ℝ, f [x] = op.eval x :=
  fun _ h => nomatch h

/-- Every real number is in the whole line. -/
theorem contains_whole (x : ℝ) : whole.Contains x :=
  ⟨fun _ h => by simp [whole] at h, fun _ h => by simp [whole] at h⟩

/-- A range with a lower end and an upper end contains the numbers between them. -/
theorem contains_both {a b : ℚ} {x : ℝ} (hlo : (a : ℝ) ≤ x) (hhi : x ≤ (b : ℝ)) :
    Contains ⟨some a, some b⟩ x :=
  ⟨fun _ h => by cases Option.some.inj h; exact hlo,
    fun _ h => by cases Option.some.inj h; exact hhi⟩

/-- A range with a lower end only contains the numbers above it. -/
theorem contains_lower {a : ℚ} {x : ℝ} (hlo : (a : ℝ) ≤ x) : Contains ⟨some a, none⟩ x :=
  ⟨fun _ h => by cases Option.some.inj h; exact hlo, fun _ h => by simp at h⟩

/-- A range with an upper end only contains the numbers below it. -/
theorem contains_upper {b : ℚ} {x : ℝ} (hhi : x ≤ (b : ℝ)) : Contains ⟨none, some b⟩ x :=
  ⟨fun _ h => by simp at h, fun _ h => by cases Option.some.inj h; exact hhi⟩

/-- The empty box places no restriction on the real assignment. -/
theorem boxContains_nil (values : Nat → ℝ) : BoxContains [] values := by
  intro i R h
  simp at h

/-- A box contains an assignment when its first range contains the first value and the rest of
the box the others. -/
theorem boxContains_cons {R : Range} {box : List Range} {values : Nat → ℝ}
    (head : R.Contains (values 0)) (tail : BoxContains box (fun i => values (i + 1))) :
    BoxContains (R :: box) values := by
  intro i S h
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact h ▸ head
  | succ i => exact tail i S (by simpa using h)

/-- The environment of a box of ranges contains the assignments of the box. -/
theorem contains_env {box : List Range} {values : Nat → ℝ} (h : BoxContains box values)
    (i : Nat) : (env box i).Contains (values i) := by
  unfold env
  rw [Kernel.Seq.nth?_eq]
  cases hi : box[i]? with
  | none => exact contains_whole _
  | some R => exact h i R hi

/-- The range of an interval contains the members of the interval. -/
theorem contains_ofInterval {I : Interval ℚ} {x : ℝ} (h : I.ContainsReal some x) :
    (ofInterval I).Contains x := by
  obtain ⟨hlo, hhi⟩ := (containsReal_some_iff I x).1 h
  exact contains_both hlo hhi

/-- A member of a range with two rational ends is a member of its interval. -/
theorem containsReal_of_interval? {R : Range} {I : Interval ℚ} (h : R.interval? = some I)
    {x : ℝ} (hx : R.Contains x) : I.ContainsReal some x := by
  obtain ⟨lo, hi⟩ := R
  cases lo with
  | none => simp [interval?] at h
  | some a =>
    cases hi with
    | none => simp [interval?] at h
    | some b =>
      simp only [interval?, Option.some.injEq] at h
      subst h
      exact (containsReal_some_iff _ _).2 ⟨hx.1 a rfl, hx.2 b rfl⟩

/-- The negation of a range contains the negatives of its members. -/
theorem contains_neg {R : Range} {x : ℝ} (h : R.Contains x) : (neg R).Contains (-x) := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 ha
    rw [Kernel.Q.neg_eq]
    push_cast
    exact neg_le_neg (h.2 b hb)
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hb
    rw [Kernel.Q.neg_eq]
    push_cast
    exact neg_le_neg (h.1 a ha)

private theorem addEnd_eq_some {p q : Option ℚ} {c : ℚ} (h : addEnd p q = some c) :
    ∃ a b, p = some a ∧ q = some b ∧ a + b = c := by
  cases p with
  | none => simp [addEnd] at h
  | some a =>
    cases q with
    | none => simp [addEnd] at h
    | some b =>
      exact ⟨a, b, rfl, rfl,
        by simpa only [addEnd, Option.some.injEq, Kernel.Q.add_eq] using h⟩

/-- The sum of two ranges contains the sums of their members. -/
theorem contains_add {R S : Range} {x y : ℝ} (hx : R.Contains x) (hy : S.Contains y) :
    (add R S).Contains (x + y) := by
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨a, b, ha, hb, rfl⟩ := addEnd_eq_some hc
    push_cast
    exact add_le_add (hx.1 a ha) (hy.1 b hb)
  · obtain ⟨a, b, ha, hb, rfl⟩ := addEnd_eq_some hc
    push_cast
    exact add_le_add (hx.2 a ha) (hy.2 b hb)

private theorem le_of_mulHiOfNonneg {R S : Range} {u : ℚ} (h : mulHiOfNonneg R S = some u)
    {x y : ℝ} (hx : R.Contains x) (hy : S.Contains y) : x * y ≤ (u : ℝ) := by
  unfold mulHiOfNonneg at h
  cases hlo : R.lo with
  | none => simp [hlo] at h
  | some a =>
    cases hhi : S.hi with
    | none => simp [hlo, hhi] at h
    | some d =>
      simp only [hlo, hhi, Kernel.Q.le_eq_decide, decide_eq_true_eq, Kernel.Q.mul_eq] at h
      have hxa := hx.1 a hlo
      have hyd := hy.2 d hhi
      split_ifs at h with ha hd
      · obtain rfl := Option.some.inj h
        have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
        have hd' : (d : ℝ) ≤ 0 := by exact_mod_cast hd
        push_cast
        nlinarith [mul_nonneg (sub_nonneg.2 hxa) (neg_nonneg.2 (hyd.trans hd')),
          mul_nonneg ha' (sub_nonneg.2 hyd)]
      · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
        have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
        have hd' : (0 : ℝ) ≤ d := by exact_mod_cast (not_le.1 hd).le
        have hxb := hx.2 b hb
        push_cast
        nlinarith [mul_nonneg (sub_nonneg.2 hxb) hd',
          mul_nonneg (ha'.trans hxa) (sub_nonneg.2 hyd)]

private theorem le_of_mulHi {R S : Range} {u : ℚ} (h : mulHi R S = some u) {x y : ℝ}
    (hx : R.Contains x) (hy : S.Contains y) : x * y ≤ (u : ℝ) := by
  unfold mulHi at h
  rcases Option.or_eq_some_iff.1 h with h | ⟨_, h⟩
  · exact le_of_mulHiOfNonneg h hx hy
  rcases Option.or_eq_some_iff.1 h with h | ⟨_, h⟩
  · rw [mul_comm]
    exact le_of_mulHiOfNonneg h hy hx
  rcases Option.or_eq_some_iff.1 h with h | ⟨_, h⟩
  · have key := le_of_mulHiOfNonneg h (contains_neg hx) (contains_neg hy)
    rwa [neg_mul_neg] at key
  · have key := le_of_mulHiOfNonneg h (contains_neg hy) (contains_neg hx)
    rwa [neg_mul_neg, mul_comm] at key

private theorem eq_zero_of_isZero {R : Range} (h : isZero R = true) {x : ℝ}
    (hx : R.Contains x) : x = 0 := by
  obtain ⟨lo, hi⟩ := R
  cases lo with
  | none => simp [isZero] at h
  | some a =>
    cases hi with
    | none => simp [isZero] at h
    | some b =>
      simp only [isZero, Bool.and_eq_true, Kernel.Q.beq_eq_decide, decide_eq_true_eq] at h
      have h1 := hx.1 a rfl
      have h2 := hx.2 b rfl
      rw [h.1] at h1
      rw [h.2] at h2
      exact le_antisymm (by simpa using h2) (by simpa using h1)

/-- The product of two ranges contains the products of their members. -/
theorem contains_mul {R S : Range} {x y : ℝ} (hx : R.Contains x) (hy : S.Contains y) :
    (mul R S).Contains (x * y) := by
  unfold mul
  split_ifs with hzero
  · have hproduct : x * y = 0 := by
      simp only [Bool.or_eq_true] at hzero
      rcases hzero with h | h
      · rw [eq_zero_of_isZero h hx, zero_mul]
      · rw [eq_zero_of_isZero h hy, mul_zero]
    rw [hproduct]
    exact contains_both (by simp) (by simp)
  · refine ⟨fun a ha => ?_, fun b hb => le_of_mulHi hb hx hy⟩
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 ha
    have key := le_of_mulHi hu (contains_neg hx) hy
    rw [Kernel.Q.neg_eq]
    push_cast
    linarith [neg_mul x y]

/-- The inverse of a range contains the inverses of its members. -/
theorem contains_inv {R : Range} {x : ℝ} (hx : R.Contains x) : (inv R).Contains x⁻¹ := by
  obtain ⟨lo, hi⟩ := R
  have positive : ∀ a : ℚ, (a : ℝ) ≤ x → 0 < a →
      Contains ⟨some ((hi.map Kernel.Q.inv).getD 0), some (Kernel.Q.inv a)⟩ x⁻¹ := by
    intro a hxa ha
    have hpos : (0 : ℝ) < a := by exact_mod_cast ha
    have hxpos : 0 < x := hpos.trans_le hxa
    refine contains_both ?_ ?_
    · cases hi with
      | none => simpa using (inv_pos.2 hxpos).le
      | some b =>
        simp only [Option.map_some, Option.getD_some, Kernel.Q.inv_eq, Rat.cast_inv]
        exact inv_anti₀ hxpos (hx.2 b rfl)
    · rw [Kernel.Q.inv_eq]
      push_cast
      exact inv_anti₀ hpos hxa
  have negative : ∀ (b : ℚ) (bound : ℚ), x ≤ (b : ℝ) → b < 0 → x⁻¹ ≤ (bound : ℝ) →
      Contains ⟨some (Kernel.Q.inv b), some bound⟩ x⁻¹ := by
    intro b bound hxb hb hbound
    have hneg : (b : ℝ) < 0 := by exact_mod_cast hb
    refine contains_both ?_ hbound
    rw [Kernel.Q.inv_eq]
    push_cast
    exact (inv_le_inv_of_neg hneg (hxb.trans_lt hneg)).2 hxb
  cases lo with
  | some a =>
    have hxa := hx.1 a rfl
    simp only [inv, Kernel.Q.lt_eq_decide, decide_eq_true_eq]
    split_ifs with ha
    · exact positive a hxa ha
    · cases hi with
      | none => exact contains_whole _
      | some b =>
        have hxb := hx.2 b rfl
        dsimp only
        split_ifs with hb
        · have hneg : (b : ℝ) < 0 := by exact_mod_cast hb
          have hxneg : x < 0 := hxb.trans_lt hneg
          refine negative b _ hxb hb ?_
          rw [Kernel.Q.inv_eq]
          push_cast
          exact (inv_le_inv_of_neg hxneg (hxa.trans_lt hxneg)).2 hxa
        · exact contains_whole _
  | none =>
    cases hi with
    | none => exact contains_whole _
    | some b =>
      have hxb := hx.2 b rfl
      simp only [inv, Kernel.Q.lt_eq_decide, decide_eq_true_eq]
      split_ifs with hb
      · have hneg : (b : ℝ) < 0 := by exact_mod_cast hb
        refine negative b 0 hxb hb ?_
        simpa using (inv_lt_zero.2 (hxb.trans_lt hneg)).le
      · exact contains_whole _

/-- The lower end of the absolute value of a range is a nonnegative number. -/
theorem abs_lo {R : Range} : ∃ a, (abs R).lo = some a ∧ 0 ≤ a := by
  obtain ⟨lo, hi⟩ := R
  cases lo with
  | some a =>
    cases hi with
    | some b =>
      simp only [abs, Kernel.Q.le_eq_decide, decide_eq_true_eq]
      split_ifs with ha hb
      · exact ⟨a, rfl, ha⟩
      · exact ⟨-b, by simp [neg], neg_nonneg.2 hb⟩
      · exact ⟨0, rfl, le_rfl⟩
    | none =>
      simp only [abs, Kernel.Q.le_eq_decide, decide_eq_true_eq]
      split_ifs with ha
      · exact ⟨a, rfl, ha⟩
      · exact ⟨0, rfl, le_rfl⟩
  | none =>
    cases hi with
    | some b =>
      simp only [abs, Kernel.Q.le_eq_decide, decide_eq_true_eq]
      split_ifs with hb
      · exact ⟨-b, by simp [neg], neg_nonneg.2 hb⟩
      · exact ⟨0, rfl, le_rfl⟩
    | none => exact ⟨0, rfl, le_rfl⟩

/-- The absolute value of a range contains the absolute values of its members. -/
theorem contains_abs {R : Range} {x : ℝ} (hx : R.Contains x) : (abs R).Contains |x| := by
  have nonneg : ∀ a : ℚ, R.lo = some a → 0 ≤ a → R.Contains |x| := by
    intro a hlo ha
    have h0 : (0 : ℝ) ≤ a := by exact_mod_cast ha
    rwa [abs_of_nonneg (h0.trans (hx.1 a hlo))]
  have nonpos : ∀ b : ℚ, R.hi = some b → b ≤ 0 → (neg R).Contains |x| := by
    intro b hhi hb
    have h0 : (b : ℝ) ≤ 0 := by exact_mod_cast hb
    rw [abs_of_nonpos ((hx.2 b hhi).trans h0)]
    exact contains_neg hx
  have zero : Contains ⟨some 0, none⟩ |x| := contains_lower (by simp)
  obtain ⟨lo, hi⟩ := R
  cases lo with
  | some a =>
    cases hi with
    | some b =>
      simp only [abs, Kernel.Q.le_eq_decide, decide_eq_true_eq]
      split_ifs with ha hb
      · exact nonneg a rfl ha
      · exact nonpos b rfl hb
      · refine contains_both (by simp) ?_
        rw [Kernel.Q.max_eq, Kernel.Q.neg_eq]
        push_cast
        exact abs_le.2 ⟨by linarith [hx.1 a rfl, le_max_left (-(a : ℝ)) b],
          (hx.2 b rfl).trans (le_max_right _ _)⟩
    | none =>
      simp only [abs, Kernel.Q.le_eq_decide, decide_eq_true_eq]
      split_ifs with ha
      · exact nonneg a rfl ha
      · exact zero
  | none =>
    cases hi with
    | some b =>
      simp only [abs, Kernel.Q.le_eq_decide, decide_eq_true_eq]
      split_ifs with hb
      · exact nonpos b rfl hb
      · exact zero
    | none => exact zero

/-- The power of a range contains the powers of its members. -/
theorem contains_pow {R : Range} {x : ℝ} (hx : R.Contains x) (n : Nat) :
    (pow R n).Contains (x ^ n) := by
  unfold pow
  split_ifs with hzero heven
  · subst hzero
    exact contains_both (by simp) (by simp)
  · have habs := contains_abs hx
    obtain ⟨l, hl, hl0⟩ := abs_lo (R := R)
    have hl0' : (0 : ℝ) ≤ l := by exact_mod_cast hl0
    rw [← Even.pow_abs (Nat.even_iff.2 heven) x]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 ha
      obtain rfl : l = c := Option.some.inj (hl.symm.trans hc)
      rw [Kernel.Q.pow_eq]
      push_cast
      exact pow_le_pow_left₀ hl0' (habs.1 l hl) n
    · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hb
      rw [Kernel.Q.pow_eq]
      push_cast
      exact pow_le_pow_left₀ (abs_nonneg x) (habs.2 c hc) n
  · have hodd : Odd n := Nat.odd_iff.2 (by omega)
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 ha
      rw [Kernel.Q.pow_eq]
      push_cast
      exact hodd.pow_le_pow.2 (hx.1 c hc)
    · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hb
      rw [Kernel.Q.pow_eq]
      push_cast
      exact hodd.pow_le_pow.2 (hx.2 c hc)

/-- The minimum of two ranges contains the smaller of a member of each. -/
theorem contains_min {R S : Range} {x y : ℝ} (hx : R.Contains x) (hy : S.Contains y) :
    (min R S).Contains (Min.min x y) := by
  obtain ⟨rlo, rhi⟩ := R
  obtain ⟨slo, shi⟩ := S
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · cases rlo with
    | none => simp [min] at ha
    | some p =>
      cases slo with
      | none => simp [min] at ha
      | some q =>
        simp only [min, Option.some.injEq, Kernel.Q.min_eq] at ha
        subst ha
        push_cast
        exact min_le_min (hx.1 p rfl) (hy.1 q rfl)
  · cases rhi with
    | none =>
      simp only [min] at hb
      exact (min_le_right x y).trans (hy.2 b hb)
    | some p =>
      cases shi with
      | none =>
        simp only [min, Option.some.injEq] at hb
        subst hb
        exact (min_le_left x y).trans (hx.2 p rfl)
      | some q =>
        simp only [min, Option.some.injEq, Kernel.Q.min_eq] at hb
        subst hb
        push_cast
        exact min_le_min (hx.2 p rfl) (hy.2 q rfl)

/-- The maximum of two ranges contains the larger of a member of each. -/
theorem contains_max {R S : Range} {x y : ℝ} (hx : R.Contains x) (hy : S.Contains y) :
    (max R S).Contains (Max.max x y) := by
  have key := contains_neg (contains_min (contains_neg hx) (contains_neg hy))
  rwa [← max_neg_neg, neg_neg, neg_neg] at key

section Backend

variable {B : Backend ℚ}

/-- The backend's enclosure of a unary operation at a rational point contains its value. -/
private theorem at_point (hB : B.Sound functions) (hdecode : ∀ q, B.decode q = some q)
    {op : UnaryOp} {q : ℚ} {J : Interval ℚ} (h : B.unary? op ⟨q, q⟩ = some J) :
    (J.lo : ℝ) ≤ op.eval q ∧ op.eval q ≤ (J.hi : ℝ) := by
  have hpoint : (⟨q, q⟩ : Interval ℚ).ContainsReal B.decode (q : ℝ) := by
    have : B.decode = some := funext hdecode
    rw [this]
    exact (containsReal_some_iff _ _).2 ⟨le_rfl, le_rfl⟩
  have hJ := hB.unary h hpoint
  have : B.decode = some := funext hdecode
  rw [this] at hJ
  exact (containsReal_some_iff _ _).1 hJ

/-- A lower end from the backend at a rational point is below the value there. -/
theorem lowerAt_le (hB : B.Sound functions) (hdecode : ∀ q, B.decode q = some q)
    {op : UnaryOp} {q m : ℚ} (h : lowerAt B op q = some m) : (m : ℝ) ≤ op.eval q := by
  obtain ⟨J, hJ, rfl⟩ := Option.map_eq_some_iff.1 h
  exact (at_point hB hdecode hJ).1

/-- An upper end from the backend at a rational point is above the value there. -/
theorem le_upperAt (hB : B.Sound functions) (hdecode : ∀ q, B.decode q = some q)
    {op : UnaryOp} {q m : ℚ} (h : upperAt B op q = some m) : op.eval q ≤ (m : ℝ) := by
  obtain ⟨J, hJ, rfl⟩ := Option.map_eq_some_iff.1 h
  exact (at_point hB hdecode hJ).2

/-- `halfPi` is at least `π / 2`. -/
theorem le_halfPi (hB : B.Sound functions) (hdecode : ∀ q, B.decode q = some q) :
    Real.pi / 2 ≤ (halfPi B : ℝ) := by
  unfold halfPi
  cases h : upperAt B .acos 0 with
  | none =>
    simp only [Option.getD_none]
    push_cast
    linarith [Real.pi_le_four]
  | some m =>
    have key := le_upperAt hB hdecode h
    simp only [UnaryOp.eval, Rat.cast_zero, Real.arccos_zero] at key
    simpa using key

/-- A monotone operation of the backend: its lower ends at the rational lower end of a range
bound its values on the range from below. -/
private theorem monotone_lower (hB : B.Sound functions) (hdecode : ∀ q, B.decode q = some q)
    {op : UnaryOp} (hmono : Monotone op.eval) {R : Range} {x : ℝ} (hx : R.Contains x) {m : ℚ}
    (h : R.lo.bind (lowerAt B op) = some m) : (m : ℝ) ≤ op.eval x := by
  obtain ⟨a, ha, hm⟩ := Option.bind_eq_some_iff.1 h
  exact (lowerAt_le hB hdecode hm).trans (hmono (hx.1 a ha))

/-- A monotone operation of the backend: its upper ends at the rational upper end of a range
bound its values on the range from above. -/
private theorem monotone_upper (hB : B.Sound functions) (hdecode : ∀ q, B.decode q = some q)
    {op : UnaryOp} (hmono : Monotone op.eval) {R : Range} {x : ℝ} (hx : R.Contains x) {m : ℚ}
    (h : R.hi.bind (upperAt B op) = some m) : op.eval x ≤ (m : ℝ) := by
  obtain ⟨b, hb, hm⟩ := Option.bind_eq_some_iff.1 h
  exact (hmono (hx.2 b hb)).trans (le_upperAt hB hdecode hm)

/-- The rules for a unary operation where the backend gives no enclosure are sound. -/
theorem contains_tail (hB : B.Sound functions) (hdecode : ∀ q, B.decode q = some q)
    (op : UnaryOp) {R : Range} {x : ℝ} (hx : R.Contains x) :
    (tail B op R).Contains (op.eval x) := by
  have hpi := le_halfPi hB hdecode
  cases op with
  | neg => exact contains_neg hx
  | abs => exact contains_abs hx
  | inv => exact contains_inv hx
  | pow n => exact contains_pow hx n
  | exp =>
    refine ⟨fun a ha => ?_,
      fun b hb => monotone_upper (op := .exp) hB hdecode Real.exp_monotone hx hb⟩
    obtain rfl := Option.some.inj ha
    cases h : R.lo.bind (lowerAt B .exp) with
    | none =>
      change ((0 : ℚ) : ℝ) ≤ Real.exp x
      exact_mod_cast (Real.exp_pos x).le
    | some m => exact monotone_lower (op := .exp) hB hdecode Real.exp_monotone hx h
  | log =>
    cases hlo : R.lo with
    | none =>
      simp only [tail, hlo]
      exact contains_whole _
    | some a =>
      simp only [tail, hlo, Kernel.Q.lt_eq_decide, decide_eq_true_eq]
      split_ifs with ha
      · have hpos : (0 : ℝ) < a := by exact_mod_cast ha
        have hxa := hx.1 a hlo
        refine ⟨fun c hc => ?_, fun c hc => ?_⟩
        · exact (lowerAt_le (op := .log) hB hdecode hc).trans (Real.log_le_log hpos hxa)
        · obtain ⟨b, hb, hm⟩ := Option.bind_eq_some_iff.1 hc
          exact (Real.log_le_log (hpos.trans_le hxa) (hx.2 b hb)).trans
            (le_upperAt (op := .log) hB hdecode hm)
      · exact contains_whole _
  | sin =>
    exact contains_both (by exact_mod_cast Real.neg_one_le_sin x)
      (by exact_mod_cast Real.sin_le_one x)
  | cos =>
    exact contains_both (by exact_mod_cast Real.neg_one_le_cos x)
      (by exact_mod_cast Real.cos_le_one x)
  | tan => exact contains_whole _
  | asin =>
    refine contains_both ?_ ((Real.arcsin_le_pi_div_two x).trans hpi)
    rw [Kernel.Q.neg_eq, Rat.cast_neg]
    exact (neg_le_neg hpi).trans (Real.neg_pi_div_two_le_arcsin x)
  | acos =>
    refine contains_both (by exact_mod_cast Real.arccos_nonneg x) ?_
    rw [Kernel.Q.mul_eq, Rat.cast_mul, Rat.cast_ofNat]
    exact (Real.arccos_le_pi x).trans (by linarith)
  | atan =>
    refine contains_both ?_ ?_
    · cases h : R.lo.bind (lowerAt B .atan) with
      | none =>
        rw [Option.getD_none, Kernel.Q.neg_eq, Rat.cast_neg]
        exact (neg_le_neg hpi).trans (Real.neg_pi_div_two_lt_arctan x).le
      | some m =>
        exact monotone_lower (op := .atan) hB hdecode Real.arctan_strictMono.monotone hx h
    · cases h : R.hi.bind (upperAt B .atan) with
      | none => exact (Real.arctan_lt_pi_div_two x).le.trans hpi
      | some m =>
        exact monotone_upper (op := .atan) hB hdecode Real.arctan_strictMono.monotone hx h
  | sinh =>
    exact ⟨fun a ha =>
        monotone_lower (op := .sinh) hB hdecode Real.sinh_strictMono.monotone hx ha,
      fun b hb => monotone_upper (op := .sinh) hB hdecode Real.sinh_strictMono.monotone hx hb⟩
  | cosh =>
    have habs := contains_abs hx
    obtain ⟨l, hl, hl0⟩ := abs_lo (R := R)
    have hl0' : (0 : ℝ) ≤ l := by exact_mod_cast hl0
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · obtain rfl := Option.some.inj ha
      cases h : (abs R).lo.bind (lowerAt B .cosh) with
      | none =>
        change ((1 : ℚ) : ℝ) ≤ Real.cosh x
        exact_mod_cast Real.one_le_cosh x
      | some m =>
        obtain ⟨c, hc, hm⟩ := Option.bind_eq_some_iff.1 h
        obtain rfl : l = c := Option.some.inj (hl.symm.trans hc)
        refine (lowerAt_le (op := .cosh) hB hdecode hm).trans ?_
        exact Real.cosh_le_cosh.2 (by rw [abs_of_nonneg hl0']; exact habs.1 l hl)
    · obtain ⟨c, hc, hm⟩ := Option.bind_eq_some_iff.1 hb
      refine le_trans ?_ (le_upperAt (op := .cosh) hB hdecode hm)
      have hc0 : (0 : ℝ) ≤ c := (abs_nonneg x).trans (habs.2 c hc)
      exact Real.cosh_le_cosh.2 (by rw [abs_of_nonneg hc0]; exact habs.2 c hc)
  | tanh =>
    refine contains_both ?_ ?_
    · cases h : R.lo.bind (lowerAt B .tanh) with
      | none =>
        change ((-1 : ℚ) : ℝ) ≤ Real.tanh x
        exact_mod_cast (Real.neg_one_lt_tanh x).le
      | some m => exact monotone_lower (op := .tanh) hB hdecode tanh_monotone hx h
    · cases h : R.hi.bind (upperAt B .tanh) with
      | none =>
        change Real.tanh x ≤ ((1 : ℚ) : ℝ)
        exact_mod_cast (Real.tanh_lt_one x).le
      | some m => exact monotone_upper (op := .tanh) hB hdecode tanh_monotone hx h
  | sqrt =>
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · obtain rfl := Option.some.inj ha
      cases h : R.lo.bind (fun a => if Kernel.Q.le 0 a then lowerAt B .sqrt a else none) with
      | none =>
        change ((0 : ℚ) : ℝ) ≤ Real.sqrt x
        exact_mod_cast Real.sqrt_nonneg x
      | some m =>
        obtain ⟨c, hc, hm⟩ := Option.bind_eq_some_iff.1 h
        split_ifs at hm
        exact (lowerAt_le (op := .sqrt) hB hdecode hm).trans (Real.sqrt_le_sqrt (hx.1 c hc))
    · obtain ⟨c, hc, hm⟩ := Option.bind_eq_some_iff.1 hb
      simp only [Kernel.Q.lt_eq_decide, decide_eq_true_eq] at hm
      split_ifs at hm with hneg
      · obtain rfl := Option.some.inj hm
        have hc0 : (c : ℝ) ≤ 0 := by exact_mod_cast hneg.le
        exact_mod_cast (Real.sqrt_eq_zero_of_nonpos ((hx.2 c hc).trans hc0)).le
      · exact (Real.sqrt_le_sqrt (hx.2 c hc)).trans (le_upperAt (op := .sqrt) hB hdecode hm)

/-- A unary operation on a range contains its values at the members of the range. -/
theorem contains_unary (hB : B.Sound functions) (hdecode : ∀ q, B.decode q = some q)
    (op : UnaryOp) {R : Range} {x : ℝ} (hx : R.Contains x) :
    (unary B op R).Contains (op.eval x) := by
  unfold unary
  cases hI : R.interval? with
  | none => exact contains_tail hB hdecode op hx
  | some I =>
    dsimp only
    cases hJ : B.unary? op I with
    | none => exact contains_tail hB hdecode op hx
    | some J =>
      have hmember : I.ContainsReal B.decode x := by
        rw [funext hdecode]
        exact containsReal_of_interval? hI hx
      have key := hB.unary hJ hmember
      rw [funext hdecode] at key
      exact contains_ofInterval key

/-- The rules for a binary operation where the backend gives no enclosure are sound. -/
theorem contains_pair (op : BinaryOp) {R S : Range} {x y : ℝ} (hx : R.Contains x)
    (hy : S.Contains y) : (pair op R S).Contains (op.eval x y) := by
  cases op with
  | add => exact contains_add hx hy
  | sub =>
    have key := contains_add hx (contains_neg hy)
    rwa [← sub_eq_add_neg] at key
  | mul => exact contains_mul hx hy
  | div =>
    have key := contains_mul hx (contains_inv hy)
    rwa [← div_eq_mul_inv] at key
  | min => exact contains_min hx hy
  | max => exact contains_max hx hy

/-- A binary operation on two ranges contains its values at their members. -/
theorem contains_binary (hB : B.Sound functions) (hdecode : ∀ q, B.decode q = some q)
    (op : BinaryOp) {R S : Range} {x y : ℝ} (hx : R.Contains x) (hy : S.Contains y) :
    (binary B op R S).Contains (op.eval x y) := by
  unfold binary
  cases hI : R.interval? with
  | none => exact contains_pair op hx hy
  | some I =>
    cases hJ : S.interval? with
    | none => exact contains_pair op hx hy
    | some J =>
      dsimp only
      cases hK : B.binary? op I J with
      | none => exact contains_pair op hx hy
      | some K =>
        have hmx : I.ContainsReal B.decode x := by
          rw [funext hdecode]
          exact containsReal_of_interval? hI hx
        have hmy : J.ContainsReal B.decode y := by
          rw [funext hdecode]
          exact containsReal_of_interval? hJ hy
        have key := hB.binary hK hmx hmy
        rw [funext hdecode] at key
        exact contains_ofInterval key

/-- A three-input operation on three ranges contains its values at their members. -/
theorem contains_ternary (hB : B.Sound functions) (hdecode : ∀ q, B.decode q = some q)
    (op : TernaryOp) {R S T : Range} {x y z : ℝ} (hx : R.Contains x) (hy : S.Contains y)
    (hz : T.Contains z) : (ternary B op R S T).Contains (op.eval x y z) := by
  have fallback : (add (mul R S) T).Contains (op.eval x y z) := by
    cases op
    exact contains_add (contains_mul hx hy) hz
  unfold ternary
  cases hI : R.interval? with
  | none => cases op; exact fallback
  | some I =>
    cases hJ : S.interval? with
    | none => cases op; exact fallback
    | some J =>
      cases hK : T.interval? with
      | none => cases op; exact fallback
      | some K =>
        dsimp only
        cases hL : B.ternary? op I J K with
        | none => cases op; exact fallback
        | some L =>
          have hmx : I.ContainsReal B.decode x := by
            rw [funext hdecode]
            exact containsReal_of_interval? hI hx
          have hmy : J.ContainsReal B.decode y := by
            rw [funext hdecode]
            exact containsReal_of_interval? hJ hy
          have hmz : K.ContainsReal B.decode z := by
            rw [funext hdecode]
            exact containsReal_of_interval? hK hz
          have key := hB.ternary hL hmx hmy hmz
          rw [funext hdecode] at key
          exact contains_ofInterval key

/-- The intervals of a list of ranges with rational ends contain the members of the ranges. -/
private theorem forall₂_of_mapM {args : List Range} {inputs : List (Interval ℚ)}
    (h : args.mapM interval? = some inputs) {values : List ℝ}
    (hvalues : List.Forall₂ Contains args values) :
    List.Forall₂ (fun I x => I.ContainsReal some x) inputs values := by
  induction hvalues generalizing inputs with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .nil
  | @cons R x args values hR _ ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨I, hI, rest, hrest, rfl⟩ := h
    exact .cons (containsReal_of_interval? hI hR) (ih hrest)

/-- A registered operation on ranges contains its values at their members. -/
theorem contains_call (hB : B.Sound functions) (hdecode : ∀ q, B.decode q = some q)
    {names : List (Option UnaryOp)} (hnames : NamesSound names functions)
    (index : Nat) {args : List Range} {values : List ℝ}
    (hvalues : List.Forall₂ Contains args values) :
    (call B names index args).Contains (functions index values) := by
  have unnamedCall : (match args.mapM interval? with
      | some inputs =>
        match B.call? index inputs with
        | some output => ofInterval output
        | none => whole
      | none => whole).Contains (functions index values) := by
    cases hinputs : args.mapM interval? with
    | none => exact contains_whole _
    | some inputs =>
      dsimp only
      cases houtput : B.call? index inputs with
      | none => exact contains_whole _
      | some output =>
        have hmembers := forall₂_of_mapM hinputs hvalues
        rw [← funext hdecode] at hmembers
        have key := hB.call houtput hmembers
        rw [funext hdecode] at key
        exact contains_ofInterval key
  unfold call
  rw [Kernel.Seq.nth?_eq]
  cases hname : names[index]? with
  | none => exact unnamedCall
  | some name =>
    cases name with
    | none => exact unnamedCall
    | some op =>
      cases hvalues with
      | nil => exact unnamedCall
      | @cons R x args values hR hrest =>
        cases hrest with
        | nil =>
          rw [hnames index op hname x]
          exact contains_unary hB hdecode op hR
        | cons _ _ => exact unnamedCall

/-- The range of a rational constant contains it. -/
theorem contains_const (hB : B.Sound functions) (hdecode : ∀ q, B.decode q = some q) (q : ℚ) :
    (const B q).Contains (q : ℝ) := by
  unfold const
  cases h : B.const? q with
  | none => exact contains_whole _
  | some I =>
    have key := hB.const h
    rw [funext hdecode] at key
    exact contains_ofInterval key

end Backend

end Range

/-- The backend with rational endpoints and registered enclosures decodes an endpoint to
itself. -/
theorem Backend.decode_rational (config : Backend.Config) (extensions : List Extension)
    (q : ℚ) : (Backend.withExtensions (Backend.rational config) config extensions).decode q =
      some q :=
  rfl

/--
The range of an expression contains its value at every real assignment in the ranges of the
variables, for a sound backend with rational endpoints that decodes each endpoint to itself.
-/
theorem Expr.contains_range (e : Expr) {B : Backend ℚ} (hB : B.Sound functions)
    (hdecode : ∀ q, B.decode q = some q) {names : List (Option UnaryOp)}
    (hnames : Range.NamesSound names functions) {env : Nat → Range} {values : Nat → ℝ}
    (henv : ∀ i, (env i).Contains (values i)) :
    (e.range B names env).Contains (e.eval values functions) := by
  refine Expr.rec
    (motive_1 := fun e => (e.range B names env).Contains (e.eval values functions))
    (motive_2 := fun args => List.Forall₂ Range.Contains (Expr.rangeArgs args B names env)
      (Expr.evalArgs args values functions))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro q
    simpa only [Expr.range, Expr.eval] using Range.contains_const hB hdecode q
  · intro i
    simpa only [Expr.range, Expr.eval] using henv i
  · intro op a ha
    simpa only [Expr.range, Expr.eval] using Range.contains_unary hB hdecode op ha
  · intro op a b ha hb
    simpa only [Expr.range, Expr.eval] using Range.contains_binary hB hdecode op ha hb
  · intro op a b c ha hb hc
    simpa only [Expr.range, Expr.eval] using Range.contains_ternary hB hdecode op ha hb hc
  · intro index args hargs
    simpa only [Expr.range, Expr.eval] using Range.contains_call hB hdecode hnames index hargs
  · simp only [Expr.rangeArgs, Expr.evalArgs]
    exact .nil
  · intro arg args harg hargs
    simp only [Expr.rangeArgs, Expr.evalArgs]
    exact .cons harg hargs

/--
A constraint that `Constraint.failsOn` rejects on a box of ranges holds at no real assignment of
the box.
-/
theorem Constraint.not_holds_of_failsOn {B : Backend ℚ} (hB : B.Sound functions)
    (hdecode : ∀ q, B.decode q = some q) {names : List (Option UnaryOp)}
    (hnames : Range.NamesSound names functions) {c : Constraint} {box : List Range}
    (h : c.failsOn B names (Range.env box) = true) {values : Nat → ℝ}
    (hbox : Range.BoxContains box values) : ¬ c.Holds values functions := by
  induction c with
  | fails relation e =>
    intro hc
    simp only [Constraint.failsOn] at h
    cases hhi : (e.range B names (Range.env box)).hi with
    | none => simp [hhi] at h
    | some hi =>
      simp only [hhi] at h
      have hvalue := (e.contains_range hB hdecode hnames (Range.contains_env hbox)).2 hi hhi
      apply hc
      rw [Relation.check_def] at h
      cases relation with
      | nonpositive =>
        have hle : (hi : ℝ) ≤ 0 := by exact_mod_cast of_decide_eq_true h
        exact hvalue.trans hle
      | negative =>
        have hlt : (hi : ℝ) < 0 := by exact_mod_cast of_decide_eq_true h
        exact hvalue.trans_lt hlt
  | form strict f => simp [Constraint.failsOn] at h
  | and a b iha ihb =>
    simp only [Constraint.failsOn, Bool.or_eq_true] at h
    intro hc
    rcases h with h | h
    · exact iha h hc.1
    · exact ihb h hc.2
  | or a b iha ihb =>
    simp only [Constraint.failsOn, Bool.and_eq_true] at h
    intro hc
    rcases hc with hc | hc
    · exact iha h.1 hc
    · exact ihb h.2 hc

end FloatLib.Numerics.Interval
