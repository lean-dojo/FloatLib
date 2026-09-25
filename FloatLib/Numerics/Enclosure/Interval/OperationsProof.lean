/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Operations
public import FloatLib.Numerics.Enclosure.Interval.Real
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic

/-!
# Containment for interval powers and set operations

The scalar contracts lift exact endpoint bounds through `OutwardRounding`. For rational
decoders, the real contracts cover every real member of the input intervals. Even powers
use monotonicity on absolute values, retaining the zero minimum of a zero-crossing interval.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

variable {α β : Type*} [Field β] [LinearOrder β] [IsStrictOrderedRing β]

private theorem binaryPow_eq_pow {M : Type*} [Monoid M] (x : M) (n : ℕ) :
    npowBinRec n x = x ^ n := by
  induction n with
  | zero => simp [npowBinRec_zero]
  | succ n ih => rw [npowBinRec_succ, ih, pow_succ]

private theorem absBounds_lo_nonneg (I : Interval β) : 0 ≤ (absBounds I).lo := by
  unfold absBounds
  split
  · exact ‹0 ≤ I.lo›
  · split
    · exact neg_nonneg.mpr ‹I.hi ≤ 0›
    · exact le_rfl

private theorem abs_bounds (I : Interval β) {x : β} (hx : I.lo ≤ x ∧ x ≤ I.hi) :
    (absBounds I).lo ≤ |x| ∧ |x| ≤ (absBounds I).hi := by
  unfold absBounds
  split
  · simpa only [abs_of_nonneg (le_trans ‹0 ≤ I.lo› hx.1)] using hx
  · split
    · simpa only [abs_of_nonpos (le_trans hx.2 ‹I.hi ≤ 0›)] using
        And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)
    · refine ⟨abs_nonneg x, abs_le.mpr ⟨?_, hx.2.trans (le_max_right _ _)⟩⟩
      have hneg : -max (-I.lo) I.hi ≤ I.lo := by
        simpa using neg_le_neg (le_max_left (-I.lo) I.hi)
      exact hneg.trans hx.1

private theorem square_bounds (I : Interval β) {x : β} (hx : I.lo ≤ x ∧ x ≤ I.hi) :
    (squareBounds I).lo ≤ x ^ 2 ∧ x ^ 2 ≤ (squareBounds I).hi := by
  have ha := abs_bounds I hx
  simpa only [squareBounds, ← pow_two, sq_abs] using
    And.intro (pow_le_pow_left₀ (absBounds_lo_nonneg I) ha.1 2)
      (pow_le_pow_left₀ (abs_nonneg x) ha.2 2)

private theorem pow_bounds (I : Interval β) (n : ℕ) {x : β}
    (hx : I.lo ≤ x ∧ x ≤ I.hi) :
    (powBounds I n).lo ≤ x ^ n ∧ x ^ n ≤ (powBounds I n).hi := by
  unfold powBounds
  split
  · subst n
    simp [point]
  · split
    · have hn := Nat.even_iff.mpr ‹n % 2 = 0›
      have ha := abs_bounds I hx
      simpa only [binaryPow_eq_pow, hn.pow_abs] using
        And.intro (pow_le_pow_left₀ (absBounds_lo_nonneg I) ha.1 n)
          (pow_le_pow_left₀ (abs_nonneg x) ha.2 n)
    · have hn : Odd n :=
        Nat.not_even_iff_odd.mp (fun hn => ‹n % 2 ≠ 0› (Nat.even_iff.mp hn))
      simpa only [binaryPow_eq_pow] using
        And.intro (hn.strictMono_pow.monotone hx.1) (hn.strictMono_pow.monotone hx.2)

/-- Every successful absolute-value operation encloses the absolute value of each member. -/
theorem contains_abs? (R : OutwardRounding α β) {I K : Interval α}
    (h : abs? R I = some K) {x : β} (hx : I.Contains R.decode x) :
    K.Contains R.decode |x| :=
  contains_liftUnary? R _ _ (fun a _ hx => abs_bounds a hx) h hx

/-- Every successful square encloses the square of each member, including across zero. -/
theorem contains_square? (R : OutwardRounding α β) {I K : Interval α}
    (h : square? R I = some K) {x : β} (hx : I.Contains R.decode x) :
    K.Contains R.decode (x ^ 2) :=
  contains_liftUnary? R _ _ (fun a _ hx => square_bounds a hx) h hx

/-- Every successful natural-power operation encloses the corresponding power of each member. -/
theorem contains_pow? (R : OutwardRounding α β) {I K : Interval α} (n : ℕ)
    (h : pow? R I n = some K) {x : β} (hx : I.Contains R.decode x) :
    K.Contains R.decode (x ^ n) :=
  contains_liftUnary? R _ _ (fun a _ hx => pow_bounds a n hx) h hx

omit [Field β] [IsStrictOrderedRing β] in
/-- Pointwise minimum preserves containment. -/
theorem contains_min? (R : OutwardRounding α β) {I J K : Interval α}
    (h : min? R I J = some K) {x y : β}
    (hx : I.Contains R.decode x) (hy : J.Contains R.decode y) :
    K.Contains R.decode (min x y) :=
  contains_liftBinary? R _ _
    (fun _ _ _ _ hx hy => ⟨min_le_min hx.1 hy.1, min_le_min hx.2 hy.2⟩) h hx hy

omit [Field β] [IsStrictOrderedRing β] in
/-- Pointwise maximum preserves containment. -/
theorem contains_max? (R : OutwardRounding α β) {I J K : Interval α}
    (h : max? R I J = some K) {x y : β}
    (hx : I.Contains R.decode x) (hy : J.Contains R.decode y) :
    K.Contains R.decode (max x y) :=
  contains_liftBinary? R _ _
    (fun _ _ _ _ hx hy => ⟨max_le_max hx.1 hy.1, max_le_max hx.2 hy.2⟩) h hx hy

private theorem inv_bounds (I : Interval β) {x : β} (hx : I.lo ≤ x ∧ x ≤ I.hi)
    (hzero : I.hi < 0 ∨ 0 < I.lo) : I.hi⁻¹ ≤ x⁻¹ ∧ x⁻¹ ≤ I.lo⁻¹ := by
  rcases hzero with hneg | hpos
  · simpa only [one_div] using
      And.intro (one_div_le_one_div_of_neg_of_le hneg hx.2)
        (one_div_le_one_div_of_neg_of_le (hx.2.trans_lt hneg) hx.1)
  · simpa only [one_div] using
      And.intro (one_div_le_one_div_of_le (hpos.trans_le hx.1) hx.2)
        (one_div_le_one_div_of_le hpos hx.1)

/-- Every successful reciprocal encloses the inverse of each member of a nonzero range. -/
theorem contains_inv? (R : OutwardRounding α β) {I K : Interval α}
    (h : inv? R I = some K) {x : β} (hx : I.Contains R.decode x) :
    K.Contains R.decode x⁻¹ := by
  cases ha : I.decode? R.decode with
  | none => simp [inv?, ha] at h
  | some a =>
    by_cases hzero : a.hi < 0 ∨ 0 < a.lo
    · exact contains_encloseInterval? R (by simpa [inv?, ha, hzero] using h)
        (inv_bounds a ((contains_iff_of_decode? ha x).mp hx) hzero)
    · simp [inv?, ha, hzero] at h

omit [IsStrictOrderedRing β] in
/-- A range containing zero is rejected by reciprocal, including a zero endpoint. -/
theorem inv?_eq_none_of_contains_zero (R : OutwardRounding α β) {I : Interval α}
    (hzero : I.Contains R.decode 0) : inv? R I = none := by
  cases ha : I.decode? R.decode with
  | none => simp [inv?, ha]
  | some a =>
    obtain ⟨hlo, hhi⟩ := (contains_iff_of_decode? ha 0).mp hzero
    simp [inv?, ha, not_lt_of_ge hlo, not_lt_of_ge hhi]

omit [Field β] [IsStrictOrderedRing β] in
private theorem decode_hull? (R : OutwardRounding α β) {I J K : Interval α}
    {a b : Interval β} (ha : I.decode? R.decode = some a)
    (hb : J.decode? R.decode = some b) (h : hull? R I J = some K) :
    K.decode? R.decode = some ⟨min a.lo b.lo, max a.hi b.hi⟩ := by
  by_cases horder : a.lo ≤ a.hi ∧ b.lo ≤ b.hi
  · simp only [hull?, ha, hb, ite_eq_left horder, Option.some.injEq] at h
    subst K
    obtain ⟨ha₁, ha₂⟩ := (decode?_eq_some_iff _ _ _).mp ha
    obtain ⟨hb₁, hb₂⟩ := (decode?_eq_some_iff _ _ _).mp hb
    by_cases hlo : a.lo ≤ b.lo <;> by_cases hhi : a.hi ≤ b.hi <;>
      simp [decode?, hlo, hhi, min_def, max_def, ha₁, ha₂, hb₁, hb₂]
  · simp [hull?, ha, hb, horder] at h

omit [Field β] [IsStrictOrderedRing β] in
private theorem decode_intersect? (R : OutwardRounding α β) {I J K : Interval α}
    {a b : Interval β} (ha : I.decode? R.decode = some a)
    (hb : J.decode? R.decode = some b) (h : intersect? R I J = some K) :
    K.decode? R.decode = some ⟨max a.lo b.lo, min a.hi b.hi⟩ := by
  by_cases horder : max a.lo b.lo ≤ min a.hi b.hi
  · simp only [intersect?, ha, hb, ite_eq_left horder, Option.some.injEq] at h
    subst K
    obtain ⟨ha₁, ha₂⟩ := (decode?_eq_some_iff _ _ _).mp ha
    obtain ⟨hb₁, hb₂⟩ := (decode?_eq_some_iff _ _ _).mp hb
    by_cases hlo : a.lo ≤ b.lo <;> by_cases hhi : a.hi ≤ b.hi <;>
      simp [decode?, hlo, hhi, min_def, max_def, ha₁, ha₂, hb₁, hb₂]
  · simp [intersect?, ha, hb, horder] at h

omit [Field β] [IsStrictOrderedRing β] in
/-- A successful hull contains every member of either input interval. -/
theorem contains_hull? (R : OutwardRounding α β) {I J K : Interval α}
    (h : hull? R I J = some K) {x : β}
    (hx : I.Contains R.decode x ∨ J.Contains R.decode x) : K.Contains R.decode x := by
  cases ha : I.decode? R.decode with
  | none => simp [hull?, ha] at h
  | some a =>
    cases hb : J.decode? R.decode with
    | none => simp [hull?, ha, hb] at h
    | some b =>
      apply (contains_iff_of_decode? (decode_hull? R ha hb h) x).mpr
      rcases hx with hx | hx
      · obtain ⟨hlo, hhi⟩ := (contains_iff_of_decode? ha x).mp hx
        exact ⟨(min_le_left _ _).trans hlo, hhi.trans (le_max_left _ _)⟩
      · obtain ⟨hlo, hhi⟩ := (contains_iff_of_decode? hb x).mp hx
        exact ⟨(min_le_right _ _).trans hlo, hhi.trans (le_max_right _ _)⟩

omit [Field β] [IsStrictOrderedRing β] in
/-- A successful intersection contains every common member of the input intervals. -/
theorem contains_intersect? (R : OutwardRounding α β) {I J K : Interval α}
    (h : intersect? R I J = some K) {x : β}
    (hx : I.Contains R.decode x) (hy : J.Contains R.decode x) :
    K.Contains R.decode x := by
  cases ha : I.decode? R.decode with
  | none => simp [intersect?, ha] at h
  | some a =>
    cases hb : J.decode? R.decode with
    | none => simp [intersect?, ha, hb] at h
    | some b =>
      obtain ⟨ha₁, ha₂⟩ := (contains_iff_of_decode? ha x).mp hx
      obtain ⟨hb₁, hb₂⟩ := (contains_iff_of_decode? hb x).mp hy
      exact (contains_iff_of_decode? (decode_intersect? R ha hb h) x).mpr
        ⟨max_le ha₁ hb₁, le_min ha₂ hb₂⟩

private theorem cast_absBounds (a : Interval ℚ) :
    (absBounds a).map (fun q : ℚ => (q : ℝ)) = absBounds (a.map (fun q : ℚ => (q : ℝ))) := by
  by_cases hlo : 0 ≤ a.lo
  · have hlo' : (0 : ℝ) ≤ a.lo := by exact_mod_cast hlo
    simp [absBounds, map, hlo, hlo']
  · have hlo' : ¬(0 : ℝ) ≤ a.lo := by exact_mod_cast hlo
    by_cases hhi : a.hi ≤ 0
    · have hhi' : (a.hi : ℝ) ≤ 0 := by exact_mod_cast hhi
      simp [absBounds, map, hlo, hlo', hhi, hhi']
    · have hhi' : ¬(a.hi : ℝ) ≤ 0 := by exact_mod_cast hhi
      simp [absBounds, map, hlo, hlo', hhi, hhi']

private theorem cast_squareBounds (a : Interval ℚ) :
    (squareBounds a).map (fun q : ℚ => (q : ℝ)) =
      squareBounds (a.map (fun q : ℚ => (q : ℝ))) := by
  have h := congrArg (fun b : Interval ℝ => (⟨b.lo * b.lo, b.hi * b.hi⟩ : Interval ℝ))
    (cast_absBounds a)
  simpa only [squareBounds, map, Rat.cast_mul] using h

private theorem cast_powBounds (a : Interval ℚ) (n : ℕ) :
    (powBounds a n).map (fun q : ℚ => (q : ℝ)) =
      powBounds (a.map (fun q : ℚ => (q : ℝ))) n := by
  unfold powBounds
  split
  · simp [point, map]
  · split
    · have h := congrArg (fun b : Interval ℝ => (⟨b.lo ^ n, b.hi ^ n⟩ : Interval ℝ))
        (cast_absBounds a)
      simpa only [map, binaryPow_eq_pow, Rat.cast_pow] using h
    · simp only [map, binaryPow_eq_pow, Rat.cast_pow]

/-- Rational endpoint absolute value encloses absolute values of arbitrary real members. -/
theorem containsReal_abs? (R : OutwardRounding α ℚ) {I K : Interval α}
    (h : abs? R I = some K) {x : ℝ} (hx : I.ContainsReal R.decode x) :
    K.ContainsReal R.decode |x| := by
  apply containsReal_liftUnary? R _ abs ?_ h hx
  intro a x hx
  have hb := abs_bounds (a.map (fun q : ℚ => (q : ℝ))) hx
  rw [← cast_absBounds] at hb
  exact hb

/-- Rational endpoint squaring encloses squares of arbitrary real members. -/
theorem containsReal_square? (R : OutwardRounding α ℚ) {I K : Interval α}
    (h : square? R I = some K) {x : ℝ} (hx : I.ContainsReal R.decode x) :
    K.ContainsReal R.decode (x ^ 2) := by
  apply containsReal_liftUnary? R _ (· ^ 2) ?_ h hx
  intro a x hx
  have hb := square_bounds (a.map (fun q : ℚ => (q : ℝ))) hx
  rw [← cast_squareBounds] at hb
  exact hb

/-- Rational endpoint powers enclose natural powers of arbitrary real members. -/
theorem containsReal_pow? (R : OutwardRounding α ℚ) {I K : Interval α} (n : ℕ)
    (h : pow? R I n = some K) {x : ℝ} (hx : I.ContainsReal R.decode x) :
    K.ContainsReal R.decode (x ^ n) := by
  apply containsReal_liftUnary? R _ (· ^ n) ?_ h hx
  intro a x hx
  have hb := pow_bounds (a.map (fun q : ℚ => (q : ℝ))) n hx
  rw [← cast_powBounds] at hb
  exact hb

/-- Rational endpoint minimum encloses minima of arbitrary real members. -/
theorem containsReal_min? (R : OutwardRounding α ℚ) {I J K : Interval α}
    (h : min? R I J = some K) {x y : ℝ}
    (hx : I.ContainsReal R.decode x) (hy : J.ContainsReal R.decode y) :
    K.ContainsReal R.decode (min x y) := by
  apply containsReal_liftBinary? R _ min ?_ h hx hy
  intro a b x y hx hy
  simpa using And.intro (min_le_min hx.1 hy.1) (min_le_min hx.2 hy.2)

/-- Rational endpoint maximum encloses maxima of arbitrary real members. -/
theorem containsReal_max? (R : OutwardRounding α ℚ) {I J K : Interval α}
    (h : max? R I J = some K) {x y : ℝ}
    (hx : I.ContainsReal R.decode x) (hy : J.ContainsReal R.decode y) :
    K.ContainsReal R.decode (max x y) := by
  apply containsReal_liftBinary? R _ max ?_ h hx hy
  intro a b x y hx hy
  simpa using And.intro (max_le_max hx.1 hy.1) (max_le_max hx.2 hy.2)

/-- Rational endpoint reciprocal encloses inverses of arbitrary real members. -/
theorem containsReal_inv? (R : OutwardRounding α ℚ) {I K : Interval α}
    (h : inv? R I = some K) {x : ℝ} (hx : I.ContainsReal R.decode x) :
    K.ContainsReal R.decode x⁻¹ := by
  cases ha : I.decode? R.decode with
  | none => simp [inv?, ha] at h
  | some a =>
    by_cases hzero : a.hi < 0 ∨ 0 < a.lo
    · apply containsReal_encloseInterval? R (by simpa [inv?, ha, hzero] using h)
      have hzero' : (a.hi : ℝ) < 0 ∨ 0 < (a.lo : ℝ) := by exact_mod_cast hzero
      simpa [map] using inv_bounds (a.map (fun q : ℚ => (q : ℝ)))
        ((containsReal_iff_of_decode? ha x).mp hx) hzero'
    · simp [inv?, ha, hzero] at h

/-- The hull contains every real member of either input interval. -/
theorem containsReal_hull? (R : OutwardRounding α ℚ) {I J K : Interval α}
    (h : hull? R I J = some K) {x : ℝ}
    (hx : I.ContainsReal R.decode x ∨ J.ContainsReal R.decode x) :
    K.ContainsReal R.decode x := by
  cases ha : I.decode? R.decode with
  | none => simp [hull?, ha] at h
  | some a =>
    cases hb : J.decode? R.decode with
    | none => simp [hull?, ha, hb] at h
    | some b =>
      apply (containsReal_iff_of_decode? (decode_hull? R ha hb h) x).mpr
      simp only [Rat.cast_min, Rat.cast_max]
      rcases hx with hx | hx
      · obtain ⟨hlo, hhi⟩ := (containsReal_iff_of_decode? ha x).mp hx
        exact ⟨(min_le_left _ _).trans hlo, hhi.trans (le_max_left _ _)⟩
      · obtain ⟨hlo, hhi⟩ := (containsReal_iff_of_decode? hb x).mp hx
        exact ⟨(min_le_right _ _).trans hlo, hhi.trans (le_max_right _ _)⟩

/-- The intersection contains every common real member of the input intervals. -/
theorem containsReal_intersect? (R : OutwardRounding α ℚ) {I J K : Interval α}
    (h : intersect? R I J = some K) {x : ℝ}
    (hx : I.ContainsReal R.decode x) (hy : J.ContainsReal R.decode x) :
    K.ContainsReal R.decode x := by
  cases ha : I.decode? R.decode with
  | none => simp [intersect?, ha] at h
  | some a =>
    cases hb : J.decode? R.decode with
    | none => simp [intersect?, ha, hb] at h
    | some b =>
      obtain ⟨ha₁, ha₂⟩ := (containsReal_iff_of_decode? ha x).mp hx
      obtain ⟨hb₁, hb₂⟩ := (containsReal_iff_of_decode? hb x).mp hy
      apply (containsReal_iff_of_decode? (decode_intersect? R ha hb h) x).mpr
      simpa only [Rat.cast_max, Rat.cast_min] using
        And.intro (max_le ha₁ hb₁) (le_min ha₂ hb₂)

end FloatLib.Numerics.Interval
