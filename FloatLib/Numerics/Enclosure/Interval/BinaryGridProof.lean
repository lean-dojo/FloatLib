/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.BinaryGrid
public import FloatLib.Numerics.Enclosure.Interval.Real
public import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Real containment for integer binary-grid intervals

Signed integer division supplies floor and ceiling bounds before interpretation in the reals.
The four-corner theorems then enclose every real member of the input intervals, including values
between grid points. The runtime definitions compute entirely with integers after input conversion.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval.BinaryGrid

/-- The shift-based scale is exactly the corresponding power of two. -/
theorem scale_eq_pow (precision : Nat) : scale precision = (2 : Int) ^ precision := by
  simp [scale, Int.shiftLeft_eq]

/-- Every binary grid has a strictly positive scale. -/
theorem scale_pos (precision : Nat) : 0 < scale precision := by
  rw [scale_eq_pow]
  positivity

/-- Real interpretation of a coefficient, used only in mathematical statements and proofs. -/
noncomputable def value (precision : Nat) (z : Int) : ℝ :=
  (z : ℝ) / (scale precision : ℝ)

private theorem real_scale_pos (precision : Nat) : (0 : ℝ) < scale precision := by
  exact_mod_cast scale_pos precision

/-- Rational decoding agrees with the real interpretation of the coefficient. -/
@[simp]
theorem cast_toRat (precision : Nat) (z : Int) :
    (toRat precision z : ℝ) = value precision z := by
  simp [toRat, value, Rat.divInt_eq_div]

/-- Real membership in a binary-grid interval is given by its scaled endpoint inequalities. -/
@[simp]
theorem containsReal_iff (precision : Nat) (I : Interval Int) (x : ℝ) :
    I.ContainsReal (decode precision) x ↔
      value precision I.lo ≤ x ∧ x ≤ value precision I.hi := by
  simp [ContainsReal, Contains, decode]

/-- A zero coefficient represents zero on every grid. -/
@[simp]
theorem value_zero (precision : Nat) : value precision 0 = 0 := by
  simp [value]

/-- The grid scale is the coefficient representing one. -/
@[simp]
theorem value_scale (precision : Nat) : value precision (scale precision) = 1 := by
  exact div_self (ne_of_gt (real_scale_pos precision))

/-- Negating a coefficient negates its real value. -/
@[simp]
theorem value_neg (precision : Nat) (z : Int) :
    value precision (-z) = -value precision z := by
  simp [value, neg_div]

/-- Coefficient addition is exact on a common grid. -/
@[simp]
theorem value_add (precision : Nat) (a b : Int) :
    value precision (a + b) = value precision a + value precision b := by
  simp [value, add_div]

/-- Coefficient subtraction is exact on a common grid. -/
@[simp]
theorem value_sub (precision : Nat) (a b : Int) :
    value precision (a - b) = value precision a - value precision b := by
  simp [value, sub_div]

/-- Non-strict comparison of coefficients agrees with comparison of their real values. -/
@[simp]
theorem value_le_value_iff (precision : Nat) (a b : Int) :
    value precision a ≤ value precision b ↔ a ≤ b := by
  simp [value, div_le_div_iff_of_pos_right (real_scale_pos precision)]

/-- Strict comparison of coefficients agrees with comparison of their real values. -/
@[simp]
theorem value_lt_value_iff (precision : Nat) (a b : Int) :
    value precision a < value precision b ↔ a < b := by
  simp [value, div_lt_div_iff_of_pos_right (real_scale_pos precision)]

/-- Taking the smaller coefficient gives the smaller real value. -/
@[simp]
theorem value_min (precision : Nat) (a b : Int) :
    value precision (min a b) = min (value precision a) (value precision b) := by
  simp [value, min_div_div_right (real_scale_pos precision).le]

/-- Taking the larger coefficient gives the larger real value. -/
@[simp]
theorem value_max (precision : Nat) (a b : Int) :
    value precision (max a b) = max (value precision a) (value precision b) := by
  simp [value, max_div_div_right (real_scale_pos precision).le]

private theorem fdiv_eq_rat_floor_of_nonneg (a b : Int) (hb : 0 ≤ b) :
    a.fdiv b = ⌊((a : ℚ) / (b : ℚ))⌋ := by
  lift b to Nat using hb
  rw [Int.fdiv_eq_ediv_of_nonneg a (Int.natCast_nonneg _)]
  exact (Rat.floor_intCast_div_natCast a _).symm

private theorem fdiv_eq_rat_floor (a b : Int) :
    a.fdiv b = ⌊((a : ℚ) / (b : ℚ))⌋ := by
  rcases le_total 0 b with hb | hb
  · exact fdiv_eq_rat_floor_of_nonneg a b hb
  · simpa using fdiv_eq_rat_floor_of_nonneg (-a) (-b) (neg_nonneg.mpr hb)

private theorem divBounds_rat_bounds (a b : Int) (hb : b ≠ 0) :
    ((divBounds a b).lo : ℚ) ≤ (a : ℚ) / b ∧
      (a : ℚ) / b ≤ ((divBounds a b).hi : ℚ) := by
  refine ⟨?_, ?_⟩
  · change (a.fdiv b : ℚ) ≤ _
    rw [fdiv_eq_rat_floor]
    exact Int.floor_le _
  · dsimp [divBounds]
    split_ifs with h
    · have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
      apply le_of_eq
      apply (div_eq_iff hb').2
      exact_mod_cast h.symm
    · rw [Int.cast_add, Int.cast_one, fdiv_eq_rat_floor]
      exact (Int.lt_floor_add_one _).le

/-- The integer quotient bounds enclose exact division in any ordered field. -/
theorem divBounds_bounds {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (a b : Int) (hb : b ≠ 0) :
    ((divBounds a b).lo : α) ≤ (a : α) / b ∧
      (a : α) / b ≤ ((divBounds a b).hi : α) := by
  have h := divBounds_rat_bounds a b hb
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- The signed downward shift is below the exact scaled coefficient. -/
theorem roundDown_le (precision : Nat) (z : Int) :
    (roundDown precision z : ℝ) ≤ value precision z := by
  have h := (divBounds_bounds (α := ℝ) z (scale precision) (ne_of_gt (scale_pos precision))).1
  change (z.fdiv (scale precision) : ℝ) ≤ _ at h
  rw [Int.fdiv_eq_ediv_of_nonneg _ (scale_pos precision).le] at h
  simpa [roundDown, value, scale_eq_pow, Int.shiftRight_eq_div_pow] using h

/-- The signed upward shift is above the exact scaled coefficient. -/
theorem le_roundUp (precision : Nat) (z : Int) :
    value precision z ≤ (roundUp precision z : ℝ) := by
  have h := neg_le_neg (roundDown_le precision (-z))
  simpa [roundUp, roundDown] using h

/-- Conversion from an exact rational produces a containing binary-grid interval. -/
theorem contains_enclose (precision : Nat) (q : ℚ) :
    (enclose precision q).Contains (decode precision) q := by
  have hs : (0 : ℚ) < scale precision := by exact_mod_cast scale_pos precision
  have h := divBounds_bounds (α := ℚ) (q.num <<< precision) q.den
    (by exact_mod_cast q.den_nz)
  have hq : (((q.num <<< precision : Int) : ℚ) / q.den) /
      (scale precision : ℚ) = q := by
    rw [Int.shiftLeft_eq, Int.cast_mul, ← scale_eq_pow, mul_div_right_comm,
      mul_div_cancel_right₀ _ (ne_of_gt hs)]
    exact Rat.num_div_den q
  refine ⟨toRat precision (enclose precision q).lo,
    toRat precision (enclose precision q).hi, rfl, rfl, ?_, ?_⟩
  · simpa [enclose, toRat, Rat.divInt_eq_div, hq] using div_le_div_of_nonneg_right h.1 hs.le
  · simpa [enclose, toRat, Rat.divInt_eq_div, hq] using div_le_div_of_nonneg_right h.2 hs.le

/-- Total outward rounding from exact rationals onto a fixed binary grid. -/
def rounding (precision : Nat) : OutwardRounding Int ℚ where
  decode := decode precision
  enclose? q := some (enclose precision q)
  sound := by
    intro q I h
    cases Option.some.inj h
    exact contains_enclose precision q

/-- Rational conversion contains the corresponding real number. -/
theorem containsReal_enclose (precision : Nat) (q : ℚ) :
    (enclose precision q).ContainsReal (decode precision) (q : ℝ) := by
  obtain ⟨lo, hi, hlo, hhi, hl, hh⟩ := contains_enclose precision q
  exact ⟨lo, hi, by simp [hlo], by simp [hhi], by exact_mod_cast hl, by exact_mod_cast hh⟩

/-- Exact grid negation encloses the negative of every real input member. -/
theorem containsReal_neg (precision : Nat) {I : Interval Int} {x : ℝ}
    (hx : I.ContainsReal (decode precision) x) :
    (neg I).ContainsReal (decode precision) (-x) := by
  rw [containsReal_iff] at hx ⊢
  simpa [neg] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

/-- Exact grid addition encloses the sum of arbitrary real input members. -/
theorem containsReal_add (precision : Nat) {I J : Interval Int} {x y : ℝ}
    (hx : I.ContainsReal (decode precision) x)
    (hy : J.ContainsReal (decode precision) y) :
    (add I J).ContainsReal (decode precision) (x + y) := by
  rw [containsReal_iff] at hx hy ⊢
  simpa [add] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

/-- Exact grid subtraction encloses the difference of arbitrary real input members. -/
theorem containsReal_sub (precision : Nat) {I J : Interval Int} {x y : ℝ}
    (hx : I.ContainsReal (decode precision) x)
    (hy : J.ContainsReal (decode precision) y) :
    (sub I J).ContainsReal (decode precision) (x - y) := by
  rw [containsReal_iff] at hx hy ⊢
  simpa [sub] using And.intro (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

private theorem value_roundDown_le (precision : Nat) (z : Int) :
    value precision (roundDown precision z) ≤
      value precision z / (scale precision : ℝ) :=
  div_le_div_of_nonneg_right (roundDown_le precision z) (real_scale_pos precision).le

private theorem le_value_roundUp (precision : Nat) (z : Int) :
    value precision z / (scale precision : ℝ) ≤ value precision (roundUp precision z) :=
  div_le_div_of_nonneg_right (le_roundUp precision z) (real_scale_pos precision).le

private theorem value_product_scaled (precision : Nat) (a b : Int) :
    value precision (a * b) / (scale precision : ℝ) =
      value precision a * value precision b := by
  simp only [value, Int.cast_mul]
  ring

/-- Integer four-corner multiplication encloses products of arbitrary real input members. -/
theorem containsReal_mul (precision : Nat) {I J : Interval Int} {x y : ℝ}
    (hx : I.ContainsReal (decode precision) x)
    (hy : J.ContainsReal (decode precision) y) :
    (mul precision I J).ContainsReal (decode precision) (x * y) := by
  rw [containsReal_iff] at hx hy ⊢
  have hxy := mul_bounds_Icc (value precision I.lo) (value precision I.hi)
    (value precision J.lo) (value precision J.hi) x y hx hy
  refine ⟨(value_roundDown_le precision _).trans ?_,
    (le_value_roundUp precision _).trans' ?_⟩
  · simpa only [minOfFour, value_min,
      ← min_div_div_right (real_scale_pos precision).le, value_product_scaled] using hxy.1
  · simpa only [maxOfFour, value_max,
      ← max_div_div_right (real_scale_pos precision).le, value_product_scaled] using hxy.2

private theorem value_divBounds (precision : Nat) (a b : Int) (hb : b ≠ 0) :
    value precision (divBounds (a <<< precision) b).lo ≤
        value precision a / value precision b ∧
      value precision a / value precision b ≤
        value precision (divBounds (a <<< precision) b).hi := by
  have h := divBounds_bounds (α := ℝ) (a <<< precision) b hb
  have hs := real_scale_pos precision
  have hq : (((a <<< precision : Int) : ℝ) / b) / (scale precision : ℝ) =
      value precision a / value precision b := by
    rw [Int.shiftLeft_eq, Int.cast_mul, ← scale_eq_pow]
    dsimp [value]
    field_simp
  constructor
  · have hl := div_le_div_of_nonneg_right h.1 hs.le
    rw [hq] at hl
    simpa only [value] using hl
  · have hh := div_le_div_of_nonneg_right h.2 hs.le
    rw [hq] at hh
    simpa only [value] using hh

/-- Successful integer division encloses quotients of arbitrary real input members. -/
theorem containsReal_div? (precision : Nat) {I J K : Interval Int}
    (h : div? precision I J = some K) {x y : ℝ}
    (hx : I.ContainsReal (decode precision) x)
    (hy : J.ContainsReal (decode precision) y) :
    K.ContainsReal (decode precision) (x / y) := by
  rw [containsReal_iff] at hx hy ⊢
  have hJ : J.lo ≤ J.hi := (value_le_value_iff precision _ _).1 (hy.1.trans hy.2)
  by_cases hz : J.hi < 0 ∨ 0 < J.lo
  · have hlo : J.lo ≠ 0 := by omega
    have hhi : J.hi ≠ 0 := by omega
    have hz' : value precision J.hi < 0 ∨ 0 < value precision J.lo := by
      simpa only [← value_zero precision, value_lt_value_iff] using hz
    have hxy := div_bounds_Icc (value precision I.lo) (value precision I.hi)
      (value precision J.lo) (value precision J.hi) x y hx hy hz'
    have ha := value_divBounds precision I.lo J.lo hlo
    have hb := value_divBounds precision I.lo J.hi hhi
    have hc := value_divBounds precision I.hi J.lo hlo
    have hd := value_divBounds precision I.hi J.hi hhi
    simp only [div?, hz, ↓reduceIte, Option.some.injEq] at h
    subst K
    simpa only [minOfFour, maxOfFour, value_min, value_max] using
      And.intro
        ((min_le_min (min_le_min ha.1 hb.1) (min_le_min hc.1 hd.1)).trans hxy.1)
        (hxy.2.trans (max_le_max (max_le_max ha.2 hb.2) (max_le_max hc.2 hd.2)))
  · simp [div?, hz] at h

/-- Exact grid absolute value encloses the absolute value of every real input member. -/
theorem containsReal_abs (precision : Nat) {I : Interval Int} {x : ℝ}
    (hx : I.ContainsReal (decode precision) x) :
    (abs I).ContainsReal (decode precision) |x| := by
  rw [containsReal_iff] at hx ⊢
  by_cases hlo : 0 ≤ I.lo
  · have hl : 0 ≤ value precision I.lo := by
      simpa only [← value_zero precision, value_le_value_iff] using hlo
    simpa [abs, hlo, abs_of_nonneg (hl.trans hx.1)] using hx
  · by_cases hhi : I.hi ≤ 0
    · have hh : value precision I.hi ≤ 0 := by
        simpa only [← value_zero precision, value_le_value_iff] using hhi
      simpa [abs, hlo, hhi, neg, abs_of_nonpos (hx.2.trans hh)] using
        And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)
    · simp only [abs, hlo, hhi, ↓reduceIte, value_zero, value_max, value_neg]
      refine ⟨abs_nonneg x, abs_le.2 ⟨?_, ?_⟩⟩
      · have hl : -max (-value precision I.lo) (value precision I.hi) ≤
            value precision I.lo := by
          simpa using neg_le_neg
            (le_max_left (-value precision I.lo) (value precision I.hi))
        exact hl.trans hx.1
      · exact hx.2.trans (le_max_right _ _)

private theorem mul_self_le_max_of_mem {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    x * x ≤ max (a * a) (b * b) := by
  rcases le_total 0 x with hx0 | hx0
  · exact (mul_self_le_mul_self hx0 hx.2).trans (le_max_right _ _)
  · have h := mul_self_le_mul_self (neg_nonneg.mpr hx0) (neg_le_neg hx.1)
    simpa only [neg_mul_neg] using h.trans (le_max_left ((-a) * (-a)) (b * b))

/-- The specialized square encloses the square of every real input member. -/
theorem containsReal_square (precision : Nat) {I : Interval Int} {x : ℝ}
    (hx : I.ContainsReal (decode precision) x) :
    (square precision I).ContainsReal (decode precision) (x ^ 2) := by
  rw [containsReal_iff] at hx ⊢
  refine ⟨(value_roundDown_le precision _).trans ?_,
    (le_value_roundUp precision _).trans' ?_⟩
  · change value precision
        (if 0 ≤ I.lo then I.lo * I.lo else if I.hi ≤ 0 then I.hi * I.hi else 0) /
        (scale precision : ℝ) ≤ x ^ 2
    split_ifs with hlo hhi
    · have hl : 0 ≤ value precision I.lo := by
        simpa only [← value_zero precision, value_le_value_iff] using hlo
      simpa only [value_product_scaled, pow_two] using mul_self_le_mul_self hl hx.1
    · have hh : value precision I.hi ≤ 0 := by
        simpa only [← value_zero precision, value_le_value_iff] using hhi
      simpa only [value_product_scaled, pow_two, neg_mul_neg] using
        mul_self_le_mul_self (neg_nonneg.mpr hh) (neg_le_neg hx.2)
    · simpa using sq_nonneg x
  · simpa only [value_max, ← max_div_div_right (real_scale_pos precision).le,
      value_product_scaled, pow_two] using mul_self_le_max_of_mem hx

private theorem containsReal_pow_internal (precision : Nat) {I : Interval Int} {x : ℝ}
    (hx : I.ContainsReal (decode precision) x) (n : Nat) :
    (Internal.pow precision I n).ContainsReal (decode precision) (x ^ n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [Internal.pow, containsReal_iff, point]
    · by_cases hone : n = 1
      · subst n
        simpa [Internal.pow] using hx
      · have hhalf : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
        have hs := containsReal_square precision (ih (n / 2) hhalf)
        rw [Internal.pow, dite_eq_right hn, ite_eq_right hone]
        by_cases heven : n % 2 = 0
        · rw [ite_eq_left heven]
          have hn' : n / 2 * 2 = n := by omega
          simpa only [← pow_mul, hn'] using hs
        · rw [ite_eq_right heven]
          have hn' : n / 2 * 2 + 1 = n := by omega
          simpa only [← pow_mul, ← pow_succ, hn'] using containsReal_mul precision hs hx

/-- Parity-aware endpoint bounds enclose every natural power of an arbitrary real input member. -/
theorem containsReal_pow (precision : Nat) {I : Interval Int} {x : ℝ}
    (hx : I.ContainsReal (decode precision) x) (n : Nat) :
    (pow precision I n).ContainsReal (decode precision) (x ^ n) := by
  by_cases hn : n = 0
  · subst n
    simp [pow, containsReal_iff, point]
  by_cases hone : n = 1
  · subst n
    simpa [pow] using hx
  rw [pow, ite_eq_right hn, ite_eq_right hone]
  by_cases heven : n % 2 = 0
  · rw [ite_eq_left heven]
    simpa only [(Nat.even_iff.mpr heven).pow_abs x] using
      containsReal_pow_internal precision (containsReal_abs precision hx) n
  · rw [ite_eq_right heven]
    by_cases hpoint : I.lo = I.hi
    · rw [ite_eq_left hpoint]
      exact containsReal_pow_internal precision hx n
    · rw [ite_eq_right hpoint]
      have hodd : Odd n := Nat.odd_iff.mpr (by omega)
      have hlo := containsReal_pow_internal precision
        (I := point I.lo) (x := value precision I.lo)
        (by simp [containsReal_iff, point]) n
      have hhi := containsReal_pow_internal precision
        (I := point I.hi) (x := value precision I.hi)
        (by simp [containsReal_iff, point]) n
      rw [containsReal_iff] at hx hlo hhi ⊢
      exact ⟨hlo.1.trans (hodd.pow_le_pow.mpr hx.1), (hodd.pow_le_pow.mpr hx.2).trans hhi.2⟩

end FloatLib.Numerics.Interval.BinaryGrid
