/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Rounding.Comparison.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Zero
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Directed.Proof

/-!
# The decimal recommended functions are correctly rounded in every direction

For every decimal format, a finite operand in the domain and each of the five rounding
directions, a function of `Transcendentals.CorrectlyRounded` meets the contract `RoundsTo` for
the real function at the operand's exact value. With `roundTo f mode r` the rounding of `r` in
the direction `mode` on the grid of the format with an unbounded exponent range, the result is
a valid finite datum that denotes `roundTo f mode r` when that value is at most the largest
finite magnitude, with `inexact` exactly when it is not `r` and `underflow` exactly when
moreover `|r|` is below the least normal magnitude; otherwise it is the overflow result of the
direction with `overflow` and `inexact`. The result has the sign of `r`.

* `apply_roundsTo`: one theorem for the 26 functions of one argument, at an operand whose exact
  value `q` is in `Function.Domain` with a real value that is not zero. Each named function
  (`exp2`, `sin`, `atanh`, ...) is `apply` at its member by definition.
* `exp_roundsTo`, `expm1_roundsTo`, `log_roundsTo`, `logp1_roundsTo`.
* `powr_roundsTo`, `pow_roundsTo_of_pos`, `pow_roundsTo_of_neg`, `compound_roundsTo`,
  `atan2_roundsTo`, `atan2Pi_roundsTo`.

No theorem has a hypothesis on a search or on the distance of the result from a rounding
boundary. The enclosures only make the comparisons cheaper: `contains_of_enclose`,
`contains_enclosePower`, `contains_encloseExp` and `contains_enclosure` show that an enclosure
contains the number it is for, and `ComparisonRounding.within_eq` that asking through it does
not change a comparator. The rules and what they locate are those of
the binary formats (`Function.locates`, `locates_powr`, `locates_pow_of_pos` and their
siblings). The special cases at zeros, infinities and NaNs are definitions and are not
theorems.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded

open FloatLib.Numerics
open DecimalInterchange.ComparisonRounding
open BinaryInterchange.Model.ComparisonRounding (Rule Operand)
open BinaryInterchange.Model.Transcendentals.CorrectlyRounded (Function powrRule powRule
  compoundRule angleRule powerExpr powerEnclosable angleExpr)
open BinaryInterchange.Model.Transcendentals.Directed (expRule expm1Rule logRule expExpr)
open BinaryInterchange.Model.Transcendentals

/-- An enclosure on one grid contains the number that its expression denotes. -/
theorem contains_of_encloseAt {expression : Interval.Expr} {target : ℝ}
    (htarget : expression.eval (fun _ => 0) = target) {slow : Bool} {bits : Nat}
    {interval : RationalInterval} (h : encloseAt expression slow bits = some interval) :
    interval.Contains target := by
  unfold encloseAt at h
  obtain ⟨bounds, hbounds, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [Enclosure.BinaryGrid.contains_toRationalInterval, ← htarget]
  exact Interval.Expr.containsReal_eval? expression (Interval.Backend.binaryGrid_sound _)
    (env := fun _ => none) (by simp) hbounds

/-- An enclosure contains the number that its expression denotes, on whichever grid it was
found. -/
theorem contains_of_enclose {f : Format} {expression : Interval.Expr} {target : ℝ}
    (htarget : expression.eval (fun _ => 0) = target) {slow : Bool}
    {interval : RationalInterval} (h : enclose f expression slow = some interval) :
    interval.Contains target := by
  have hrefine (steps bits : Nat)
      (h : refine f expression slow steps bits = some interval) : interval.Contains target := by
    induction steps generalizing bits with
    | zero => exact contains_of_encloseAt htarget h
    | succ steps ih =>
        unfold refine at h
        split at h
        · next found hfound =>
          split_ifs at h
          · cases Option.some.inj h
            exact contains_of_encloseAt htarget hfound
          · exact ih _ h
        · exact absurd h (by simp)
  exact hrefine _ _ h

/-- A reciprocal enclosure contains the reciprocal of the number that its expression
denotes. -/
theorem contains_of_encloseInverse {f : Format} {expression : Interval.Expr} {value : ℝ}
    (hvalue : expression.eval (fun _ => 0) = value) {slow : Bool}
    {interval : RationalInterval} (h : encloseInverse f expression slow = some interval) :
    interval.Contains value⁻¹ := by
  unfold encloseInverse at h
  obtain ⟨found, hfound, hreciprocal⟩ := Option.bind_eq_some_iff.mp h
  have hcontains := contains_of_enclose hvalue hfound
  split_ifs at hreciprocal with hlow
  cases Option.some.inj hreciprocal
  have hlo : (0 : ℝ) < found.lo := by exact_mod_cast hlow
  have hpos : 0 < value := hlo.trans_le hcontains.1
  constructor
  · push_cast
    rw [one_div]
    exact inv_anti₀ hpos hcontains.2
  · push_cast
    rw [one_div]
    exact inv_anti₀ hlo hcontains.1

/-- A shifted enclosure contains the shifted number. -/
theorem contains_shift {interval : RationalInterval} {value : ℝ}
    (h : interval.Contains value) (offset : ℚ) :
    (shift offset interval).Contains (value + offset) := by
  constructor
  · simpa [shift] using h.1
  · simpa [shift] using h.2

/-- The enclosure of a power with a positive base contains it. -/
theorem contains_enclosePower {f : Format} {p q : ℚ} (hp : 0 < p)
    {interval : RationalInterval} (h : enclosePower f p q = some interval) :
    interval.Contains ((p : ℝ) ^ (q : ℝ)) := by
  have hreal : (0 : ℝ) < p := by exact_mod_cast hp
  unfold enclosePower at h
  split_ifs at h
  obtain ⟨found, hfound, rfl⟩ := Option.map_eq_some_iff.mp h
  have hcontains := contains_of_enclose (CorrectlyRounded.eval_powerExpr hp (q - round q) _)
    hfound
  rw [show (((q - round q : ℚ)) : ℝ) = (q : ℝ) - ((round q : ℤ) : ℝ) by push_cast; rfl]
    at hcontains
  have hscale : (0 : ℝ) < (p : ℝ) ^ (round q : ℤ) := zpow_pos hreal _
  have hsplit : (p : ℝ) ^ (q : ℝ) =
      (p : ℝ) ^ ((q : ℝ) - ((round q : ℤ) : ℝ)) * (p : ℝ) ^ (round q : ℤ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add hreal]
    congr 1
    ring
  rw [hsplit]
  constructor
  · push_cast
    exact mul_le_mul_of_nonneg_right hcontains.1 hscale.le
  · push_cast
    exact mul_le_mul_of_nonneg_right hcontains.2 hscale.le

/-- The enclosure of an exponential contains it. -/
theorem contains_encloseExp {f : Format} {q : ℚ} {interval : RationalInterval}
    (h : encloseExp f q = some interval) : interval.Contains (Real.exp q) := by
  have hmagnitude : (Interval.Expr.binary .mul (.unary .exp (.const ((round |q| : ℤ) : ℚ)))
      (.unary .exp (.const (|q| - (round |q| : ℤ))))).eval (fun _ => 0) =
      Real.exp ((|q| : ℚ) : ℝ) := by
    simp only [Interval.Expr.eval, Interval.UnaryOp.eval, Interval.BinaryOp.eval]
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  unfold encloseExp at h
  split_ifs at h with hnegative
  · have hcontains := contains_of_encloseInverse hmagnitude h
    rwa [abs_of_neg hnegative, Rat.cast_neg, Real.exp_neg, inv_inv] at hcontains
  · have hcontains := contains_of_enclose hmagnitude h
    rwa [abs_of_nonneg (not_lt.mp hnegative)] at hcontains

/--
An enclosure from the exponential contains the function: for a real function `value` that is
`g (exp t)` with `g` the real form of `hyperbolicOf function`, increasing from one on, and that
is odd or even as `odd` says.
-/
private theorem contains_encloseHyperbolic {f : Format} {function : Function} {odd : Bool}
    {q : ℚ} {interval : RationalInterval}
    (h : encloseHyperbolic f function odd q = some interval) (g value : ℝ → ℝ)
    (hcast : ∀ e : ℚ, ((hyperbolicOf function e : ℚ) : ℝ) = g e)
    (hmono : ∀ a b : ℝ, 1 ≤ a → a ≤ b → g a ≤ g b)
    (hvalue : ∀ t : ℝ, value t = g (Real.exp t))
    (hparity : ∀ t : ℝ, value (-t) = if odd = true then -value t else value t) :
    interval.Contains (value q) := by
  unfold encloseHyperbolic at h
  obtain ⟨found, hfound, hrest⟩ := Option.bind_eq_some_iff.mp h
  have hexp := contains_encloseExp hfound
  split_ifs at hrest with hlow hnegative
  · -- An odd function at a negative operand.
    cases Option.some.inj hrest
    have hone : (1 : ℝ) ≤ found.lo := by exact_mod_cast hlow
    have hlower := hmono _ _ hone hexp.1
    have hupper := hmono _ _ (hone.trans hexp.1) hexp.2
    have hq : (q : ℝ) = -((|q| : ℚ) : ℝ) := by
      rw [abs_of_neg hnegative.2]
      push_cast
      ring
    rw [hq, hparity, ite_eq_left hnegative.1, hvalue]
    constructor
    · change ((-hyperbolicOf function found.hi : ℚ) : ℝ) ≤ _
      rw [Rat.cast_neg, hcast]
      linarith
    · change _ ≤ ((-hyperbolicOf function found.lo : ℚ) : ℝ)
      rw [Rat.cast_neg, hcast]
      linarith
  · cases Option.some.inj hrest
    have hone : (1 : ℝ) ≤ found.lo := by exact_mod_cast hlow
    have hlower := hmono _ _ hone hexp.1
    have hupper := hmono _ _ (hone.trans hexp.1) hexp.2
    have hq : value q = value ((|q| : ℚ) : ℝ) := by
      rcases lt_or_ge q 0 with hneg | hnonneg
      · have hodd : ¬odd = true := fun hodd => hnegative ⟨hodd, hneg⟩
        have hcastq : (q : ℝ) = -((|q| : ℚ) : ℝ) := by
          rw [abs_of_neg hneg]
          push_cast
          ring
        rw [hcastq, hparity, ite_eq_right hodd]
      · rw [abs_of_nonneg hnonneg]
    rw [hq, hvalue]
    exact ⟨by rw [hcast]; exact hlower, by rw [hcast]; exact hupper⟩

/-- A datum with an exact value is finite, and that value is the value of its fields. -/
private theorem eq_finite_of_toRat? {x : Datum} {q : ℚ} (hx : x.toRat? = some q) :
    ∃ negative coefficient quantum, x = .finite negative coefficient quantum ∧
      Datum.finiteValue negative coefficient quantum = q := by
  cases x with
  | finite negative coefficient quantum =>
      rw [Datum.toRat?_eq] at hx
      exact ⟨negative, coefficient, quantum, rfl, Option.some.inj hx⟩
  | infinity negative => simp [Datum.toRat?] at hx
  | nan negative signaling payload => simp [Datum.toRat?] at hx

/-- A finite zero has the exact value zero. -/
private theorem finiteValue_of_isZero {negative : Bool} {coefficient : ℕ} {quantum : ℤ}
    (hzero : (Datum.finite negative coefficient quantum).isZero = true) :
    Datum.finiteValue negative coefficient quantum = 0 := by
  have hc : coefficient = 0 := by simpa [Datum.isZero] using hzero
  simp [Datum.finiteValue, hc]

/-- The enclosure of a member of `Function` at a finite operand in its domain contains the
real function. -/
theorem contains_enclosure {f : Format} {function : Function} {negative : Bool} {q : ℚ}
    (hdomain : function.Domain q) {interval : RationalInterval}
    (h : enclosure f function (.finite negative q) () = some interval) :
    interval.Contains (function.real q) := by
  have hpower (base : ℚ) (hbase : 0 < base) {found : RationalInterval}
      (hfound : enclosePower f base q = some found) :
      found.Contains ((base : ℝ) ^ (q : ℝ)) := contains_enclosePower hbase hfound
  have hminusOne (base : ℚ) (hbase : 0 < base)
      (hfound : (enclosePower f base q).map (shift (-1)) = some interval) :
      interval.Contains ((base : ℝ) ^ (q : ℝ) - 1) := by
    obtain ⟨found, hpowerFound, rfl⟩ := Option.map_eq_some_iff.mp hfound
    have hshift := contains_shift (hpower base hbase hpowerFound) (-1)
    simpa [sub_eq_add_neg] using hshift
  have hinv (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) : 1 / b ≤ 1 / a :=
    one_div_le_one_div_of_le (by linarith) hab
  have hsinh : ∀ {found : RationalInterval},
      encloseHyperbolic f .sinh true q = some found → found.Contains (Real.sinh q) := by
    intro found hfound
    refine contains_encloseHyperbolic hfound (fun e => (e - 1 / e) / 2) Real.sinh
      (fun e => by simp only [hyperbolicOf]; push_cast; ring) (fun a b ha hab => ?_)
      (fun t => ?_) (fun t => ?_)
    · have := hinv a b ha hab
      linarith
    · rw [Real.sinh_eq, Real.exp_neg, one_div]
    · simp [Real.sinh_neg]
  have hcosh : ∀ {found : RationalInterval},
      encloseHyperbolic f .cosh false q = some found → found.Contains (Real.cosh q) := by
    intro found hfound
    refine contains_encloseHyperbolic hfound (fun e => (e + 1 / e) / 2) Real.cosh
      (fun e => by simp only [hyperbolicOf]; push_cast; ring) (fun a b ha hab => ?_)
      (fun t => ?_) (fun t => ?_)
    · have : 0 < a := by linarith
      have : 0 < b := by linarith
      have hdiff : 1 / a - 1 / b = (b - a) / (a * b) := by
        field_simp
      have hbound : (b - a) / (a * b) ≤ b - a :=
        div_le_self (by linarith) (by nlinarith)
      linarith
    · rw [Real.cosh_eq, Real.exp_neg, one_div]
    · simp [Real.cosh_neg]
  have htanh : ∀ {found : RationalInterval},
      encloseHyperbolic f .tanh true q = some found → found.Contains (Real.tanh q) := by
    intro found hfound
    refine contains_encloseHyperbolic hfound (fun e => (e ^ 2 - 1) / (e ^ 2 + 1)) Real.tanh
      (fun e => by simp only [hyperbolicOf]; push_cast; ring) (fun a b ha hab => ?_)
      (fun t => ?_) (fun t => ?_)
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · have := Real.exp_pos t
      rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
      field_simp
    · simp [Real.tanh_neg]
  simp only [enclosure] at h
  split_ifs at h
  · split at h
    · simpa [Function.real] using hpower 2 (by norm_num) h
    · simpa [Function.real] using hpower 10 (by norm_num) h
    · exact contains_of_enclose (Function.exp2m1.eval_expr trivial _) h
    · exact contains_of_enclose (Function.exp10m1.eval_expr trivial _) h
    · exact contains_of_enclose (Function.sinh.eval_expr trivial _) h
    · exact contains_of_enclose (Function.cosh.eval_expr trivial _) h
    · exact contains_of_enclose (Function.tanh.eval_expr trivial _) h
    · exact contains_of_enclose (function.eval_expr hdomain _) h
  · split at h
    · simpa [Function.real] using hpower 2 (by norm_num) h
    · simpa [Function.real] using hpower 10 (by norm_num) h
    · simpa [Function.real] using hminusOne 2 (by norm_num) h
    · simpa [Function.real] using hminusOne 10 (by norm_num) h
    · exact hsinh h
    · exact hcosh h
    · exact htanh h
    · exact contains_of_enclose (function.eval_expr hdomain _) h

/-- The rule of the exact value one is rounded as the real number one. -/
private theorem deliver_one_roundsTo (f : Format) (mode : RoundingMode) :
    RoundsTo f mode 1 false (deliver f mode (fun _ => none) (Rule.rational 1)) := by
  have h := deliver_roundsTo f mode
    (BinaryInterchange.Model.ComparisonRounding.Rule.locates_rational 1) (by norm_num)
    (enclosure := fun _ => none) (fun _ h => absurd h (by simp))
  simp only [Rat.cast_one] at h
  rwa [decide_eq_false (by norm_num : ¬(1 : ℝ) < 0)] at h

/--
**The decimal recommended functions of one argument are correctly rounded in every
direction.** For every decimal format, a member of `Function`, a finite operand whose exact
value `q` is in the function's domain with a real value that is not zero, and each rounding
direction `mode`, the outcome meets the contract `RoundsTo` for the real function at `q`.
-/
theorem apply_roundsTo (f : Format) (function : Function) (mode : RoundingMode) {x : Datum}
    {q : ℚ} (hx : x.toRat? = some q) (hdomain : function.Domain q)
    (hne : function.real q ≠ 0) :
    RoundsTo f mode (function.real q) (decide (function.real q < 0))
      (apply f function mode x) := by
  obtain ⟨negative, coefficient, quantum, rfl, rfl⟩ := eq_finite_of_toRat? hx
  have hspecial : ¬((Datum.finite negative coefficient quantum).isZero = true ∧
      function.vanishesAtZero = true) := by
    rintro ⟨hzero, hvanish⟩
    apply hne
    rw [finiteValue_of_isZero hzero, Rat.cast_zero]
    exact Function.real_zero_of_vanishesAtZero hvanish
  unfold apply
  rw [ite_eq_right hspecial, unary_finite]
  refine deliver_roundsTo f mode (function.locates _ _ hdomain) hne fun interval h => ?_
  exact contains_enclosure hdomain h

/-- A zero operand of a function that is zero at zero is returned with its sign and with its
quantum exponent brought into the range of the format, without a flag. -/
theorem apply_zero (f : Format) (function : Function) (mode : RoundingMode) (negative : Bool)
    (quantum : ℤ) (hvanish : function.vanishesAtZero = true) :
    apply f function mode (.finite negative 0 quantum) =
      { value := .finite negative 0 (max f.minQuantum (min quantum f.maxQuantum)) } := by
  simp [apply, hvanish, Datum.isZero, keepZero, projectMagnitude_zero]

/-! ## `exp`, `expm1`, `log` and `logp1` -/

/-- **Decimal `exp` is correctly rounded in every direction.** -/
theorem exp_roundsTo (f : Format) (mode : RoundingMode) {x : Datum} {q : ℚ}
    (hx : x.toRat? = some q) : RoundsTo f mode (Real.exp q) false (exp f mode x) := by
  obtain ⟨negative, coefficient, quantum, rfl, rfl⟩ := eq_finite_of_toRat? hx
  have hpos := Real.exp_pos ((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ)
  unfold exp
  rw [unary_finite]
  have h := deliver_roundsTo f mode (Directed.locates_exp (levels f) negative _) hpos.ne'
    (enclosure := expEnclosure f false (.finite negative _)) fun interval h => by
      simp only [expEnclosure, ↓reduceIte] at h
      split_ifs at h
      exact contains_encloseExp h
  rwa [decide_eq_false (not_lt.mpr hpos.le)] at h

/-- **Decimal `expm1` is correctly rounded in every direction**, at a nonzero operand. -/
theorem expm1_roundsTo (f : Format) (mode : RoundingMode) {x : Datum} {q : ℚ}
    (hx : x.toRat? = some q) (hne : q ≠ 0) :
    RoundsTo f mode (Real.exp q - 1) (decide (Real.exp q - 1 < 0)) (expm1 f mode x) := by
  obtain ⟨negative, coefficient, quantum, rfl, rfl⟩ := eq_finite_of_toRat? hx
  have hvalue : Real.exp ((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ) - 1 ≠ 0 := by
    intro h
    exact hne (by exact_mod_cast (Real.exp_eq_one_iff _).mp (sub_eq_zero.mp h))
  have hzero : ¬(Datum.finite negative coefficient quantum).isZero = true :=
    fun h => hne (finiteValue_of_isZero h)
  unfold expm1
  rw [ite_eq_right hzero, unary_finite]
  refine deliver_roundsTo f mode (Directed.locates_expm1 (levels f) negative _) hvalue
    fun interval h => ?_
  simp only [expEnclosure, Bool.true_eq_false, ↓reduceIte] at h
  split_ifs at h
  · exact contains_of_enclose (Directed.eval_expExpr true _ _) h
  · obtain ⟨found, hfound, rfl⟩ := Option.map_eq_some_iff.mp h
    have hshift := contains_shift (contains_encloseExp hfound) (-1)
    simpa [sub_eq_add_neg] using hshift

/-- The enclosure of a logarithm contains it. -/
private theorem contains_logEnclosure {f : Format} {offset : ℚ} {negative : Bool} {q : ℚ}
    {interval : RationalInterval}
    (h : logEnclosure f offset (.finite negative q) () = some interval) :
    interval.Contains (Real.log ((q : ℝ) + (offset : ℝ))) := by
  simp only [logEnclosure] at h
  split_ifs at h
  exact contains_of_enclose (by simp [Interval.Expr.eval, Interval.UnaryOp.eval]) h

/-- **Decimal `log` is correctly rounded in every direction**, at a positive operand other
than 1. -/
theorem log_roundsTo (f : Format) (mode : RoundingMode) {x : Datum} {q : ℚ}
    (hx : x.toRat? = some q) (hpos : 0 < q) (hne : q ≠ 1) :
    RoundsTo f mode (Real.log q) (decide (Real.log q < 0)) (log f mode x) := by
  obtain ⟨negative, coefficient, quantum, rfl, rfl⟩ := eq_finite_of_toRat? hx
  have hreal : (0 : ℝ) < (Datum.finiteValue negative coefficient quantum : ℚ) := by
    exact_mod_cast hpos
  have hvalue : Real.log ((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ) ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h0 | h1 | h1
    · exact hreal.ne' h0
    · exact hne (by exact_mod_cast h1)
    · linarith
  unfold log
  rw [unary_finite]
  have h := deliver_roundsTo f mode
    (Directed.locates_log (offset := 0) (.inl rfl) (levels f) negative (by simpa using hpos))
    (by simpa using hvalue) (enclosure := logEnclosure f 0 (.finite negative _))
    fun interval h => contains_logEnclosure h
  simp only [Rat.cast_zero, add_zero] at h
  exact h

/-- **Decimal `logp1` is correctly rounded in every direction**, at a nonzero operand
above -1. -/
theorem logp1_roundsTo (f : Format) (mode : RoundingMode) {x : Datum} {q : ℚ}
    (hx : x.toRat? = some q) (hdomain : -1 < q) (hne : q ≠ 0) :
    RoundsTo f mode (Real.log ((q : ℝ) + 1)) (decide (Real.log ((q : ℝ) + 1) < 0))
      (logp1 f mode x) := by
  obtain ⟨negative, coefficient, quantum, rfl, rfl⟩ := eq_finite_of_toRat? hx
  have hreal : (0 : ℝ) < ((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ) + 1 := by
    have : (-1 : ℝ) < (Datum.finiteValue negative coefficient quantum : ℚ) := by
      exact_mod_cast hdomain
    linarith
  have hvalue :
      Real.log (((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ) + 1) ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h0 | h1 | h1
    · exact hreal.ne' h0
    · exact hne (by exact_mod_cast (by linarith :
        ((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ) = 0))
    · linarith
  have hzero : ¬(Datum.finite negative coefficient quantum).isZero = true :=
    fun h => hne (finiteValue_of_isZero h)
  unfold logp1
  rw [ite_eq_right hzero, unary_finite]
  have h := deliver_roundsTo f mode
    (Directed.locates_log (offset := 1) (.inr rfl) (levels f) negative (by linarith))
    (by simpa using hvalue) (enclosure := logEnclosure f 1 (.finite negative _))
    fun interval h => contains_logEnclosure h
  simp only [Rat.cast_one] at h
  exact h

/-! ## Functions of two arguments -/

/-- The enclosure of a power at finite operands with a positive base contains it. -/
private theorem contains_powerEnclosure {f : Format} {negative negative' : Bool} {p q : ℚ}
    (hp : 0 < p) {interval : RationalInterval}
    (h : powerEnclosure f (.finite negative p) (.finite negative' q) () = some interval) :
    interval.Contains ((p : ℝ) ^ (q : ℝ)) := by
  simp only [powerEnclosure, hp, ↓reduceIte] at h
  exact contains_enclosePower hp h

/-- **Decimal `powr` is correctly rounded in every direction**, at a finite positive base and
a finite exponent. -/
theorem powr_roundsTo (f : Format) (mode : RoundingMode) {x y : Datum} {p q : ℚ}
    (hx : x.toRat? = some p) (hy : y.toRat? = some q) (hp : 0 < p) :
    RoundsTo f mode ((p : ℝ) ^ (q : ℝ)) false (powr f mode x y) := by
  obtain ⟨negative, coefficient, quantum, rfl, rfl⟩ := eq_finite_of_toRat? hx
  obtain ⟨negative', coefficient', quantum', rfl, rfl⟩ := eq_finite_of_toRat? hy
  have hpos : (0 : ℝ) < ((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ) ^
      ((Datum.finiteValue negative' coefficient' quantum' : ℚ) : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp) _
  unfold powr
  rw [binary_finite]
  have h := deliver_roundsTo f mode (CorrectlyRounded.locates_powr negative negative' hp)
    hpos.ne' (enclosure := powerEnclosure f (.finite negative _) (.finite negative' _))
    fun interval h => contains_powerEnclosure hp h
  rwa [decide_eq_false (not_lt.mpr hpos.le)] at h

/-- **Decimal `pow` of a positive base is correctly rounded in every direction**, at a finite
positive base and a finite exponent. -/
theorem pow_roundsTo_of_pos (f : Format) (mode : RoundingMode) {x y : Datum} {p q : ℚ}
    (hx : x.toRat? = some p) (hy : y.toRat? = some q) (hp : 0 < p) :
    RoundsTo f mode ((p : ℝ) ^ (q : ℝ)) false (pow f mode x y) := by
  unfold pow
  split_ifs with hspecial
  · have hone : (p : ℝ) ^ (q : ℝ) = 1 := by
      rcases hspecial with ⟨hzero, -⟩ | ⟨hone, -⟩
      · obtain ⟨negative', coefficient', quantum', rfl, rfl⟩ := eq_finite_of_toRat? hy
        simp [finiteValue_of_isZero hzero]
      · simp [Option.some.inj (hx.symm.trans hone)]
    rw [hone]
    exact deliver_one_roundsTo f mode
  · obtain ⟨negative, coefficient, quantum, rfl, rfl⟩ := eq_finite_of_toRat? hx
    obtain ⟨negative', coefficient', quantum', rfl, rfl⟩ := eq_finite_of_toRat? hy
    have hpos : (0 : ℝ) < ((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ) ^
        ((Datum.finiteValue negative' coefficient' quantum' : ℚ) : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hp) _
    rw [binary_finite]
    have h := deliver_roundsTo f mode
      (CorrectlyRounded.locates_pow_of_pos negative negative' hp _) hpos.ne'
      (enclosure := powerEnclosure f (.finite negative _) (.finite negative' _))
      fun interval h => contains_powerEnclosure hp h
    rwa [decide_eq_false (not_lt.mpr hpos.le)] at h

/-- **Decimal `pow` of a negative base and an integral exponent is correctly rounded in every
direction.** -/
theorem pow_roundsTo_of_neg (f : Format) (mode : RoundingMode) {x y : Datum} {p : ℚ} {n : ℤ}
    (hx : x.toRat? = some p) (hy : y.toRat? = some (n : ℚ)) (hp : p < 0) :
    RoundsTo f mode ((p : ℝ) ^ n) (decide ((p : ℝ) ^ n < 0)) (pow f mode x y) := by
  have hbase : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne
  have hne : (p : ℝ) ^ n ≠ 0 := zpow_ne_zero n hbase
  unfold pow
  split_ifs with hspecial
  · have hone : (p : ℝ) ^ n = 1 := by
      rcases hspecial with ⟨hzero, -⟩ | ⟨hone, -⟩
      · obtain ⟨negative', coefficient', quantum', rfl, hvalue⟩ := eq_finite_of_toRat? hy
        have hn : n = 0 := by
          rw [finiteValue_of_isZero hzero] at hvalue
          exact_mod_cast hvalue.symm
        simp [hn]
      · have : p = 1 := Option.some.inj (hx.symm.trans hone)
        linarith
    rw [hone, decide_eq_false (by norm_num)]
    exact deliver_one_roundsTo f mode
  · obtain ⟨negative, coefficient, quantum, rfl, hbaseValue⟩ := eq_finite_of_toRat? hx
    obtain ⟨negative', coefficient', quantum', rfl, hvalue⟩ := eq_finite_of_toRat? hy
    rw [binary_finite, hbaseValue, hvalue]
    refine deliver_roundsTo f mode (CorrectlyRounded.locates_pow_of_neg negative negative' hp n)
      hne fun interval h => ?_
    simp only [powerEnclosure, not_lt.mpr hp.le, ↓reduceIte, Rat.den_intCast,
      Rat.num_intCast] at h
    obtain ⟨found, hfound, rfl⟩ := Option.map_eq_some_iff.mp h
    have hcontains := contains_enclosePower (p := -p) (q := n) (by linarith) hfound
    have hpower : (((-p : ℚ)) : ℝ) ^ (((n : ℚ)) : ℝ) = (-(p : ℝ)) ^ n := by
      push_cast
      exact Real.rpow_intCast _ n
    rw [hpower] at hcontains
    by_cases hodd : n % 2 = 1
    · simp only [hodd, ↓reduceIte]
      rw [show (p : ℝ) ^ n = -((-(p : ℝ)) ^ n) by
        rw [(Int.odd_iff.mpr hodd).neg_zpow, _root_.neg_neg]]
      exact ⟨by push_cast; linarith [hcontains.2], by push_cast; linarith [hcontains.1]⟩
    · simp only [hodd, ↓reduceIte]
      rw [show (p : ℝ) ^ n = (-(p : ℝ)) ^ n by
        rw [(Int.not_odd_iff_even.mp (mt Int.odd_iff.mp hodd)).neg_zpow]]
      exact hcontains

/-- **Decimal `compound` is correctly rounded in every direction**, at a finite operand
above -1. -/
theorem compound_roundsTo (f : Format) (mode : RoundingMode) {x : Datum} {q : ℚ}
    (hx : x.toRat? = some q) (hq : -1 < q) (n : ℤ) :
    RoundsTo f mode ((1 + (q : ℝ)) ^ (n : ℝ)) false (compound f mode x n) := by
  obtain ⟨negative, coefficient, quantum, rfl, rfl⟩ := eq_finite_of_toRat? hx
  have hbase : (0 : ℝ) < 1 + ((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ) := by
    have : (-1 : ℝ) < (Datum.finiteValue negative coefficient quantum : ℚ) := by
      exact_mod_cast hq
    linarith
  have hpos := Real.rpow_pos_of_pos hbase (n : ℝ)
  unfold compound
  rw [ite_eq_right (by simp [Datum.isNaN]), unary_finite]
  have h := deliver_roundsTo f mode (CorrectlyRounded.locates_compound negative hq n) hpos.ne'
    (enclosure := compoundEnclosure f n (.finite negative _)) fun interval h => by
      have hcontains := contains_enclosePower (p := 1 + Datum.finiteValue negative coefficient
        quantum) (q := n) (by linarith) h
      push_cast at hcontains
      exact hcontains
  rwa [decide_eq_false (not_lt.mpr hpos.le)] at h

/-- The enclosure of an angle contains it. -/
private theorem contains_angleEnclosure {f : Format} {halfTurns negative negative' : Bool}
    {qy qx : ℚ} {interval : RationalInterval}
    (h : angleEnclosure f halfTurns (.finite negative qy) (.finite negative' qx) () =
      some interval) :
    interval.Contains (if halfTurns then Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi
      else Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩) := by
  simp only [angleEnclosure] at h
  split_ifs at h
  exact contains_of_enclose (CorrectlyRounded.eval_angleExpr halfTurns qx qy _) h

/-- **Decimal `atan2` is correctly rounded in every direction**, at finite operands with a
nonzero `y`: the angle of `x + i y`. -/
theorem atan2_roundsTo (f : Format) (mode : RoundingMode) {y x : Datum} {qy qx : ℚ}
    (hy : y.toRat? = some qy) (hx : x.toRat? = some qx) (hne : qy ≠ 0) :
    RoundsTo f mode (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩)
      (decide (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ < 0)) (atan2 f mode y x) := by
  obtain ⟨negative, coefficient, quantum, rfl, rfl⟩ := eq_finite_of_toRat? hy
  obtain ⟨negative', coefficient', quantum', rfl, rfl⟩ := eq_finite_of_toRat? hx
  have harg : Complex.arg ⟨((Datum.finiteValue negative' coefficient' quantum' : ℚ) : ℝ),
      ((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ)⟩ ≠ 0 := by
    intro h
    have him : ((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ) = 0 :=
      (Complex.arg_eq_zero_iff.mp h).2
    exact hne (by exact_mod_cast him)
  unfold atan2
  rw [binary_finite]
  exact deliver_roundsTo f mode (CorrectlyRounded.locates_atan2 (levels f) negative negative' hne)
    harg fun interval h => contains_angleEnclosure (halfTurns := false) h

/-- **Decimal `atan2Pi` is correctly rounded in every direction**, at finite operands with a
nonzero `y`: the angle of `x + i y` divided by π. -/
theorem atan2Pi_roundsTo (f : Format) (mode : RoundingMode) {y x : Datum} {qy qx : ℚ}
    (hy : y.toRat? = some qy) (hx : x.toRat? = some qx) (hne : qy ≠ 0) :
    RoundsTo f mode (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi)
      (decide (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi < 0)) (atan2Pi f mode y x) := by
  obtain ⟨negative, coefficient, quantum, rfl, rfl⟩ := eq_finite_of_toRat? hy
  obtain ⟨negative', coefficient', quantum', rfl, rfl⟩ := eq_finite_of_toRat? hx
  have harg : Complex.arg ⟨((Datum.finiteValue negative' coefficient' quantum' : ℚ) : ℝ),
      ((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ)⟩ ≠ 0 := by
    intro h
    have him : ((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ) = 0 :=
      (Complex.arg_eq_zero_iff.mp h).2
    exact hne (by exact_mod_cast him)
  unfold atan2Pi
  rw [binary_finite]
  exact deliver_roundsTo f mode
    (CorrectlyRounded.locates_atan2Pi (levels f) negative negative' hne)
    (div_ne_zero harg Real.pi_ne_zero) fun interval h =>
      contains_angleEnclosure (halfTurns := true) h

end FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded
