/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Recommended.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Comparison.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Enclosure.Proof
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof
public import FloatLib.Floats.Formats.Posit.Logarithm.Proof
public import FloatLib.Numerics.Exact.RationalPower.Proof
public import FloatLib.Numerics.Exact.Hyperbolic.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Pi.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Proof
public import FloatLib.Numerics.Order.Comparison

/-!
# The recommended functions are correctly rounded

`Function.real` is the real function that each member of `Function` computes, and
`Function.Domain` the finite arguments at which it is a real number (the domain of the
function without its poles). `Function.toReal_apply` is one theorem for the 26 functions of
one argument: for a conventional IEEE descriptor and a finite operand in the domain, a finite
result to nearest-even is `roundAt fmt` of the real function at the operand's exact value. Each
named function (`exp2`, `sin`, `atanh`, ...) is `Function.apply` at its member by definition, so
the theorem applies to it as it stands. `Function.inexact_apply_iff` gives the `inexact` flag
its meaning, in every rounding direction. `Function.apply_encloses` is the statement for the
directions toward negative and toward positive infinity: the first result is at most the real
function and the second at least, in the extended reals.

`toReal_powr`, `toReal_compound`, `toReal_atan2` and `toReal_atan2Pi` are the nearest-even
statement for the functions of two arguments, at finite operands: a positive base for `powr`,
an operand above -1 for `compound`, and a nonzero `y` for the angles, which are `Complex.arg` of
`x + i y`. `powr_encloses`, `compound_encloses`, `atan2_encloses` and `atan2Pi_encloses` are
their enclosures.

To nearest-even every function takes its value from an enclosure when one settles it.
`Function.eval_expr` shows that the expression that is enclosed
denotes the function, `settle_sound` that an enclosure which settles gives `roundAt fmt` of the
number its expression denotes, and `Function.hint_sound`, `angleHint_sound`, `powrHint_sound`
and `compoundHint_sound` put the two together, so the theorems hold whichever path delivers the
value.

The nearest-even equation with `roundAt` requires finite operands in the stated domain and a
finite result. It has no hypothesis on the number of search steps.
In the two directed directions the enclosure is proved, and that the results are the nearest
values on their side is not; the directions toward zero, away from zero and to nearest with ties
away have no theorem. The special cases at zeros, infinities and NaNs are definitions, read off
ISO/IEC 9899:2024 F.10.1 to F.10.4, and are not theorems. `underflow` has no theorem.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded

open FloatLib.Numerics
open FloatLib.Numerics.TrigonometricComparison FloatLib.Numerics.HyperbolicComparison
open ComparisonRounding

variable {fmt : FloatFormat}

/-- The expression of π denotes π. -/
theorem eval_piExpr (env : Nat → ℝ) : piExpr.eval env = Real.pi := by
  simp [piExpr, Interval.Expr.eval, Interval.UnaryOp.eval, Interval.BinaryOp.eval,
    Real.arctan_one]
  ring

/-- The expression of a power with a positive base denotes the power. -/
theorem eval_powerExpr {base : ℚ} (hbase : 0 < base) (q : ℚ) (env : Nat → ℝ) :
    (powerExpr base q).eval env = (base : ℝ) ^ (q : ℝ) := by
  simp only [powerExpr, Interval.Expr.eval, Interval.UnaryOp.eval, Interval.BinaryOp.eval]
  rw [Real.rpow_def_of_pos (by exact_mod_cast hbase), mul_comm]

/-- The expression of a logarithm denotes the logarithm to that base. -/
theorem eval_logarithmExpr (base q : ℚ) (env : Nat → ℝ) :
    (logarithmExpr base q).eval env = Real.logb base q := by
  simp [logarithmExpr, Interval.Expr.eval, Interval.UnaryOp.eval, Interval.BinaryOp.eval,
    Real.logb]

/--
An enclosure that settles gives the correctly rounded value: for an expression that denotes
`target`, the value of `settle` is finite, denotes `roundAt fmt target`, and the ordering it
states is the ordering of that value and `target`.
-/
theorem settle_sound {expression : Interval.Expr} {target : ℝ}
    (htarget : expression.eval (fun _ => 0) = target) {config : Interval.Backend.Config}
    {found : Hint fmt} (h : settle fmt expression config = some found) :
    isFinite found.value = true ∧ toReal found.value = roundAt fmt target ∧
      ∀ ordering, found.ternary = some ordering → ordering = cmp (toReal found.value) target := by
  unfold settle at h
  split at h
  · exact absurd h (by simp)
  · next bounds hbounds =>
    have hcontains : (Enclosure.BinaryGrid.toRationalInterval config.precision bounds).Contains
        target := by
      rw [Enclosure.BinaryGrid.contains_toRationalInterval, ← htarget]
      exact Interval.Expr.containsReal_eval? expression
        (Interval.Backend.binaryGrid_sound config) (env := fun _ => none) (by simp) hbounds
    dsimp only at h
    split at h
    · exact absurd h (by simp)
    · next value hvalue =>
      cases Option.some.inj h
      have hfinite := Enclosure.isFinite_of_round?_eq_some hvalue
      refine ⟨hfinite, Enclosure.toReal_eq_roundAt_of_round?_eq_some hcontains hvalue, ?_⟩
      intro ordering hordering
      obtain ⟨delivered, hdelivered, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hfinite
      rw [hdelivered] at hordering
      dsimp only at hordering ⊢
      rw [hreal]
      split_ifs at hordering with hlow hhigh
      · cases Option.some.inj hordering
        exact ((cmp_eq_lt_iff _ _).mpr
          (lt_of_lt_of_le (by exact_mod_cast hlow) hcontains.1)).symm
      · cases Option.some.inj hordering
        exact ((cmp_eq_gt_iff _ _).mpr
          (lt_of_le_of_lt hcontains.2 (by exact_mod_cast hhigh))).symm

/-- The enclosure search for an expression that denotes `target` is right about `target`. -/
theorem nearest?_sound {expression : Interval.Expr} {target : ℝ}
    (htarget : expression.eval (fun _ => 0) = target) (slow : Bool) :
    Hint.Sound (fun _ => nearest? fmt expression slow) target := by
  intro found h
  obtain ⟨config, -, hconfig⟩ := List.exists_of_findSome?_eq_some h
  exact settle_sound htarget hconfig

namespace Function

/-- The real function that a member of `Function` rounds. -/
noncomputable def real : Function → ℝ → ℝ
  | .exp2, x => (2 : ℝ) ^ x
  | .exp2m1, x => (2 : ℝ) ^ x - 1
  | .exp10, x => (10 : ℝ) ^ x
  | .exp10m1, x => (10 : ℝ) ^ x - 1
  | .log2, x => Real.logb 2 x
  | .log10, x => Real.logb 10 x
  | .log2p1, x => Real.logb 2 (x + 1)
  | .log10p1, x => Real.logb 10 (x + 1)
  | .sin, x => Real.sin x
  | .cos, x => Real.cos x
  | .tan, x => Real.tan x
  | .sinPi, x => Real.sin (x * Real.pi)
  | .cosPi, x => Real.cos (x * Real.pi)
  | .tanPi, x => Real.tan (x * Real.pi)
  | .asin, x => Real.arcsin x
  | .acos, x => Real.arccos x
  | .atan, x => Real.arctan x
  | .asinPi, x => Real.arcsin x / Real.pi
  | .acosPi, x => Real.arccos x / Real.pi
  | .atanPi, x => Real.arctan x / Real.pi
  | .sinh, x => Real.sinh x
  | .cosh, x => Real.cosh x
  | .tanh, x => Real.tanh x
  | .asinh, x => Real.arsinh x
  | .acosh, x => Real.arcosh x
  | .atanh, x => Real.artanh x

/-- A function that `vanishesAtZero` says so of is zero at zero. -/
theorem real_zero_of_vanishesAtZero {function : Function} (h : function.vanishesAtZero = true) :
    function.real 0 = 0 := by
  cases function <;> simp_all [vanishesAtZero, real]

/-- At a finite argument `base ^ x` is located by the rational-power comparator. -/
theorem locates_exponential {base : ℚ} (hbase : 0 ≤ base) (negative : Bool) (q : ℚ) :
    (exponential base (.finite negative q)).Locates ((base : ℝ) ^ (q : ℝ)) :=
  fun candidate => RationalPower.compare_eq_real base q candidate hbase

/-- At a finite argument `base ^ x - 1` is located by shifting the candidates by one. -/
theorem locates_exponentialMinusOne {base : ℚ} (hbase : 0 < base) (negative : Bool) (q : ℚ) :
    (exponentialMinusOne base (.finite negative q)).Locates ((base : ℝ) ^ (q : ℝ) - 1) := by
  refine Rule.locates_oddAt ?_ ?_
  · rintro rfl
    simp
  · intro _ candidate
    rw [RationalPower.compare_eq_real base q _ hbase.le, cmp_sub_eq_cmp_add]
    push_cast
    rfl

/-- In its domain the logarithm of `x + offset`, for the offsets zero and one, is located. -/
theorem locates_logarithm {base offset : ℚ} (hbase : 1 < base)
    (hoffset : offset = 0 ∨ offset = 1) (negative : Bool) {q : ℚ} (hq : 0 < q + offset) :
    (logarithm base offset (.finite negative q)).Locates
      (Real.logb (base : ℝ) ((q : ℝ) + (offset : ℝ))) := by
  change (if offset ≠ 0 ∧ q = 0 then Rule.zero negative
    else if q + offset = 0 then Rule.pole true
    else if q + offset < 0 then Rule.invalid
    else Rule.real (Posit.Model.Logarithm.compareTarget base (q + offset))).Locates _
  by_cases h : offset ≠ 0 ∧ q = 0
  · simp only [h]
    obtain ⟨hne, rfl⟩ := h
    rcases hoffset with rfl | rfl
    · exact absurd rfl hne
    · change Real.logb _ _ = 0
      simp
  · simp only [h, hq.ne', not_lt.mpr hq.le, ↓reduceIte]
    intro candidate
    simpa using Posit.Model.Logarithm.compareTarget_eq_real base (q + offset) candidate hbase hq

/-- An integer times π has sine zero, for a rational with denominator one. -/
private theorem sin_mul_pi_of_den_eq_one {q : ℚ} (h : q.den = 1) :
    Real.sin ((q : ℝ) * Real.pi) = 0 := by
  have hq : (q : ℝ) = ((q.num : ℤ) : ℝ) := by
    exact_mod_cast ((Rat.den_eq_one_iff q).mp h).symm
  rw [hq]
  exact Real.sin_int_mul_pi q.num

/-- An integer times π has tangent zero, for a rational with denominator one. -/
private theorem tan_mul_pi_of_den_eq_one {q : ℚ} (h : q.den = 1) :
    Real.tan ((q : ℝ) * Real.pi) = 0 := by
  have hq : (q : ℝ) = ((q.num : ℤ) : ℝ) := by
    exact_mod_cast ((Rat.den_eq_one_iff q).mp h).symm
  rw [hq]
  exact Real.tan_int_mul_pi q.num

/--
In its domain every member of `Function` is located by its rule at a finite argument: the
rule is an exact zero where the function is zero, and otherwise a comparator of its value.
-/
theorem locates (function : Function) (levels : Nat) (negative : Bool) {q : ℚ}
    (hdomain : function.Domain q) :
    (function.rule levels (.finite negative q)).Locates (function.real q) := by
  cases function with
  | exp2 =>
      change (exponential 2 (.finite negative q)).Locates _
      simpa [real] using locates_exponential (base := 2) (by norm_num) negative q
  | exp10 =>
      change (exponential 10 (.finite negative q)).Locates _
      simpa [real] using locates_exponential (base := 10) (by norm_num) negative q
  | exp2m1 =>
      change (exponentialMinusOne 2 (.finite negative q)).Locates _
      simpa [real] using locates_exponentialMinusOne (base := 2) (by norm_num) negative q
  | exp10m1 =>
      change (exponentialMinusOne 10 (.finite negative q)).Locates _
      simpa [real] using locates_exponentialMinusOne (base := 10) (by norm_num) negative q
  | log2 =>
      change (logarithm 2 0 (.finite negative q)).Locates _
      simpa [real] using locates_logarithm (base := 2) (offset := 0) (by norm_num) (.inl rfl)
        negative (q := q) (by simpa [Domain] using hdomain)
  | log10 =>
      change (logarithm 10 0 (.finite negative q)).Locates _
      simpa [real] using locates_logarithm (base := 10) (offset := 0) (by norm_num) (.inl rfl)
        negative (q := q) (by simpa [Domain] using hdomain)
  | log2p1 =>
      have hq : -1 < q := hdomain
      change (logarithm 2 1 (.finite negative q)).Locates _
      simpa [real] using locates_logarithm (base := 2) (offset := 1) (by norm_num) (.inr rfl)
        negative (q := q) (by linarith)
  | log10p1 =>
      have hq : -1 < q := hdomain
      change (logarithm 10 1 (.finite negative q)).Locates _
      simpa [real] using locates_logarithm (base := 10) (offset := 1) (by norm_num) (.inr rfl)
        negative (q := q) (by linarith)
  | sin =>
      exact Rule.locates_oddAt (by rintro rfl; simp [real])
        fun _ candidate => prepareSin_eq_real q levels candidate
  | cos => exact fun candidate => prepareCos_eq_real q levels candidate
  | tan =>
      exact Rule.locates_oddAt (by rintro rfl; simp [real])
        fun _ candidate => prepareTan_eq_real q levels candidate
  | sinPi =>
      change (if q.den = 1 then Rule.zero negative
        else Rule.real (prepareSinPi q levels).compare).Locates _
      by_cases h : q.den = 1
      · simp only [h, ↓reduceIte]
        exact sin_mul_pi_of_den_eq_one h
      · simp only [h, ↓reduceIte]
        exact fun candidate => prepareSinPi_eq_real q levels candidate
  | cosPi =>
      have hden : q.den ≠ 2 := hdomain
      change (if q.den = 2 then Rule.zero false
        else Rule.real (prepareCosPi q levels).compare).Locates _
      simp only [hden, ↓reduceIte]
      exact fun candidate => prepareCosPi_eq_real q levels candidate
  | tanPi =>
      have hden : q.den ≠ 2 := hdomain
      change (if q = 0 then Rule.zero negative
        else if q.den = 1 then Rule.zero (tanPiZeroSign q.num)
        else if q.den = 2 then Rule.pole (decide (q.num % 4 = 3))
        else Rule.real (prepareTanPi q levels).compare).Locates _
      by_cases h0 : q = 0
      · subst h0
        simp [real, Rule.Locates]
      · by_cases h1 : q.den = 1
        · simp only [h0, h1, ↓reduceIte]
          exact tan_mul_pi_of_den_eq_one h1
        · simp only [h0, h1, hden, ↓reduceIte]
          exact fun candidate => prepareTanPi_eq_real q levels candidate
  | asin =>
      have h : -1 ≤ q ∧ q ≤ 1 := hdomain
      change (if -1 ≤ q ∧ q ≤ 1 then _ else Rule.invalid).Locates _
      simp only [h]
      exact Rule.locates_oddAt (by rintro rfl; simp [real])
        fun _ candidate => prepareArcsin_eq_real q levels candidate h.1 h.2
  | acos =>
      have h : -1 ≤ q ∧ q ≤ 1 := hdomain
      change (if -1 ≤ q ∧ q ≤ 1 then _ else Rule.invalid).Locates _
      simp only [h]
      exact fun candidate => prepareArccos_eq_real q levels candidate h.1 h.2
  | atan =>
      exact Rule.locates_oddAt (by rintro rfl; simp [real])
        fun _ candidate => prepareArctan_eq_real q levels candidate
  | asinPi =>
      have h : -1 ≤ q ∧ q ≤ 1 := hdomain
      change (if -1 ≤ q ∧ q ≤ 1 then _ else Rule.invalid).Locates _
      simp only [h]
      exact Rule.locates_oddAt (by rintro rfl; simp [real])
        fun _ candidate => prepareArcsinPi_eq_real q levels candidate h.1 h.2
  | acosPi =>
      have h : -1 ≤ q ∧ q ≤ 1 := hdomain
      change (if -1 ≤ q ∧ q ≤ 1 then _ else Rule.invalid).Locates _
      simp only [h]
      exact fun candidate => prepareArccosPi_eq_real q levels candidate h.1 h.2
  | atanPi =>
      exact Rule.locates_oddAt (by rintro rfl; simp [real])
        fun _ candidate => prepareArctanPi_eq_real q levels candidate
  | sinh =>
      exact Rule.locates_oddAt (by rintro rfl; simp [real])
        fun _ candidate => compareSinh_eq_real q candidate
  | cosh => exact fun candidate => compareCosh_eq_real q candidate
  | tanh =>
      exact Rule.locates_oddAt (by rintro rfl; simp [real])
        fun _ candidate => compareTanh_eq_real q candidate
  | asinh =>
      exact Rule.locates_oddAt (by rintro rfl; simp [real])
        fun _ candidate => prepareArsinh_eq_real q levels candidate
  | acosh =>
      have h : 1 ≤ q := hdomain
      change (if 1 ≤ q then Rule.real (prepareArcosh q levels).compare else Rule.invalid).Locates _
      simp only [h, ↓reduceIte]
      exact fun candidate => prepareArcosh_eq_real q levels candidate h
  | atanh =>
      have h : -1 < q ∧ q < 1 := hdomain
      change (if hlower : -1 < q then
          if hupper : q < 1 then
            Rule.oddAt negative q (prepareArtanh q levels hlower hupper).compare
          else if q = 1 then Rule.pole false else Rule.invalid
        else if q = -1 then Rule.pole true else Rule.invalid).Locates _
      simp only [h.1, h.2, ↓reduceDIte]
      exact Rule.locates_oddAt (by rintro rfl; simp [real])
        fun _ candidate => prepareArtanh_eq_real q levels h.1 h.2 candidate

/-- In its domain the expression of a function denotes the function. -/
theorem eval_expr (function : Function) {q : ℚ} (hdomain : function.Domain q) (env : Nat → ℝ) :
    (function.expr q).eval env = function.real q := by
  cases function
  case exp2 => simpa [expr, real] using eval_powerExpr (by norm_num : (0 : ℚ) < 2) q env
  case exp2m1 =>
    simp only [expr, real, Interval.Expr.eval, Interval.BinaryOp.eval,
      eval_powerExpr (by norm_num : (0 : ℚ) < 2)]
    norm_num
  case exp10 => simpa [expr, real] using eval_powerExpr (by norm_num : (0 : ℚ) < 10) q env
  case exp10m1 =>
    simp only [expr, real, Interval.Expr.eval, Interval.BinaryOp.eval,
      eval_powerExpr (by norm_num : (0 : ℚ) < 10)]
    norm_num
  case log2 => simpa [expr, real] using eval_logarithmExpr 2 q env
  case log10 => simpa [expr, real] using eval_logarithmExpr 10 q env
  case log2p1 => simpa [expr, real] using eval_logarithmExpr 2 (q + 1) env
  case log10p1 => simpa [expr, real] using eval_logarithmExpr 10 (q + 1) env
  case asinh =>
    simp only [expr, real]
    split_ifs with hneg
    · have hreal : (q : ℝ) < 0 := by exact_mod_cast hneg
      simp only [Interval.Expr.eval, Interval.UnaryOp.eval, Interval.BinaryOp.eval]
      rw [← _root_.neg_neg (q : ℝ), Real.arsinh_neg, Real.arsinh]
      push_cast
      rw [abs_of_neg hreal, neg_sq]
    · have hreal : (0 : ℝ) ≤ q := by exact_mod_cast not_lt.mp hneg
      simp only [Interval.Expr.eval, Interval.UnaryOp.eval, Interval.BinaryOp.eval]
      rw [Real.arsinh]
      push_cast
      rw [abs_of_nonneg hreal]
  case acosh =>
    simp only [expr, real, Interval.Expr.eval, Interval.UnaryOp.eval, Interval.BinaryOp.eval,
      Real.arcosh]
    push_cast
    rfl
  case atanh =>
    have hq : -1 < q ∧ q < 1 := hdomain
    have hmem : (q : ℝ) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by exact_mod_cast hq.1.le, by exact_mod_cast hq.2.le⟩
    simp only [expr, real, Interval.Expr.eval, Interval.UnaryOp.eval, Interval.BinaryOp.eval]
    rw [Real.artanh_eq_half_log hmem]
    push_cast
    rfl
  all_goals
    simp [expr, real, Interval.Expr.eval, Interval.UnaryOp.eval, Interval.BinaryOp.eval,
      eval_piExpr]

/-- In the domain the hint of a function is right about the real function. -/
theorem hint_sound (function : Function) (negative : Bool) {q : ℚ}
    (hdomain : function.Domain q) :
    Hint.Sound (function.hint fmt (.finite negative q)) (function.real q) := by
  intro found h
  simp only [hint] at h
  split_ifs at h
  exact nearest?_sound (eval_expr function hdomain _) _ found h

/--
**`inexact` means that the result is not the real value.** For a finite operand in the domain
and every rounding direction, a member of `Function` raises `inexact` exactly when its finite
result is not the value of the real function.
-/
theorem inexact_apply_iff (function : Function) {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) (hdomain : function.Domain q) (mode : IEEERoundingMode)
    (hfinite : isFinite (function.apply x mode).value = true) :
    (function.apply x mode).status.inexact = true ↔
      toReal (function.apply x mode).value ≠ function.real q := by
  unfold apply at hfinite ⊢
  rw [unary_of_toRat? _ hq] at hfinite ⊢
  exact Rule.deliver_inexact_iff (function.locates _ _ hdomain) mode
    (function.hint_sound _ hdomain) hfinite

/--
**The recommended functions of one argument are correctly rounded.** For a conventional IEEE
descriptor, a member of `Function` and a finite operand whose exact value `q` is in the
function's domain, a finite result denotes `roundAt fmt` of the real function at `q`.
-/
theorem toReal_apply (hfmt : fmt.isIEEE = true) (function : Function) {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) (hdomain : function.Domain q)
    (hfinite : isFinite (function.apply x).value = true) :
    toReal (function.apply x).value = roundAt fmt (function.real q) :=
  toReal_unary hfmt _ hq (function.locates _ _ hdomain) (function.hint_sound _ hdomain) hfinite

/--
**The directed results enclose the function.** For a conventional IEEE descriptor, a member of
`Function` and a finite operand whose exact value `q` is in the function's domain, the result
toward negative infinity is at most the real function at `q` and the result toward positive
infinity at least that, in the extended reals.
-/
theorem apply_encloses (hfmt : fmt.isIEEE = true) (function : Function) {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) (hdomain : function.Domain q) :
    toEReal (function.apply x .down).value ≤ (function.real q : EReal) ∧
      (function.real q : EReal) ≤ toEReal (function.apply x .up).value :=
  unary_encloses hfmt _ hq (function.locates _ _ hdomain) _

end Function

/-- The rule of `powr` at a positive base and a finite exponent locates `p ^ q`. -/
theorem locates_powr (negative negative' : Bool) {p q : ℚ} (hp : 0 < p) :
    (powrRule (.finite negative p) (.finite negative' q)).Locates ((p : ℝ) ^ (q : ℝ)) := by
  change (if p < 0 then Rule.invalid else if p = 0 then _
    else Rule.real (RationalPower.compare p q)).Locates _
  simp only [not_lt.mpr hp.le, hp.ne', ↓reduceIte]
  exact fun candidate => RationalPower.compare_eq_real p q candidate hp.le

/-- The rule of `compound` at an operand above -1 locates `(1 + q) ^ n`. -/
theorem locates_compound (negative : Bool) {q : ℚ} (hq : -1 < q) (n : ℤ) :
    (compoundRule n (.finite negative q)).Locates ((1 + (q : ℝ)) ^ (n : ℝ)) := by
  change (if q < -1 then Rule.invalid else if q = -1 then _
    else Rule.real (RationalPower.compare (1 + q) n)).Locates _
  simp only [not_lt.mpr hq.le, hq.ne', ↓reduceIte]
  intro candidate
  simpa using RationalPower.compare_eq_real (1 + q) n candidate (by linarith)

/-- The hint of `powr` at a positive base is right about the power. -/
theorem powrHint_sound (negative negative' : Bool) {p q : ℚ} (hp : 0 < p) :
    Hint.Sound (powrHint fmt (.finite negative p) (.finite negative' q))
      ((p : ℝ) ^ (q : ℝ)) := by
  intro found h
  simp only [powrHint] at h
  split_ifs at h
  exact nearest?_sound (eval_powerExpr hp q _) true found h

/-- The hint of `compound` at an operand above -1 is right about the power. -/
theorem compoundHint_sound (negative : Bool) {q : ℚ} (hq : -1 < q) (n : ℤ) :
    Hint.Sound (compoundHint fmt n (.finite negative q)) ((1 + (q : ℝ)) ^ (n : ℝ)) := by
  intro found h
  simp only [compoundHint] at h
  split_ifs at h
  have htarget : (powerExpr (1 + q) n).eval (fun _ => 0) = (1 + (q : ℝ)) ^ (n : ℝ) := by
    rw [eval_powerExpr (show (0 : ℚ) < 1 + q by linarith)]
    push_cast
    rfl
  exact nearest?_sound htarget true found h

/-- At a finite operand that is not a NaN, `compound` is the function of its rule, with its
hint. -/
theorem compound_eq_unary {x : Model fmt} {q : ℚ} (hx : toRat? x = some q) (n : ℤ)
    (mode : IEEERoundingMode) :
    compound x n mode = unary (compoundRule n) x mode (compoundHint fmt n) := by
  have hnan : isNaN x = false :=
    isNaN_eq_false_of_isFinite_eq_true x (Algebraic.isFinite_of_toRat?_eq_some hx)
  simp [compound, hnan]

/-- The rule of `atan2` at a nonzero `y` locates the angle of `x + i y`. -/
theorem locates_atan2 (levels : Nat) (negative negative' : Bool) {qy qx : ℚ} (hne : qy ≠ 0) :
    (angleRule false levels (.finite negative qy) (.finite negative' qx)).Locates
      (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩) := by
  change (if qy = 0 then _ else if false = true then _
    else Rule.real (prepareAtan2 qx qy _).compare).Locates _
  simp only [hne, ↓reduceIte, Bool.false_eq_true]
  exact fun candidate => prepareAtan2_eq_real qx qy _ candidate

/-- The expression of an angle denotes the argument of `x + i y`, divided by π in half-turns. -/
theorem eval_angleExpr (halfTurns : Bool) (x y : ℚ) (env : Nat → ℝ) :
    (angleExpr halfTurns x y).eval env =
      if halfTurns then Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ / Real.pi
      else Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ := by
  have hnorm : ‖(⟨(x : ℝ), (y : ℝ)⟩ : ℂ)‖ = Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) :=
    Complex.norm_eq_sqrt_sq_add_sq _
  have hangle : (if 0 ≤ x then
        Interval.Expr.unary .asin (.binary .div (.const y) (.unary .sqrt (.const (x ^ 2 + y ^ 2))))
      else if 0 ≤ y then
        .binary .add (.unary .asin (.binary .div (.const (-y))
          (.unary .sqrt (.const (x ^ 2 + y ^ 2))))) piExpr
      else .binary .sub (.unary .asin (.binary .div (.const (-y))
          (.unary .sqrt (.const (x ^ 2 + y ^ 2))))) piExpr).eval env =
      Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ := by
    split_ifs with hx hy
    · have hre : (0 : ℝ) ≤ (⟨(x : ℝ), (y : ℝ)⟩ : ℂ).re := by
        change (0 : ℝ) ≤ (x : ℝ)
        exact_mod_cast hx
      rw [Complex.arg_of_re_nonneg hre, hnorm]
      simp [Interval.Expr.eval, Interval.UnaryOp.eval, Interval.BinaryOp.eval]
    · have hre : (⟨(x : ℝ), (y : ℝ)⟩ : ℂ).re < 0 := by
        change (x : ℝ) < 0
        exact_mod_cast not_le.mp hx
      have him : (0 : ℝ) ≤ (⟨(x : ℝ), (y : ℝ)⟩ : ℂ).im := by
        change (0 : ℝ) ≤ (y : ℝ)
        exact_mod_cast hy
      rw [Complex.arg_of_re_neg_of_im_nonneg hre him, hnorm]
      simp [Interval.Expr.eval, Interval.UnaryOp.eval, Interval.BinaryOp.eval, eval_piExpr]
    · have hre : (⟨(x : ℝ), (y : ℝ)⟩ : ℂ).re < 0 := by
        change (x : ℝ) < 0
        exact_mod_cast not_le.mp hx
      have him : (⟨(x : ℝ), (y : ℝ)⟩ : ℂ).im < 0 := by
        change (y : ℝ) < 0
        exact_mod_cast not_le.mp hy
      rw [Complex.arg_of_re_neg_of_im_neg hre him, hnorm]
      simp [Interval.Expr.eval, Interval.UnaryOp.eval, Interval.BinaryOp.eval, eval_piExpr]
  unfold angleExpr
  cases halfTurns
  · simpa using hangle
  · simp only [↓reduceIte, Interval.Expr.eval, Interval.BinaryOp.eval, eval_piExpr]
    rw [hangle]

/-- The hint of an angle at a nonzero `y` is right about the angle of `x + i y`, in radians or
in half-turns. -/
theorem angleHint_sound (halfTurns negative negative' : Bool) (qy qx : ℚ) :
    Hint.Sound (angleHint fmt halfTurns (.finite negative qy) (.finite negative' qx))
      (if halfTurns then Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi
        else Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩) := by
  intro found h
  simp only [angleHint] at h
  split_ifs at h
  exact nearest?_sound (eval_angleExpr halfTurns qx qy _) false found h

/-- The rule of `atan2Pi` at a nonzero `y` locates the angle of `x + i y` divided by π. -/
theorem locates_atan2Pi (levels : Nat) (negative negative' : Bool) {qy qx : ℚ} (hne : qy ≠ 0) :
    (angleRule true levels (.finite negative qy) (.finite negative' qx)).Locates
      (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi) := by
  change (if qy = 0 then _ else if true = true then Rule.real (prepareAtan2Pi qx qy _).compare
    else _).Locates _
  simp only [hne, ↓reduceIte]
  exact fun candidate => prepareAtan2Pi_eq_real qx qy _ candidate

/--
**`powr` is correctly rounded.** For a conventional IEEE descriptor, a finite positive base
and a finite exponent, a finite result denotes `roundAt fmt (p ^ q)`.
-/
theorem toReal_powr (hfmt : fmt.isIEEE = true) {x y : Model fmt} {p q : ℚ}
    (hx : toRat? x = some p) (hy : toRat? y = some q) (hp : 0 < p)
    (hfinite : isFinite (powr x y).value = true) :
    toReal (powr x y).value = roundAt fmt ((p : ℝ) ^ (q : ℝ)) :=
  toReal_binary hfmt powrRule hx hy (locates_powr _ _ hp) (powrHint_sound _ _ hp) hfinite

/--
**The directed results of `powr` enclose the power.** For a conventional IEEE descriptor, a
finite positive base and a finite exponent, the result toward negative infinity is at most
`p ^ q` and the result toward positive infinity at least `p ^ q`.
-/
theorem powr_encloses (hfmt : fmt.isIEEE = true) {x y : Model fmt} {p q : ℚ}
    (hx : toRat? x = some p) (hy : toRat? y = some q) (hp : 0 < p) :
    toEReal (powr x y .down).value ≤ (((p : ℝ) ^ (q : ℝ) : ℝ) : EReal) ∧
      (((p : ℝ) ^ (q : ℝ) : ℝ) : EReal) ≤ toEReal (powr x y .up).value :=
  binary_encloses hfmt powrRule hx hy (locates_powr _ _ hp) _

/--
**`compound` is correctly rounded.** For a conventional IEEE descriptor, a finite operand
above -1 and an integer `n`, a finite result denotes `roundAt fmt ((1 + q) ^ n)`.
-/
theorem toReal_compound (hfmt : fmt.isIEEE = true) {x : Model fmt} {q : ℚ}
    (hx : toRat? x = some q) (hq : -1 < q) (n : ℤ)
    (hfinite : isFinite (compound x n).value = true) :
    toReal (compound x n).value = roundAt fmt ((1 + (q : ℝ)) ^ (n : ℝ)) := by
  rw [compound_eq_unary hx] at hfinite ⊢
  exact toReal_unary hfmt _ hx (locates_compound _ hq n) (compoundHint_sound _ hq n) hfinite

/--
**The directed results of `compound` enclose the power.** For a conventional IEEE descriptor, a
finite operand above -1 and an integer `n`, the result toward negative infinity is at most
`(1 + q) ^ n` and the result toward positive infinity at least that.
-/
theorem compound_encloses (hfmt : fmt.isIEEE = true) {x : Model fmt} {q : ℚ}
    (hx : toRat? x = some q) (hq : -1 < q) (n : ℤ) :
    toEReal (compound x n .down).value ≤ (((1 + (q : ℝ)) ^ (n : ℝ) : ℝ) : EReal) ∧
      (((1 + (q : ℝ)) ^ (n : ℝ) : ℝ) : EReal) ≤ toEReal (compound x n .up).value := by
  rw [compound_eq_unary hx, compound_eq_unary hx]
  exact unary_encloses hfmt _ hx (locates_compound _ hq n) _

/--
**`atan2` is correctly rounded.** For a conventional IEEE descriptor and finite operands with a
nonzero `y`, a finite result denotes `roundAt fmt` of the angle of `x + i y`.
-/
theorem toReal_atan2 (hfmt : fmt.isIEEE = true) {y x : Model fmt} {qy qx : ℚ}
    (hy : toRat? y = some qy) (hx : toRat? x = some qx) (hne : qy ≠ 0)
    (hfinite : isFinite (atan2 y x).value = true) :
    toReal (atan2 y x).value = roundAt fmt (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩) :=
  toReal_binary hfmt _ hy hx (locates_atan2 _ _ _ hne) (angleHint_sound false _ _ qy qx) hfinite

/--
**The directed results of `atan2` enclose the angle.** For a conventional IEEE descriptor and
finite operands with a nonzero `y`, the result toward negative infinity is at most the angle of
`x + i y` and the result toward positive infinity at least that.
-/
theorem atan2_encloses (hfmt : fmt.isIEEE = true) {y x : Model fmt} {qy qx : ℚ}
    (hy : toRat? y = some qy) (hx : toRat? x = some qx) (hne : qy ≠ 0) :
    toEReal (atan2 y x .down).value ≤ (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ : EReal) ∧
      (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ : EReal) ≤ toEReal (atan2 y x .up).value :=
  binary_encloses hfmt _ hy hx (locates_atan2 _ _ _ hne) _

/--
**`atan2Pi` is correctly rounded.** For a conventional IEEE descriptor and finite operands with
a nonzero `y`, a finite result denotes `roundAt fmt` of the angle of `x + i y` divided by π.
-/
theorem toReal_atan2Pi (hfmt : fmt.isIEEE = true) {y x : Model fmt} {qy qx : ℚ}
    (hy : toRat? y = some qy) (hx : toRat? x = some qx) (hne : qy ≠ 0)
    (hfinite : isFinite (atan2Pi y x).value = true) :
    toReal (atan2Pi y x).value =
      roundAt fmt (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi) :=
  toReal_binary hfmt _ hy hx (locates_atan2Pi _ _ _ hne) (angleHint_sound true _ _ qy qx) hfinite

/--
**The directed results of `atan2Pi` enclose the angle in half turns.** For a conventional IEEE
descriptor and finite operands with a nonzero `y`, the result toward negative infinity is at
most the angle of `x + i y` divided by π and the result toward positive infinity at least that.
-/
theorem atan2Pi_encloses (hfmt : fmt.isIEEE = true) {y x : Model fmt} {qy qx : ℚ}
    (hy : toRat? y = some qy) (hx : toRat? x = some qx) (hne : qy ≠ 0) :
    toEReal (atan2Pi y x .down).value ≤
        ((Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi : ℝ) : EReal) ∧
      ((Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi : ℝ) : EReal) ≤
        toEReal (atan2Pi y x .up).value :=
  binary_encloses hfmt _ hy hx (locates_atan2Pi _ _ _ hne) _

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded
