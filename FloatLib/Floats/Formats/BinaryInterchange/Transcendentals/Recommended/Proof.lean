/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Recommended.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Comparison.Underflow
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
`Function.Domain` the finite arguments at which it is a real number (the domain of the function
without its poles). The theorems are for a finite operand whose exact value `q` is in the
domain, and each of them is one statement for the 26 functions of one argument. Each named
function (`exp2`, `sin`, `atanh`, ...) is `Function.apply` at its member by definition, so the
theorems apply to it as they stand. `Function.apply_roundsTo` and its siblings for the
functions of two arguments hold for every format descriptor: a conventional IEEE one, a format
without an infinity such as OCP E4M3, a format with one zero such as ONNX E4M3FNUZ, or a format
in which every encoding is finite. The equations to nearest-even and the enclosures are stated
for a conventional IEEE descriptor.

* `Function.apply_roundsTo`: in every rounding direction the result is the correctly rounded
  value of the real function at `q`, when that is not zero. With `roundAt fmt r mode` the
  rounding of `r` in the direction `mode` on the grid of the format with an unbounded exponent
  range, the result is finite and denotes `roundAt fmt (function.real q) mode` when that value
  is at most the largest finite magnitude, it is the overflow result of the direction otherwise
  (IEEE 754-2019, clause 7.4), and in a format with signed zeros it has the sign of the real
  function, also when it is a zero (`RoundsTo`). The directions are the five rounding-direction
  attributes of IEEE 754-2019 and rounding away from zero. `Function.isZero_apply` is the case
  of a real value that is zero: the result is a zero.
* `Function.toReal_apply`: to nearest-even a finite result is `roundAt fmt` of the real
  function, without a premise on the range.
* `Function.inexact_apply_iff`: `inexact` is raised exactly when the finite result is not the
  real value, in every direction.
* `Function.overflow_apply_iff`: `overflow` is raised exactly when the rounding of the real
  value with an unbounded exponent range exceeds the largest finite value in magnitude, in
  every direction and for every format descriptor (IEEE 754-2019 §7.4).
* `Function.underflow_apply_iff`: `underflow` is raised exactly when `inexact` is raised and the
  magnitude of the real value is tiny after rounding in the direction, for every format
  descriptor (IEEE 754-2019 §7.5 with tininess detected after rounding).
* `Function.invalid_divideByZero_apply`: neither `invalid` nor `divideByZero` is raised.
* `Function.apply_encloses`: the result toward negative infinity is at most the real function
  and the result toward positive infinity at least, in the extended reals.

`powr_roundsTo`, `compound_roundsTo`, `atan2_roundsTo` and `atan2Pi_roundsTo` are the statement
in every direction for the functions of two arguments, at finite operands: a positive base for
`powr`, an operand above -1 for `compound`, and a nonzero `y` for the angles, which are
`Complex.arg` of `x + i y`. `pow_roundsTo_of_pos` and `pow_roundsTo_of_neg` are the statement
for `pow`: at a finite positive base with any finite exponent, and at a finite negative base
with an integral exponent. `toReal_powr`, `toReal_compound`, `toReal_atan2` and
`toReal_atan2Pi` are the nearest-even equations, and `powr_encloses`, `compound_encloses`,
`atan2_encloses` and `atan2Pi_encloses` the enclosures. `powr_overflow_iff`,
`compound_overflow_iff`, `pow_overflow_iff_of_pos`, `pow_overflow_iff_of_neg` and
`atan2_overflow_iff` are the statement on the overflow flag, and `powr_underflow_iff`,
`compound_underflow_iff`, `pow_underflow_iff_of_pos`, `pow_underflow_iff_of_neg` and
`atan2_underflow_iff` the statement on the underflow flag. `powr_inexact_iff`,
`compound_inexact_iff`, `pow_inexact_iff_of_pos`, `pow_inexact_iff_of_neg`, `atan2_inexact_iff`
and `atan2Pi_inexact_iff` are the statement on `inexact`, and `powr_invalid_divideByZero`,
`compound_invalid_divideByZero`, `pow_invalid_divideByZero_of_pos`,
`pow_invalid_divideByZero_of_neg` and `atan2_invalid_divideByZero` say that neither `invalid`
nor `divideByZero` is raised.

To nearest-even every function takes its value from an enclosure when one settles it.
`Function.eval_expr` shows that the expression that is enclosed denotes the function,
`settle_sound` that an enclosure which settles gives `roundAt fmt` of the number its expression
denotes, `settle_signed` that the value has the sign of that number, and `Function.hint_sound`,
`Function.hint_signed` and their siblings for the functions of two arguments put these
together, so the theorems hold whichever path delivers the value.

No theorem has a hypothesis on the number of search steps. The special cases at zeros,
infinities and NaNs are definitions, read off ISO/IEC 9899:2024 F.10.1 to F.10.4, and are not
theorems.
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

/-- The enclosure that `settle` rounds contains the number that its expression denotes. -/
private theorem contains_of_eval? {expression : Interval.Expr} {target : ℝ}
    (htarget : expression.eval (fun _ => 0) = target) {config : Interval.Backend.Config}
    {bounds : Numerics.Interval ℤ}
    (hbounds : expression.eval? (Interval.Backend.binaryGrid config) (fun _ => none) =
      some bounds) :
    (Enclosure.BinaryGrid.toRationalInterval config.precision bounds).Contains target := by
  rw [Enclosure.BinaryGrid.contains_toRationalInterval, ← htarget]
  exact Interval.Expr.containsReal_eval? expression
    (Interval.Backend.binaryGrid_sound config) (env := fun _ => none) (by simp) hbounds

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
    have hcontains := contains_of_eval? htarget hbounds
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

/--
An enclosure that settles gives a value with the sign of the number that its expression
denotes, also when that value is a zero.
-/
theorem settle_signed {expression : Interval.Expr} {target : ℝ}
    (htarget : expression.eval (fun _ => 0) = target) {config : Interval.Backend.Config}
    {found : Hint fmt} (h : settle fmt expression config = some found) :
    signBit found.value = decide (target < 0) := by
  unfold settle at h
  split at h
  · exact absurd h (by simp)
  · next bounds hbounds =>
    dsimp only at h
    split at h
    · exact absurd h (by simp)
    · next value hvalue =>
      cases Option.some.inj h
      exact signBit_of_round?_eq_some (contains_of_eval? htarget hbounds) hvalue

/-- The enclosure search for an expression that denotes `target` gives a value with the sign of
`target`. -/
theorem nearest?_signed {expression : Interval.Expr} {target : ℝ}
    (htarget : expression.eval (fun _ => 0) = target) (slow : Bool) :
    Hint.Signed (fun _ => nearest? fmt expression slow) target := by
  intro found h
  obtain ⟨config, -, hconfig⟩ := List.exists_of_findSome?_eq_some h
  exact settle_signed htarget hconfig

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

/-- The hint of a function in its domain has the sign of the real function. -/
theorem hint_signed (function : Function) (negative : Bool) {q : ℚ}
    (hdomain : function.Domain q) :
    Hint.Signed (function.hint fmt (.finite negative q)) (function.real q) := by
  intro found h
  simp only [hint] at h
  split_ifs at h
  exact nearest?_signed (eval_expr function hdomain _) _ found h

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

/--
**The recommended functions of one argument are correctly rounded in every direction.** For
every format descriptor (a conventional IEEE one, a format without an infinity such as OCP
E4M3, a format with one zero such as ONNX E4M3FNUZ, or a format in which every encoding is
finite), each rounding direction `mode`, a member of `Function` and a finite operand whose
exact value `q` is in the function's domain with a real value that is not zero: the result is
finite and denotes `roundAt fmt (function.real q) mode` when that value is at most the largest
finite magnitude, it is the overflow result of the direction otherwise, and in a format with
signed zeros it has the sign of the real value.
-/
theorem apply_roundsTo {mode : IEEERoundingMode} (function : Function)
    {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) (hdomain : function.Domain q) (hne : function.real q ≠ 0) :
    RoundsTo fmt mode (function.real q) (decide (function.real q < 0))
      (function.apply x mode).value :=
  unary_roundsTo _ hq (function.locates _ _ hdomain) hne
    (function.hint_sound _ hdomain) (function.hint_signed _ hdomain)

/-- At a finite operand in the domain a member of `Function` raises neither `invalid` nor
`divideByZero`, in every rounding direction and for every format descriptor. -/
theorem invalid_divideByZero_apply (function : Function) {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) (hdomain : function.Domain q) (mode : IEEERoundingMode) :
    (function.apply x mode).status.invalid = false ∧
      (function.apply x mode).status.divideByZero = false :=
  unary_invalid_divideByZero _ hq (function.locates _ _ hdomain) mode _

/--
**`overflow` is the overflow of the standard.** For every format descriptor, a member of
`Function`, a finite operand whose exact value `q` is in the function's domain with a real
value that is not zero and each rounding direction `mode`, `overflow` is raised exactly when
the rounding of the real value on the grid of the format with an unbounded exponent range
exceeds the largest finite value in magnitude (IEEE 754-2019 §7.4).
-/
theorem overflow_apply_iff (function : Function) {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) (hdomain : function.Domain q) (hne : function.real q ≠ 0)
    (mode : IEEERoundingMode) :
    (function.apply x mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt (function.real q) mode| :=
  unary_overflow_iff _ hq (function.locates _ _ hdomain) hne mode
    (function.hint_sound _ hdomain) (function.hint_signed _ hdomain)

/--
**`underflow` is the underflow of the standard.** For every format descriptor, a member of
`Function`, a finite operand whose exact value `q` is in the function's domain with a real
value that is not zero and each rounding direction `mode`, `underflow` is raised exactly when
`inexact` is raised and the magnitude of the real value is tiny after rounding: its rounding to
the precision of the format with an unbounded exponent range is below the least normal
magnitude (IEEE 754-2019 §7.5).
-/
theorem underflow_apply_iff (function : Function) {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) (hdomain : function.Domain q) (hne : function.real q ≠ 0)
    (mode : IEEERoundingMode) :
    (function.apply x mode).status.underflow = true ↔
      (function.apply x mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide (function.real q < 0))) |function.real q| :=
  unary_underflow_iff _ hq (function.locates _ _ hdomain) hne mode
    (function.hint_sound _ hdomain) (function.hint_signed _ hdomain)

/--
For a member of `Function` and a finite operand whose exact value `q` is in the function's
domain with a real value of zero, the result is a zero in every rounding direction.
-/
theorem isZero_apply (function : Function) {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) (hdomain : function.Domain q) (hzero : function.real q = 0)
    (mode : IEEERoundingMode) : isZero (function.apply x mode).value = true := by
  unfold apply
  rw [unary_of_toRat? _ hq]
  exact Rule.isZero_deliver (hzero ▸ function.locates _ _ hdomain) mode
    (hzero ▸ function.hint_sound _ hdomain)

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

/-- The hint of `powr` at a positive base has the sign of the power. -/
theorem powrHint_signed (negative negative' : Bool) {p q : ℚ}
    (hp : 0 < p) :
    Hint.Signed (powrHint fmt (.finite negative p) (.finite negative' q))
      ((p : ℝ) ^ (q : ℝ)) := by
  intro found h
  simp only [powrHint] at h
  split_ifs at h
  exact nearest?_signed (eval_powerExpr hp q _) true found h

/-- The hint of `compound` at an operand above -1 has the sign of the power. -/
theorem compoundHint_signed (negative : Bool) {q : ℚ} (hq : -1 < q)
    (n : ℤ) :
    Hint.Signed (compoundHint fmt n (.finite negative q)) ((1 + (q : ℝ)) ^ (n : ℝ)) := by
  intro found h
  simp only [compoundHint] at h
  split_ifs at h
  have htarget : (powerExpr (1 + q) n).eval (fun _ => 0) = (1 + (q : ℝ)) ^ (n : ℝ) := by
    rw [eval_powerExpr (show (0 : ℚ) < 1 + q by linarith)]
    push_cast
    rfl
  exact nearest?_signed htarget true found h

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

/-- The hint of an angle at a nonzero `y` has the sign of the angle of `x + i y`, in radians or
in half-turns. -/
theorem angleHint_signed (halfTurns negative negative' : Bool)
    (qy qx : ℚ) :
    Hint.Signed (angleHint fmt halfTurns (.finite negative qy) (.finite negative' qx))
      (if halfTurns then Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi
        else Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩) := by
  intro found h
  simp only [angleHint] at h
  split_ifs at h
  exact nearest?_signed (eval_angleExpr halfTurns qx qy _) false found h

/-- The angle of `x + i y` is not zero for a nonzero `y`, and it is negative exactly when `y`
is. -/
private theorem arg_ne_zero_and_neg_iff {qy : ℚ} (qx : ℚ) (hne : qy ≠ 0) :
    Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ ≠ 0 ∧
      (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ < 0 ↔ qy < 0) := by
  refine ⟨fun h => hne ?_, ?_⟩
  · have him : (qy : ℝ) = 0 := (Complex.arg_eq_zero_iff.mp h).2
    exact_mod_cast him
  · rw [Complex.arg_neg_iff]
    change (qy : ℝ) < 0 ↔ qy < 0
    exact_mod_cast Iff.rfl

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

/-! ## Every rounding direction -/

/--
**`powr` is correctly rounded in every direction.** For every format descriptor and each
rounding direction `mode`, a finite positive base and a finite exponent: the result is finite
and denotes `roundAt fmt (p ^ q) mode` when that value is at most the largest finite magnitude,
it is the overflow result of the direction otherwise, and in a format with signed zeros its
sign bit is clear.
-/
theorem powr_roundsTo {mode : IEEERoundingMode} {x y : Model fmt}
    {p q : ℚ} (hx : toRat? x = some p) (hy : toRat? y = some q) (hp : 0 < p) :
    RoundsTo fmt mode ((p : ℝ) ^ (q : ℝ)) false (powr x y mode).value := by
  have hpos : (0 : ℝ) < (p : ℝ) ^ (q : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hp) _
  have h := binary_roundsTo (mode := mode) powrRule hx hy (locates_powr _ _ hp) hpos.ne'
    (powrHint_sound _ _ hp) (powrHint_signed _ _ hp)
  rwa [decide_eq_false (not_lt.mpr hpos.le)] at h

/--
**`compound` is correctly rounded in every direction.** For every format descriptor and each
rounding direction `mode`, a finite operand above -1 and an integer `n`: the result is finite
and denotes `roundAt fmt ((1 + q) ^ n) mode` when that value is at most the largest finite
magnitude, it is the overflow result of the direction otherwise, and in a format with signed
zeros its sign bit is clear.
-/
theorem compound_roundsTo {mode : IEEERoundingMode} {x : Model fmt}
    {q : ℚ} (hx : toRat? x = some q) (hq : -1 < q) (n : ℤ) :
    RoundsTo fmt mode ((1 + (q : ℝ)) ^ (n : ℝ)) false (compound x n mode).value := by
  have hbase : (0 : ℝ) < 1 + (q : ℝ) := by
    have : (-1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    linarith
  have hpos : (0 : ℝ) < (1 + (q : ℝ)) ^ (n : ℝ) := Real.rpow_pos_of_pos hbase _
  rw [compound_eq_unary hx]
  have h := unary_roundsTo (mode := mode) _ hx (locates_compound _ hq n) hpos.ne'
    (compoundHint_sound _ hq n) (compoundHint_signed _ hq n)
  rwa [decide_eq_false (not_lt.mpr hpos.le)] at h

/-- `powr` at a finite positive base raises `overflow` exactly when the rounding of `p ^ q` on
the grid of the format with an unbounded exponent range exceeds the largest finite value, in
every rounding direction and for every format descriptor. -/
theorem powr_overflow_iff {x y : Model fmt} {p q : ℚ} (hx : toRat? x = some p)
    (hy : toRat? y = some q) (hp : 0 < p) (mode : IEEERoundingMode) :
    (powr x y mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt ((p : ℝ) ^ (q : ℝ)) mode| :=
  binary_overflow_iff powrRule hx hy (locates_powr _ _ hp)
    (Real.rpow_pos_of_pos (by exact_mod_cast hp) _).ne' mode (powrHint_sound _ _ hp)
    (powrHint_signed _ _ hp)

/-- `powr` at a finite positive base raises `underflow` exactly when it raises `inexact` and
`p ^ q` is tiny after rounding in the direction, in every rounding direction and for every
format descriptor. -/
theorem powr_underflow_iff {x y : Model fmt} {p q : ℚ} (hx : toRat? x = some p)
    (hy : toRat? y = some q) (hp : 0 < p) (mode : IEEERoundingMode) :
    (powr x y mode).status.underflow = true ↔
      (powr x y mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide ((p : ℝ) ^ (q : ℝ) < 0))) |(p : ℝ) ^ (q : ℝ)| :=
  binary_underflow_iff powrRule hx hy (locates_powr _ _ hp)
    (Real.rpow_pos_of_pos (by exact_mod_cast hp) _).ne' mode (powrHint_sound _ _ hp)
    (powrHint_signed _ _ hp)

/-- `compound` at a finite operand above -1 raises `overflow` exactly when the rounding of
`(1 + q) ^ n` on the grid of the format with an unbounded exponent range exceeds the largest
finite value, in every rounding direction and for every format descriptor. -/
theorem compound_overflow_iff {x : Model fmt} {q : ℚ} (hx : toRat? x = some q) (hq : -1 < q)
    (n : ℤ) (mode : IEEERoundingMode) :
    (compound x n mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt ((1 + (q : ℝ)) ^ (n : ℝ)) mode| := by
  have hbase : (0 : ℝ) < 1 + (q : ℝ) := by
    have : (-1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    linarith
  rw [compound_eq_unary hx]
  exact unary_overflow_iff _ hx (locates_compound _ hq n) (Real.rpow_pos_of_pos hbase _).ne' mode
    (compoundHint_sound _ hq n) (compoundHint_signed _ hq n)

/-- `compound` at a finite operand above -1 raises `underflow` exactly when it raises `inexact`
and `(1 + q) ^ n` is tiny after rounding in the direction, in every rounding direction and for
every format descriptor. -/
theorem compound_underflow_iff {x : Model fmt} {q : ℚ} (hx : toRat? x = some q) (hq : -1 < q)
    (n : ℤ) (mode : IEEERoundingMode) :
    (compound x n mode).status.underflow = true ↔
      (compound x n mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide ((1 + (q : ℝ)) ^ (n : ℝ) < 0)))
          |(1 + (q : ℝ)) ^ (n : ℝ)| := by
  have hbase : (0 : ℝ) < 1 + (q : ℝ) := by
    have : (-1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    linarith
  rw [compound_eq_unary hx]
  exact unary_underflow_iff _ hx (locates_compound _ hq n) (Real.rpow_pos_of_pos hbase _).ne' mode
    (compoundHint_sound _ hq n) (compoundHint_signed _ hq n)

/-- `powr` at a finite positive base raises `inexact` exactly when its finite result is not
`p ^ q`, in every rounding direction and for every format descriptor. -/
theorem powr_inexact_iff {x y : Model fmt} {p q : ℚ} (hx : toRat? x = some p)
    (hy : toRat? y = some q) (hp : 0 < p) (mode : IEEERoundingMode)
    (hfinite : isFinite (powr x y mode).value = true) :
    (powr x y mode).status.inexact = true ↔
      toReal (powr x y mode).value ≠ (p : ℝ) ^ (q : ℝ) := by
  unfold powr at hfinite ⊢
  rw [binary_of_toRat? _ hx hy] at hfinite ⊢
  exact Rule.deliver_inexact_iff (locates_powr _ _ hp) mode (powrHint_sound _ _ hp) hfinite

/-- `powr` at a finite positive base raises neither `invalid` nor `divideByZero`, in every
rounding direction and for every format descriptor. -/
theorem powr_invalid_divideByZero {x y : Model fmt} {p q : ℚ} (hx : toRat? x = some p)
    (hy : toRat? y = some q) (hp : 0 < p) (mode : IEEERoundingMode) :
    (powr x y mode).status.invalid = false ∧ (powr x y mode).status.divideByZero = false :=
  binary_invalid_divideByZero powrRule hx hy (locates_powr _ _ hp) mode _

/-- `compound` at a finite operand above -1 raises `inexact` exactly when its finite result is
not `(1 + q) ^ n`, in every rounding direction and for every format descriptor. -/
theorem compound_inexact_iff {x : Model fmt} {q : ℚ} (hx : toRat? x = some q) (hq : -1 < q)
    (n : ℤ) (mode : IEEERoundingMode)
    (hfinite : isFinite (compound x n mode).value = true) :
    (compound x n mode).status.inexact = true ↔
      toReal (compound x n mode).value ≠ (1 + (q : ℝ)) ^ (n : ℝ) := by
  rw [compound_eq_unary hx] at hfinite ⊢
  rw [unary_of_toRat? _ hx] at hfinite ⊢
  exact Rule.deliver_inexact_iff (locates_compound _ hq n) mode (compoundHint_sound _ hq n)
    hfinite

/-- `compound` at a finite operand above -1 raises neither `invalid` nor `divideByZero`, in
every rounding direction and for every format descriptor. -/
theorem compound_invalid_divideByZero {x : Model fmt} {q : ℚ} (hx : toRat? x = some q)
    (hq : -1 < q) (n : ℤ) (mode : IEEERoundingMode) :
    (compound x n mode).status.invalid = false ∧
      (compound x n mode).status.divideByZero = false := by
  rw [compound_eq_unary hx]
  exact unary_invalid_divideByZero _ hx (locates_compound _ hq n) mode _

/-- The rule of `pow` at a positive base and a finite exponent locates `p ^ q`. -/
theorem locates_pow_of_pos (negative negative' : Bool) {p : ℚ} (hp : 0 < p) (q : ℚ) :
    (powRule (.finite negative p) (.finite negative' q)).Locates ((p : ℝ) ^ (q : ℝ)) := by
  change (if q = 0 then Rule.rational 1 else if p = 0 then _
    else if 0 < p then Rule.real (RationalPower.compare p q) else _).Locates _
  by_cases hq : q = 0
  · subst hq
    simpa using Rule.locates_rational 1
  · simp only [hq, hp.ne', hp, ↓reduceIte]
    exact fun candidate => RationalPower.compare_eq_real p q candidate hp.le

/-- The rule of `pow` at a negative base and an integral exponent locates `p ^ n`. -/
theorem locates_pow_of_neg (negative negative' : Bool) {p : ℚ} (hp : p < 0) (n : ℤ) :
    (powRule (.finite negative p) (.finite negative' (n : ℚ))).Locates ((p : ℝ) ^ n) := by
  change (if (n : ℚ) = 0 then Rule.rational 1 else if p = 0 then _
    else if 0 < p then _
    else if (n : ℚ).den = 1 then
      if (n : ℚ).num % 2 = 1 then
        Rule.real fun candidate => (RationalPower.compare (-p) (n : ℚ) (-candidate)).swap
      else Rule.real (RationalPower.compare (-p) (n : ℚ))
    else Rule.invalid).Locates _
  by_cases hn : n = 0
  · subst hn
    simpa using Rule.locates_rational 1
  · have hcast : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hmagnitude (candidate : ℚ) : RationalPower.compare (-p) (n : ℚ) candidate =
        cmp ((-(p : ℝ)) ^ n) (candidate : ℝ) := by
      rw [RationalPower.compare_eq_real (-p) n candidate (by linarith)]
      push_cast
      rw [Real.rpow_intCast]
    simp only [hcast, hp.ne, not_lt.mpr hp.le, Rat.den_intCast, Rat.num_intCast, ↓reduceIte]
    by_cases hodd : n % 2 = 1
    · simp only [hodd, ↓reduceIte]
      intro candidate
      have h := magnitude_compare hmagnitude candidate
      rwa [(Int.odd_iff.mpr hodd).neg_zpow, _root_.neg_neg] at h
    · simp only [hodd, ↓reduceIte]
      intro candidate
      have h := hmagnitude candidate
      rwa [(Int.not_odd_iff_even.mp (mt Int.odd_iff.mp hodd)).neg_zpow] at h

/-- The enclosure search has no result for a negative base, so its hint is right about every
number and has every sign. -/
private theorem powrHint_of_neg {p : ℚ} (hp : p < 0) (negativeBase negativeExponent : Bool)
    (n : ℤ) (target : ℝ) :
    Hint.Sound (powrHint fmt (.finite negativeBase p) (.finite negativeExponent n)) target ∧
      Hint.Signed (powrHint fmt (.finite negativeBase p) (.finite negativeExponent n)) target := by
  constructor <;> intro found h <;>
    simp only [powrHint, powerEnclosable, not_lt.mpr hp.le, false_and, decide_false] at h <;>
    exact absurd h (by simp)

/-- In its two exact cases `pow` delivers one rounding of the rational 1, without a hint. -/
private theorem pow_roundsTo_one {mode : IEEERoundingMode} :
    RoundsTo fmt mode 1 false ((Rule.rational 1).deliver fmt mode).value := by
  have h := Rule.deliver_roundsTo (fmt := fmt) (mode := mode) (Rule.locates_rational 1)
    (by norm_num) (hint := fun _ => none) (Hint.sound_none _) (Hint.signed_none _)
  simp only [Rat.cast_one] at h
  rwa [decide_eq_false (by norm_num : ¬(1 : ℝ) < 0)] at h

/-- A finite operand that is a zero has the exact value zero. -/
private theorem eq_zero_of_isZero {y : Model fmt} {q : ℚ} (hy : toRat? y = some q)
    (hzero : isZero y = true) : q = 0 := by
  have h := toReal_eq_zero_of_isZero y hzero
  rw [Algebraic.toReal_of_toRat?_eq_some hy] at h
  exact_mod_cast h

/--
**`pow` of a positive base is correctly rounded in every direction.** For every format
descriptor and each rounding direction `mode`, a finite positive base and a finite exponent:
the result is finite and denotes `roundAt fmt (p ^ q) mode` when that value is at most the
largest finite magnitude, it is the overflow result of the direction otherwise, and in a format
with signed zeros its sign bit is clear. No search has to settle.
-/
theorem pow_roundsTo_of_pos {mode : IEEERoundingMode}
    {x y : Model fmt} {p q : ℚ}
    (hx : toRat? x = some p) (hy : toRat? y = some q) (hp : 0 < p) :
    RoundsTo fmt mode ((p : ℝ) ^ (q : ℝ)) false (pow x y mode).value := by
  have hpos : (0 : ℝ) < (p : ℝ) ^ (q : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hp) _
  unfold pow
  split_ifs with hspecial
  · have hone : (p : ℝ) ^ (q : ℝ) = 1 := by
      rcases hspecial with ⟨hzero, -⟩ | ⟨hone, -⟩
      · simp [eq_zero_of_isZero hy hzero]
      · simp [Option.some.inj (hx.symm.trans hone)]
    rw [hone]
    exact pow_roundsTo_one
  · have h := binary_roundsTo (mode := mode) powRule hx hy (locates_pow_of_pos _ _ hp q)
      hpos.ne' (powrHint_sound _ _ hp) (powrHint_signed _ _ hp)
    rwa [decide_eq_false (not_lt.mpr hpos.le)] at h

/--
**`pow` of a negative base and an integral exponent is correctly rounded in every direction.**
For every format descriptor and each rounding direction `mode`, a finite negative base and a
finite exponent that is the integer `n`: the result is finite and denotes `roundAt fmt (p ^ n)
mode` when that value is at most the largest finite magnitude, it is the overflow result of the
direction otherwise, and in a format with signed zeros it has the sign of `p ^ n`.
-/
theorem pow_roundsTo_of_neg {mode : IEEERoundingMode}
    {x y : Model fmt} {p : ℚ} {n : ℤ}
    (hx : toRat? x = some p) (hy : toRat? y = some (n : ℚ)) (hp : p < 0) :
    RoundsTo fmt mode ((p : ℝ) ^ n) (decide ((p : ℝ) ^ n < 0)) (pow x y mode).value := by
  have hbase : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne
  have hne : (p : ℝ) ^ n ≠ 0 := zpow_ne_zero n hbase
  unfold pow
  split_ifs with hspecial
  · have hone : (p : ℝ) ^ n = 1 := by
      rcases hspecial with ⟨hzero, -⟩ | ⟨hone, -⟩
      · have hn : n = 0 := by exact_mod_cast eq_zero_of_isZero hy hzero
        simp [hn]
      · have : p = 1 := Option.some.inj (hx.symm.trans hone)
        linarith
    rw [hone, decide_eq_false (by norm_num)]
    exact pow_roundsTo_one
  · obtain ⟨hsound, hsigned⟩ :=
      powrHint_of_neg (fmt := fmt) hp (signBit x) (signBit y) n ((p : ℝ) ^ n)
    exact binary_roundsTo powRule hx hy (locates_pow_of_neg _ _ hp n) hne hsound hsigned

/-- In its two exact cases `pow` raises `overflow` exactly when the rounding of 1 exceeds the
largest finite value. -/
private theorem pow_overflow_one (mode : IEEERoundingMode) :
    ((Rule.rational 1).deliver fmt mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt 1 mode| := by
  have h := Rule.deliver_overflow_iff (fmt := fmt) (Rule.locates_rational 1) (by norm_num) mode
    (hint := fun _ => none) (Hint.sound_none _) (Hint.signed_none _)
  simp only [Rat.cast_one] at h
  exact h

/-- In its two exact cases `pow` raises `underflow` exactly when it raises `inexact` and 1 is
tiny after rounding. -/
private theorem pow_underflow_one (mode : IEEERoundingMode) :
    ((Rule.rational 1).deliver fmt mode).status.underflow = true ↔
      ((Rule.rational 1).deliver fmt mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide ((1 : ℝ) < 0))) |(1 : ℝ)| := by
  have h := Rule.deliver_underflow_iff (fmt := fmt) (Rule.locates_rational 1) (by norm_num) mode
    (hint := fun _ => none) (Hint.sound_none _) (Hint.signed_none _)
  simp only [Rat.cast_one] at h
  exact h

/-- `pow` at a finite positive base raises `overflow` exactly when the rounding of `p ^ q` on
the grid of the format with an unbounded exponent range exceeds the largest finite value, in
every rounding direction and for every format descriptor. -/
theorem pow_overflow_iff_of_pos {x y : Model fmt} {p q : ℚ} (hx : toRat? x = some p)
    (hy : toRat? y = some q) (hp : 0 < p) (mode : IEEERoundingMode) :
    (pow x y mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt ((p : ℝ) ^ (q : ℝ)) mode| := by
  unfold pow
  split_ifs with hspecial
  · have hone : (p : ℝ) ^ (q : ℝ) = 1 := by
      rcases hspecial with ⟨hzero, -⟩ | ⟨hone, -⟩
      · simp [eq_zero_of_isZero hy hzero]
      · simp [Option.some.inj (hx.symm.trans hone)]
    rw [hone]
    exact pow_overflow_one mode
  · exact binary_overflow_iff powRule hx hy (locates_pow_of_pos _ _ hp q)
      (Real.rpow_pos_of_pos (by exact_mod_cast hp) _).ne' mode (powrHint_sound _ _ hp)
      (powrHint_signed _ _ hp)

/-- `pow` at a finite positive base raises `underflow` exactly when it raises `inexact` and
`p ^ q` is tiny after rounding in the direction, in every rounding direction and for every
format descriptor. -/
theorem pow_underflow_iff_of_pos {x y : Model fmt} {p q : ℚ} (hx : toRat? x = some p)
    (hy : toRat? y = some q) (hp : 0 < p) (mode : IEEERoundingMode) :
    (pow x y mode).status.underflow = true ↔
      (pow x y mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide ((p : ℝ) ^ (q : ℝ) < 0))) |(p : ℝ) ^ (q : ℝ)| := by
  unfold pow
  split_ifs with hspecial
  · have hone : (p : ℝ) ^ (q : ℝ) = 1 := by
      rcases hspecial with ⟨hzero, -⟩ | ⟨hone, -⟩
      · simp [eq_zero_of_isZero hy hzero]
      · simp [Option.some.inj (hx.symm.trans hone)]
    rw [hone]
    exact pow_underflow_one mode
  · exact binary_underflow_iff powRule hx hy (locates_pow_of_pos _ _ hp q)
      (Real.rpow_pos_of_pos (by exact_mod_cast hp) _).ne' mode (powrHint_sound _ _ hp)
      (powrHint_signed _ _ hp)

/-- `pow` at a finite negative base and an integral exponent raises `overflow` exactly when the
rounding of `p ^ n` on the grid of the format with an unbounded exponent range exceeds the
largest finite value in magnitude, in every rounding direction and for every format descriptor. -/
theorem pow_overflow_iff_of_neg {x y : Model fmt} {p : ℚ} {n : ℤ} (hx : toRat? x = some p)
    (hy : toRat? y = some (n : ℚ)) (hp : p < 0) (mode : IEEERoundingMode) :
    (pow x y mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt ((p : ℝ) ^ n) mode| := by
  have hbase : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne
  unfold pow
  split_ifs with hspecial
  · have hone : (p : ℝ) ^ n = 1 := by
      rcases hspecial with ⟨hzero, -⟩ | ⟨hone, -⟩
      · have hn : n = 0 := by exact_mod_cast eq_zero_of_isZero hy hzero
        simp [hn]
      · have : p = 1 := Option.some.inj (hx.symm.trans hone)
        linarith
    rw [hone]
    exact pow_overflow_one mode
  · obtain ⟨hsound, hsigned⟩ :=
      powrHint_of_neg (fmt := fmt) hp (signBit x) (signBit y) n ((p : ℝ) ^ n)
    exact binary_overflow_iff powRule hx hy (locates_pow_of_neg _ _ hp n) (zpow_ne_zero n hbase)
      mode hsound hsigned

/-- `pow` at a finite negative base and an integral exponent raises `underflow` exactly when it
raises `inexact` and the magnitude of `p ^ n` is tiny after rounding in the direction, in every
rounding direction and for every format descriptor. -/
theorem pow_underflow_iff_of_neg {x y : Model fmt} {p : ℚ} {n : ℤ} (hx : toRat? x = some p)
    (hy : toRat? y = some (n : ℚ)) (hp : p < 0) (mode : IEEERoundingMode) :
    (pow x y mode).status.underflow = true ↔
      (pow x y mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide ((p : ℝ) ^ n < 0))) |(p : ℝ) ^ n| := by
  have hbase : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne
  unfold pow
  split_ifs with hspecial
  · have hone : (p : ℝ) ^ n = 1 := by
      rcases hspecial with ⟨hzero, -⟩ | ⟨hone, -⟩
      · have hn : n = 0 := by exact_mod_cast eq_zero_of_isZero hy hzero
        simp [hn]
      · have : p = 1 := Option.some.inj (hx.symm.trans hone)
        linarith
    rw [hone]
    exact pow_underflow_one mode
  · obtain ⟨hsound, hsigned⟩ :=
      powrHint_of_neg (fmt := fmt) hp (signBit x) (signBit y) n ((p : ℝ) ^ n)
    exact binary_underflow_iff powRule hx hy (locates_pow_of_neg _ _ hp n) (zpow_ne_zero n hbase)
      mode hsound hsigned

/-- In its two exact cases `pow` raises `inexact` exactly when its finite result is not 1. -/
private theorem pow_inexact_one (mode : IEEERoundingMode)
    (hfinite : isFinite ((Rule.rational 1).deliver fmt mode).value = true) :
    ((Rule.rational 1).deliver fmt mode).status.inexact = true ↔
      toReal ((Rule.rational 1).deliver fmt mode).value ≠ 1 := by
  have h := Rule.deliver_inexact_iff (fmt := fmt) (Rule.locates_rational 1) mode
    (hint := fun _ => none) (Hint.sound_none _) hfinite
  simpa only [Rat.cast_one] using h

/-- `pow` at a finite positive base raises `inexact` exactly when its finite result is not
`p ^ q`, in every rounding direction and for every format descriptor. -/
theorem pow_inexact_iff_of_pos {x y : Model fmt} {p q : ℚ} (hx : toRat? x = some p)
    (hy : toRat? y = some q) (hp : 0 < p) (mode : IEEERoundingMode)
    (hfinite : isFinite (pow x y mode).value = true) :
    (pow x y mode).status.inexact = true ↔ toReal (pow x y mode).value ≠ (p : ℝ) ^ (q : ℝ) := by
  unfold pow at hfinite ⊢
  split_ifs at hfinite ⊢ with hspecial
  · have hone : (p : ℝ) ^ (q : ℝ) = 1 := by
      rcases hspecial with ⟨hzero, -⟩ | ⟨hone, -⟩
      · simp [eq_zero_of_isZero hy hzero]
      · simp [Option.some.inj (hx.symm.trans hone)]
    rw [hone]
    exact pow_inexact_one mode hfinite
  · rw [binary_of_toRat? _ hx hy] at hfinite ⊢
    exact Rule.deliver_inexact_iff (locates_pow_of_pos _ _ hp q) mode (powrHint_sound _ _ hp)
      hfinite

/-- `pow` at a finite negative base and an integral exponent raises `inexact` exactly when its
finite result is not `p ^ n`, in every rounding direction and for every format descriptor. -/
theorem pow_inexact_iff_of_neg {x y : Model fmt} {p : ℚ} {n : ℤ} (hx : toRat? x = some p)
    (hy : toRat? y = some (n : ℚ)) (hp : p < 0) (mode : IEEERoundingMode)
    (hfinite : isFinite (pow x y mode).value = true) :
    (pow x y mode).status.inexact = true ↔ toReal (pow x y mode).value ≠ (p : ℝ) ^ n := by
  unfold pow at hfinite ⊢
  split_ifs at hfinite ⊢ with hspecial
  · have hone : (p : ℝ) ^ n = 1 := by
      rcases hspecial with ⟨hzero, -⟩ | ⟨hone, -⟩
      · have hn : n = 0 := by exact_mod_cast eq_zero_of_isZero hy hzero
        simp [hn]
      · have : p = 1 := Option.some.inj (hx.symm.trans hone)
        linarith
    rw [hone]
    exact pow_inexact_one mode hfinite
  · obtain ⟨hsound, -⟩ :=
      powrHint_of_neg (fmt := fmt) hp (signBit x) (signBit y) n ((p : ℝ) ^ n)
    rw [binary_of_toRat? _ hx hy] at hfinite ⊢
    exact Rule.deliver_inexact_iff (locates_pow_of_neg _ _ hp n) mode hsound hfinite

/-- `pow` at a finite positive base raises neither `invalid` nor `divideByZero`, in every
rounding direction and for every format descriptor. -/
theorem pow_invalid_divideByZero_of_pos {x y : Model fmt} {p q : ℚ} (hx : toRat? x = some p)
    (hy : toRat? y = some q) (hp : 0 < p) (mode : IEEERoundingMode) :
    (pow x y mode).status.invalid = false ∧ (pow x y mode).status.divideByZero = false := by
  unfold pow
  split_ifs with hspecial
  · exact Rule.deliver_invalid_divideByZero (Rule.locates_rational 1) mode _
  · exact binary_invalid_divideByZero powRule hx hy (locates_pow_of_pos _ _ hp q) mode _

/-- `pow` at a finite negative base and an integral exponent raises neither `invalid` nor
`divideByZero`, in every rounding direction and for every format descriptor. -/
theorem pow_invalid_divideByZero_of_neg {x y : Model fmt} {p : ℚ} {n : ℤ}
    (hx : toRat? x = some p) (hy : toRat? y = some (n : ℚ)) (hp : p < 0)
    (mode : IEEERoundingMode) :
    (pow x y mode).status.invalid = false ∧ (pow x y mode).status.divideByZero = false := by
  unfold pow
  split_ifs with hspecial
  · exact Rule.deliver_invalid_divideByZero (Rule.locates_rational 1) mode _
  · exact binary_invalid_divideByZero powRule hx hy (locates_pow_of_neg _ _ hp n) mode _

/--
**`atan2` is correctly rounded in every direction.** For every format descriptor and each
rounding direction `mode` and finite operands with a nonzero `y`, the result meets the contract
`RoundsTo` for the angle of `x + i y` and the sign of `y`.
-/
theorem atan2_roundsTo {mode : IEEERoundingMode} {y x : Model fmt}
    {qy qx : ℚ} (hy : toRat? y = some qy) (hx : toRat? x = some qx) (hne : qy ≠ 0) :
    RoundsTo fmt mode (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩) (decide (qy < 0))
      (atan2 y x mode).value := by
  obtain ⟨harg, hsign⟩ := arg_ne_zero_and_neg_iff qx hne
  have h := binary_roundsTo (mode := mode) (angleRule false (Function.levels fmt)) hy hx
    (locates_atan2 _ _ _ hne) harg (angleHint_sound false _ _ qy qx)
    (angleHint_signed false _ _ qy qx)
  rwa [decide_eq_decide.mpr hsign] at h

/--
**`atan2Pi` is correctly rounded in every direction.** For every format descriptor and each
rounding direction `mode` and finite operands with a nonzero `y`, the result meets the contract
`RoundsTo` for the angle of `x + i y` divided by π and the sign of `y`.
-/
theorem atan2Pi_roundsTo {mode : IEEERoundingMode} {y x : Model fmt}
    {qy qx : ℚ} (hy : toRat? y = some qy) (hx : toRat? x = some qx) (hne : qy ≠ 0) :
    RoundsTo fmt mode (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi) (decide (qy < 0))
      (atan2Pi y x mode).value := by
  obtain ⟨harg, hsign⟩ := arg_ne_zero_and_neg_iff qx hne
  have hturn : Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi < 0 ↔ qy < 0 := by
    rw [div_lt_iff₀ Real.pi_pos, zero_mul]
    exact hsign
  have h := binary_roundsTo (mode := mode) (angleRule true (Function.levels fmt)) hy hx
    (locates_atan2Pi _ _ _ hne) (div_ne_zero harg Real.pi_ne_zero)
    (angleHint_sound true _ _ qy qx) (angleHint_signed true _ _ qy qx)
  rwa [decide_eq_decide.mpr hturn] at h

/-- `atan2` and `atan2Pi` at finite operands with a nonzero `y` raise `overflow` exactly when
the rounding of the angle on the grid of the format with an unbounded exponent range exceeds
the largest finite value in magnitude, in every rounding direction and for every format
descriptor. -/
theorem atan2_overflow_iff {y x : Model fmt} {qy qx : ℚ} (hy : toRat? y = some qy)
    (hx : toRat? x = some qx) (hne : qy ≠ 0) (mode : IEEERoundingMode) :
    ((atan2 y x mode).status.overflow = true ↔
        toReal (posMaxFinite fmt) < |roundAt fmt (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩) mode|) ∧
      ((atan2Pi y x mode).status.overflow = true ↔
        toReal (posMaxFinite fmt) <
          |roundAt fmt (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi) mode|) := by
  obtain ⟨harg, -⟩ := arg_ne_zero_and_neg_iff qx hne
  exact ⟨binary_overflow_iff (angleRule false (Function.levels fmt)) hy hx
      (locates_atan2 _ _ _ hne) harg mode (angleHint_sound false _ _ qy qx)
      (angleHint_signed false _ _ qy qx),
    binary_overflow_iff (angleRule true (Function.levels fmt)) hy hx
      (locates_atan2Pi _ _ _ hne) (div_ne_zero harg Real.pi_ne_zero) mode
      (angleHint_sound true _ _ qy qx) (angleHint_signed true _ _ qy qx)⟩

/-- `atan2` and `atan2Pi` at finite operands with a nonzero `y` raise `underflow` exactly when
they raise `inexact` and the magnitude of the angle is tiny after rounding in the direction, in
every rounding direction and for every format descriptor. -/
theorem atan2_underflow_iff {y x : Model fmt} {qy qx : ℚ} (hy : toRat? y = some qy)
    (hx : toRat? x = some qx) (hne : qy ≠ 0) (mode : IEEERoundingMode) :
    ((atan2 y x mode).status.underflow = true ↔
       (atan2 y x mode).status.inexact = true ∧
         AlgebraicRounding.TinyAfterRounding fmt
           (mode.magnitudeRounding (decide (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ < 0)))
           |Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩|) ∧
      ((atan2Pi y x mode).status.underflow = true ↔
         (atan2Pi y x mode).status.inexact = true ∧
           AlgebraicRounding.TinyAfterRounding fmt
             (mode.magnitudeRounding (decide (Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi < 0)))
             |Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi|) := by
  obtain ⟨harg, -⟩ := arg_ne_zero_and_neg_iff qx hne
  exact ⟨binary_underflow_iff (angleRule false (Function.levels fmt)) hy hx
      (locates_atan2 _ _ _ hne) harg mode (angleHint_sound false _ _ qy qx)
      (angleHint_signed false _ _ qy qx),
    binary_underflow_iff (angleRule true (Function.levels fmt)) hy hx
      (locates_atan2Pi _ _ _ hne) (div_ne_zero harg Real.pi_ne_zero) mode
      (angleHint_sound true _ _ qy qx) (angleHint_signed true _ _ qy qx)⟩

/-- `atan2` at finite operands with a nonzero `y` raises `inexact` exactly when its finite
result is not the angle of `x + i y`, in every rounding direction and for every format
descriptor. -/
theorem atan2_inexact_iff {y x : Model fmt} {qy qx : ℚ} (hy : toRat? y = some qy)
    (hx : toRat? x = some qx) (hne : qy ≠ 0) (mode : IEEERoundingMode)
    (hfinite : isFinite (atan2 y x mode).value = true) :
    (atan2 y x mode).status.inexact = true ↔
      toReal (atan2 y x mode).value ≠ Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ := by
  unfold atan2 at hfinite ⊢
  rw [binary_of_toRat? _ hy hx] at hfinite ⊢
  exact Rule.deliver_inexact_iff (locates_atan2 _ _ _ hne) mode
    (angleHint_sound false _ _ qy qx) hfinite

/-- `atan2Pi` at finite operands with a nonzero `y` raises `inexact` exactly when its finite
result is not the angle of `x + i y` divided by π, in every rounding direction and for every
format descriptor. -/
theorem atan2Pi_inexact_iff {y x : Model fmt} {qy qx : ℚ} (hy : toRat? y = some qy)
    (hx : toRat? x = some qx) (hne : qy ≠ 0) (mode : IEEERoundingMode)
    (hfinite : isFinite (atan2Pi y x mode).value = true) :
    (atan2Pi y x mode).status.inexact = true ↔
      toReal (atan2Pi y x mode).value ≠ Complex.arg ⟨(qx : ℝ), (qy : ℝ)⟩ / Real.pi := by
  unfold atan2Pi at hfinite ⊢
  rw [binary_of_toRat? _ hy hx] at hfinite ⊢
  exact Rule.deliver_inexact_iff (locates_atan2Pi _ _ _ hne) mode
    (angleHint_sound true _ _ qy qx) hfinite

/-- `atan2` and `atan2Pi` at finite operands with a nonzero `y` raise neither `invalid` nor
`divideByZero`, in every rounding direction and for every format descriptor. -/
theorem atan2_invalid_divideByZero {y x : Model fmt} {qy qx : ℚ} (hy : toRat? y = some qy)
    (hx : toRat? x = some qx) (hne : qy ≠ 0) (mode : IEEERoundingMode) :
    ((atan2 y x mode).status.invalid = false ∧ (atan2 y x mode).status.divideByZero = false) ∧
      (atan2Pi y x mode).status.invalid = false ∧
        (atan2Pi y x mode).status.divideByZero = false :=
  ⟨binary_invalid_divideByZero (angleRule false (Function.levels fmt)) hy hx
      (locates_atan2 _ _ _ hne) mode _,
    binary_invalid_divideByZero (angleRule true (Function.levels fmt)) hy hx
      (locates_atan2Pi _ _ _ hne) mode _⟩

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded
