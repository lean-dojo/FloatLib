/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Directed.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Recommended.Proof
public import FloatLib.Numerics.Exact.Elementary.Proof

/-!
# `exp`, `expm1`, `log` and `logp1` are correctly rounded in every direction

For every format descriptor (a conventional IEEE one, a format without an infinity such as OCP
E4M3, a format with one zero such as ONNX E4M3FNUZ, or a format in which every encoding is
finite), each rounding direction and a finite operand in the domain, `Directed.exp`, `expm1`,
`log` and `logp1` meet the contract `RoundsTo` for the real function at the operand's exact
value (`exp_roundsTo`, `expm1_roundsTo`, `log_roundsTo`, `logp1_roundsTo`): the result is
finite and denotes `roundAt fmt` of the real value in that direction when that is at most the
largest finite magnitude, it is the overflow result of the direction otherwise, and in a format
with signed zeros it has the sign of the real value. `expm1` and `logp1` of a nonzero operand
and `log` of an operand other than 1 are not zero; at those operands the result is the exact
zero that the rule states.

`locates_exp`, `locates_expm1` and `locates_log` say that the rules, which decimal formats
apply too, locate the real functions, and `expHint_sound`, `logHint_sound` and their `signed`
forms that the enclosure search is right about them. `inexact` is raised exactly when the
finite result is not the real value, in every direction (`exp_inexact_iff` and its siblings),
`overflow` exactly when the rounding of the real value with an unbounded exponent range
exceeds the largest finite value in magnitude (`exp_overflow_iff` and its siblings), and
`underflow` exactly when `inexact` is raised and the magnitude of the real value is tiny after
rounding in the direction (`exp_underflow_iff` and its siblings). `invalid` and `divideByZero`
stay clear (`exp_invalid_divideByZero` and its siblings).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Directed

open FloatLib.Numerics
open ComparisonRounding
open CorrectlyRounded (nearest?_sound nearest?_signed)

variable {fmt : FloatFormat}

/-- The rule of `exp` at a finite operand locates the exponential. -/
theorem locates_exp (levels : Nat) (negative : Bool) (q : ℚ) :
    (expRule levels (.finite negative q)).Locates (Real.exp q) :=
  fun candidate => ElementaryComparison.prepareExp_eq_real q levels candidate

/-- The rule of `expm1` at a finite operand locates `exp q - 1`. -/
theorem locates_expm1 (levels : Nat) (negative : Bool) (q : ℚ) :
    (expm1Rule levels (.finite negative q)).Locates (Real.exp q - 1) := by
  refine Rule.locates_oddAt ?_ ?_
  · rintro rfl
    simp
  · intro _ candidate
    rw [ElementaryComparison.prepareExp_eq_real, cmp_sub_eq_cmp_add]
    push_cast
    rfl

/-- In its domain the rule of the logarithm of `x + offset`, for the offsets zero and one,
locates the logarithm. -/
theorem locates_log {offset : ℚ} (hoffset : offset = 0 ∨ offset = 1) (levels : Nat)
    (negative : Bool) {q : ℚ} (hq : 0 < q + offset) :
    (logRule levels offset (.finite negative q)).Locates (Real.log ((q : ℝ) + (offset : ℝ))) := by
  change (if offset ≠ 0 ∧ q = 0 then Rule.zero negative
    else if hpositive : 0 < q + offset then
      Rule.real (ElementaryComparison.prepareLog (q + offset) levels hpositive).compare
    else if q + offset = 0 then Rule.pole true else Rule.invalid).Locates _
  by_cases h : offset ≠ 0 ∧ q = 0
  · simp only [h]
    obtain ⟨hne, rfl⟩ := h
    rcases hoffset with rfl | rfl
    · exact absurd rfl hne
    · change Real.log _ = 0
      simp
  · simp only [h, hq, ↓reduceIte, ↓reduceDIte]
    intro candidate
    simpa using ElementaryComparison.prepareLog_eq_real (q + offset) levels hq candidate

/-- The expression of `exp` or `expm1` denotes the function. -/
theorem eval_expExpr (minusOne : Bool) (q : ℚ) (env : Nat → ℝ) :
    (expExpr minusOne q).eval env = if minusOne then Real.exp q - 1 else Real.exp q := by
  cases minusOne <;>
    simp [expExpr, Interval.Expr.eval, Interval.UnaryOp.eval, Interval.BinaryOp.eval]

/-- The hint of `exp` or `expm1` is right about the function. -/
theorem expHint_sound (minusOne negative : Bool) (q : ℚ) :
    Hint.Sound (expHint fmt minusOne (.finite negative q))
      (if minusOne then Real.exp q - 1 else Real.exp q) := by
  intro found h
  simp only [expHint] at h
  split_ifs at h
  exact nearest?_sound (eval_expExpr minusOne q _) _ found h

/-- The hint of `exp` or `expm1` has the sign of the function. -/
theorem expHint_signed (minusOne negative : Bool) (q : ℚ) :
    Hint.Signed (expHint fmt minusOne (.finite negative q))
      (if minusOne then Real.exp q - 1 else Real.exp q) := by
  intro found h
  simp only [expHint] at h
  split_ifs at h
  exact nearest?_signed (eval_expExpr minusOne q _) _ found h

/-- The expression of a logarithm denotes it. -/
private theorem eval_logExpr (q offset : ℚ) (env : Nat → ℝ) :
    (Interval.Expr.unary .log (.const (q + offset))).eval env =
      Real.log ((q : ℝ) + (offset : ℝ)) := by
  simp [Interval.Expr.eval, Interval.UnaryOp.eval]

/-- The hint of the logarithm of `x + offset` is right about it. -/
theorem logHint_sound (offset : ℚ) (negative : Bool) (q : ℚ) :
    Hint.Sound (logHint fmt offset (.finite negative q))
      (Real.log ((q : ℝ) + (offset : ℝ))) := by
  intro found h
  simp only [logHint] at h
  split_ifs at h
  exact nearest?_sound (eval_logExpr q offset _) true found h

/-- The hint of the logarithm of `x + offset` has its sign. -/
theorem logHint_signed (offset : ℚ) (negative : Bool) (q : ℚ) :
    Hint.Signed (logHint fmt offset (.finite negative q))
      (Real.log ((q : ℝ) + (offset : ℝ))) := by
  intro found h
  simp only [logHint] at h
  split_ifs at h
  exact nearest?_signed (eval_logExpr q offset _) true found h

/--
**`exp` is correctly rounded in every direction.** For every format descriptor, each rounding
direction `mode` and a finite operand with the exact value `q`: the result is finite and
denotes `roundAt fmt (exp q) mode` when that value is at most the largest finite magnitude, it
is the overflow result of the direction otherwise, and in a format with signed zeros its sign
bit is clear.
-/
theorem exp_roundsTo {mode : IEEERoundingMode} {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) :
    RoundsTo fmt mode (Real.exp q) false (exp x mode).value := by
  have hpos := Real.exp_pos (q : ℝ)
  have h := unary_roundsTo (mode := mode) (expRule (CorrectlyRounded.Function.levels fmt)) hq
    (locates_exp _ _ q) hpos.ne' (expHint_sound false _ q) (expHint_signed false _ q)
  rwa [decide_eq_false (not_lt.mpr hpos.le)] at h

/--
**`expm1` is correctly rounded in every direction.** For every format descriptor and each
rounding direction `mode` and a finite nonzero operand with the exact value `q`, the result
meets the contract `RoundsTo` for `exp q - 1` and the sign of that value.
-/
theorem expm1_roundsTo {mode : IEEERoundingMode} {x : Model fmt}
    {q : ℚ} (hq : toRat? x = some q) (hne : q ≠ 0) :
    RoundsTo fmt mode (Real.exp q - 1) (decide (Real.exp q - 1 < 0)) (expm1 x mode).value := by
  have hvalue : Real.exp (q : ℝ) - 1 ≠ 0 := by
    intro h
    exact hne (by exact_mod_cast (Real.exp_eq_one_iff _).mp (sub_eq_zero.mp h))
  exact unary_roundsTo (expm1Rule (CorrectlyRounded.Function.levels fmt)) hq
    (locates_expm1 _ _ q) hvalue (expHint_sound true _ q) (expHint_signed true _ q)

/--
**`log` is correctly rounded in every direction.** For every format descriptor and each
rounding direction `mode` and a finite positive operand with the exact value `q` other than 1,
the result meets the contract `RoundsTo` for `log q` and the sign of that value.
-/
theorem log_roundsTo {mode : IEEERoundingMode} {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) (hpos : 0 < q) (hne : q ≠ 1) :
    RoundsTo fmt mode (Real.log q) (decide (Real.log q < 0)) (log x mode).value := by
  have hreal : (0 : ℝ) < q := by exact_mod_cast hpos
  have hvalue : Real.log (q : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hreal (by exact_mod_cast hne)
  have h := unary_roundsTo (mode := mode) (logRule (CorrectlyRounded.Function.levels fmt) 0) hq
    (locates_log (offset := 0) (.inl rfl) _ _ (by simpa using hpos))
    (by simpa using hvalue) (logHint_sound 0 _ q) (logHint_signed 0 _ q)
  simp only [Rat.cast_zero, add_zero] at h
  exact h

/--
**`logp1` is correctly rounded in every direction.** For every format descriptor and each
rounding direction `mode` and a finite nonzero operand above -1 with the exact value `q`, the
result meets the contract `RoundsTo` for `log (1 + q)` and the sign of that value.
-/
theorem logp1_roundsTo {mode : IEEERoundingMode} {x : Model fmt}
    {q : ℚ} (hq : toRat? x = some q) (hdomain : -1 < q) (hne : q ≠ 0) :
    RoundsTo fmt mode (Real.log ((q : ℝ) + 1)) (decide (Real.log ((q : ℝ) + 1) < 0))
      (logp1 x mode).value := by
  have hreal : (0 : ℝ) < (q : ℝ) + 1 := by
    have : (-1 : ℝ) < q := by exact_mod_cast hdomain
    linarith
  have hvalue : Real.log ((q : ℝ) + 1) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hreal fun h =>
      hne (by exact_mod_cast (by linarith : (q : ℝ) = 0))
  have h := unary_roundsTo (mode := mode) (logRule (CorrectlyRounded.Function.levels fmt) 1) hq
    (locates_log (offset := 1) (.inr rfl) _ _ (by linarith))
    (by simpa using hvalue) (logHint_sound 1 _ q) (logHint_signed 1 _ q)
  simp only [Rat.cast_one] at h
  exact h

/--
**`inexact` means that `exp` is not the real value.** For a finite operand and every rounding
direction, `exp` raises `inexact` exactly when its finite result is not `exp q`.
-/
theorem exp_inexact_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (mode : IEEERoundingMode) (hfinite : isFinite (exp x mode).value = true) :
    (exp x mode).status.inexact = true ↔ toReal (exp x mode).value ≠ Real.exp q := by
  unfold exp at hfinite ⊢
  rw [unary_of_toRat? _ hq] at hfinite ⊢
  exact Rule.deliver_inexact_iff (locates_exp _ _ q) mode (expHint_sound false _ q) hfinite

/-- For a finite operand and every rounding direction, `expm1` raises `inexact` exactly when
its finite result is not `exp q - 1`. -/
theorem expm1_inexact_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (mode : IEEERoundingMode) (hfinite : isFinite (expm1 x mode).value = true) :
    (expm1 x mode).status.inexact = true ↔ toReal (expm1 x mode).value ≠ Real.exp q - 1 := by
  unfold expm1 at hfinite ⊢
  rw [unary_of_toRat? _ hq] at hfinite ⊢
  exact Rule.deliver_inexact_iff (locates_expm1 _ _ q) mode (expHint_sound true _ q) hfinite

/-- For a finite positive operand and every rounding direction, `log` raises `inexact` exactly
when its finite result is not `log q`. -/
theorem log_inexact_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q)
    (mode : IEEERoundingMode) (hfinite : isFinite (log x mode).value = true) :
    (log x mode).status.inexact = true ↔ toReal (log x mode).value ≠ Real.log q := by
  unfold log at hfinite ⊢
  rw [unary_of_toRat? _ hq] at hfinite ⊢
  have hlocates := locates_log (offset := 0) (.inl rfl) (CorrectlyRounded.Function.levels fmt)
    (signBit x) (q := q) (by simpa using hpos)
  have hsound := logHint_sound (fmt := fmt) 0 (signBit x) q
  simp only [Rat.cast_zero, add_zero] at hlocates hsound
  exact Rule.deliver_inexact_iff hlocates mode hsound hfinite

/-- For a finite operand above -1 and every rounding direction, `logp1` raises `inexact`
exactly when its finite result is not `log (1 + q)`. -/
theorem logp1_inexact_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hdomain : -1 < q)
    (mode : IEEERoundingMode) (hfinite : isFinite (logp1 x mode).value = true) :
    (logp1 x mode).status.inexact = true ↔
      toReal (logp1 x mode).value ≠ Real.log ((q : ℝ) + 1) := by
  unfold logp1 at hfinite ⊢
  rw [unary_of_toRat? _ hq] at hfinite ⊢
  have hlocates := locates_log (offset := 1) (.inr rfl) (CorrectlyRounded.Function.levels fmt)
    (signBit x) (q := q) (by linarith)
  have hsound := logHint_sound (fmt := fmt) 1 (signBit x) q
  simp only [Rat.cast_one] at hlocates hsound
  exact Rule.deliver_inexact_iff hlocates mode hsound hfinite

/--
**`overflow` is the overflow of the standard for `exp` and `expm1`.** For a finite operand
(nonzero for `expm1`), every rounding direction and every format descriptor, `overflow` is
raised exactly when the rounding of the real value on the grid of the format with an unbounded
exponent range exceeds the largest finite value in magnitude (IEEE 754-2019 §7.4).
-/
theorem exp_overflow_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (mode : IEEERoundingMode) :
    (exp x mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt (Real.exp q) mode| :=
  unary_overflow_iff (expRule (CorrectlyRounded.Function.levels fmt)) hq (locates_exp _ _ q)
    (Real.exp_pos (q : ℝ)).ne' mode (expHint_sound false _ q) (expHint_signed false _ q)

/--
**`underflow` is the underflow of the standard for `exp` and `expm1`.** For a finite operand
(nonzero for `expm1`), every rounding direction and every format descriptor, `underflow` is
raised exactly when `inexact` is raised and the magnitude of the real value is tiny after
rounding: its rounding to the precision of the format with an unbounded exponent range is below
the least normal magnitude (IEEE 754-2019 §7.5).
-/
theorem exp_underflow_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (mode : IEEERoundingMode) :
    (exp x mode).status.underflow = true ↔
      (exp x mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide (Real.exp q < 0))) |Real.exp q| :=
  unary_underflow_iff (expRule (CorrectlyRounded.Function.levels fmt)) hq (locates_exp _ _ q)
    (Real.exp_pos (q : ℝ)).ne' mode (expHint_sound false _ q) (expHint_signed false _ q)

@[inherit_doc exp_overflow_iff]
theorem expm1_overflow_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hne : q ≠ 0)
    (mode : IEEERoundingMode) :
    (expm1 x mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt (Real.exp q - 1) mode| := by
  have hvalue : Real.exp (q : ℝ) - 1 ≠ 0 := by
    intro h
    exact hne (by exact_mod_cast (Real.exp_eq_one_iff _).mp (sub_eq_zero.mp h))
  exact unary_overflow_iff (expm1Rule (CorrectlyRounded.Function.levels fmt)) hq
    (locates_expm1 _ _ q) hvalue mode (expHint_sound true _ q) (expHint_signed true _ q)

@[inherit_doc exp_underflow_iff]
theorem expm1_underflow_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hne : q ≠ 0)
    (mode : IEEERoundingMode) :
    (expm1 x mode).status.underflow = true ↔
      (expm1 x mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide (Real.exp q - 1 < 0))) |Real.exp q - 1| := by
  have hvalue : Real.exp (q : ℝ) - 1 ≠ 0 := by
    intro h
    exact hne (by exact_mod_cast (Real.exp_eq_one_iff _).mp (sub_eq_zero.mp h))
  exact unary_underflow_iff (expm1Rule (CorrectlyRounded.Function.levels fmt)) hq
    (locates_expm1 _ _ q) hvalue mode (expHint_sound true _ q) (expHint_signed true _ q)

/-- The logarithm of `q + offset` is not zero where `q + offset` is positive and other than
one. -/
private theorem log_add_ne_zero {q offset : ℚ} (hpos : 0 < q + offset) (hne : q + offset ≠ 1) :
    Real.log ((q : ℝ) + (offset : ℝ)) ≠ 0 :=
  Real.log_ne_zero_of_pos_of_ne_one (by exact_mod_cast hpos) (by exact_mod_cast hne)

/-- `log` at a finite positive operand other than 1 raises `overflow` exactly when the rounding
of `log q` on the grid of the format with an unbounded exponent range exceeds the largest
finite value in magnitude, in every rounding direction and for every format descriptor. -/
theorem log_overflow_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q)
    (hne : q ≠ 1) (mode : IEEERoundingMode) :
    (log x mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt (Real.log q) mode| := by
  have h := unary_overflow_iff (logRule (CorrectlyRounded.Function.levels fmt) 0) hq
    (locates_log (offset := 0) (.inl rfl) _ _ (by simpa using hpos))
    (log_add_ne_zero (by simpa using hpos) (by simpa using hne)) mode
    (logHint_sound 0 _ q) (logHint_signed 0 _ q)
  simp only [Rat.cast_zero, add_zero] at h
  exact h

/-- `log` at a finite positive operand other than 1 raises `underflow` exactly when it raises
`inexact` and the magnitude of `log q` is tiny after rounding in the direction, in every
rounding direction and for every format descriptor. -/
theorem log_underflow_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q)
    (hne : q ≠ 1) (mode : IEEERoundingMode) :
    (log x mode).status.underflow = true ↔
      (log x mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide (Real.log q < 0))) |Real.log q| := by
  have h := unary_underflow_iff (logRule (CorrectlyRounded.Function.levels fmt) 0) hq
    (locates_log (offset := 0) (.inl rfl) _ _ (by simpa using hpos))
    (log_add_ne_zero (by simpa using hpos) (by simpa using hne)) mode
    (logHint_sound 0 _ q) (logHint_signed 0 _ q)
  simp only [Rat.cast_zero, add_zero] at h
  exact h

/-- `logp1` at a finite nonzero operand above -1 raises `overflow` exactly when the rounding of
`log (1 + q)` on the grid of the format with an unbounded exponent range exceeds the largest
finite value in magnitude, in every rounding direction and for every format descriptor. -/
theorem logp1_overflow_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hdomain : -1 < q)
    (hne : q ≠ 0) (mode : IEEERoundingMode) :
    (logp1 x mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt (Real.log ((q : ℝ) + 1)) mode| := by
  have h := unary_overflow_iff (logRule (CorrectlyRounded.Function.levels fmt) 1) hq
    (locates_log (offset := 1) (.inr rfl) _ _ (by linarith))
    (log_add_ne_zero (by linarith) fun h => hne (by linarith)) mode
    (logHint_sound 1 _ q) (logHint_signed 1 _ q)
  simp only [Rat.cast_one] at h
  exact h

/-- `logp1` at a finite nonzero operand above -1 raises `underflow` exactly when it raises
`inexact` and the magnitude of `log (1 + q)` is tiny after rounding in the direction, in every
rounding direction and for every format descriptor. -/
theorem logp1_underflow_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hdomain : -1 < q)
    (hne : q ≠ 0) (mode : IEEERoundingMode) :
    (logp1 x mode).status.underflow = true ↔
      (logp1 x mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide (Real.log ((q : ℝ) + 1) < 0)))
          |Real.log ((q : ℝ) + 1)| := by
  have h := unary_underflow_iff (logRule (CorrectlyRounded.Function.levels fmt) 1) hq
    (locates_log (offset := 1) (.inr rfl) _ _ (by linarith))
    (log_add_ne_zero (by linarith) fun h => hne (by linarith)) mode
    (logHint_sound 1 _ q) (logHint_signed 1 _ q)
  simp only [Rat.cast_one] at h
  exact h

/--
**`invalid` and `divideByZero` stay clear for `exp`, `expm1`, `log` and `logp1`.** For a finite
operand in the domain, every rounding direction and every format descriptor, neither flag is
raised.
-/
theorem exp_invalid_divideByZero {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (mode : IEEERoundingMode) :
    (exp x mode).status.invalid = false ∧ (exp x mode).status.divideByZero = false :=
  unary_invalid_divideByZero (expRule (CorrectlyRounded.Function.levels fmt)) hq
    (locates_exp _ _ q) mode _

@[inherit_doc exp_invalid_divideByZero]
theorem expm1_invalid_divideByZero {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (mode : IEEERoundingMode) :
    (expm1 x mode).status.invalid = false ∧ (expm1 x mode).status.divideByZero = false :=
  unary_invalid_divideByZero (expm1Rule (CorrectlyRounded.Function.levels fmt)) hq
    (locates_expm1 _ _ q) mode _

@[inherit_doc exp_invalid_divideByZero]
theorem log_invalid_divideByZero {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (hpos : 0 < q) (mode : IEEERoundingMode) :
    (log x mode).status.invalid = false ∧ (log x mode).status.divideByZero = false :=
  unary_invalid_divideByZero (logRule (CorrectlyRounded.Function.levels fmt) 0) hq
    (locates_log (offset := 0) (.inl rfl) _ _ (by simpa using hpos)) mode _

@[inherit_doc exp_invalid_divideByZero]
theorem logp1_invalid_divideByZero {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (hdomain : -1 < q) (mode : IEEERoundingMode) :
    (logp1 x mode).status.invalid = false ∧ (logp1 x mode).status.divideByZero = false :=
  unary_invalid_divideByZero (logRule (CorrectlyRounded.Function.levels fmt) 1) hq
    (locates_log (offset := 1) (.inr rfl) _ _ (by linarith)) mode _

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Directed
