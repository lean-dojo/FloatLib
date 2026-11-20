/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Directed.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Comparison.Underflow
public import FloatLib.Floats.Formats.Posit.Algebraic.Root.Proof

/-!
# `rSqrt`, `hypot`, `rootn` and `pown` are correctly rounded in every direction

For every format descriptor (a conventional IEEE one, a format without an infinity such as OCP
E4M3, a format with one zero such as ONNX E4M3FNUZ, or a format in which every encoding is
finite), each rounding direction `mode` and finite operands in the domain, the four functions
of `Algebraic.Directed.Runtime` meet the contract `RoundsTo` for their real value: the result
is finite and denotes `roundAt fmt target mode` when that value is at most the largest finite
magnitude, it is the overflow result of the direction otherwise, and in a format with signed
zeros it has the sign of the real value.

* `rSqrt_roundsTo`: `(√q)⁻¹` for a positive operand.
* `hypot_roundsTo`: `√(p² + q²)` for operands that are not both zero.
* `rootn_roundsTo_of_pos`: `q ^ (1 / n)` for a positive operand and a nonzero degree, and
  `rootn_roundsTo_of_neg`: `-((-q) ^ (1 / n))` for a negative operand and an odd degree.
  `cbrt_roundsTo_of_pos` and `cbrt_roundsTo_of_neg` are the degree three.
* `pown_roundsTo`: `q ^ n` for a nonzero operand.

`rSqrt_inexact_iff`, `hypot_inexact_iff`, `rootn_inexact_iff_of_pos`,
`rootn_inexact_iff_of_neg` and `pown_inexact_iff` say that `inexact` is raised
exactly when the finite result is not the real value, for every descriptor.
`rSqrt_invalid_divideByZero`, `hypot_invalid_divideByZero`, `rootn_invalid_divideByZero_of_pos`,
`rootn_invalid_divideByZero_of_neg` and `pown_invalid_divideByZero` say that neither `invalid`
nor `divideByZero` is raised. `cbrt` is `rootn` of degree three, so the statements of `rootn`
are its own.
`rSqrt_overflow_iff`, `hypot_overflow_iff`, `rootn_overflow_iff_of_pos`,
`rootn_overflow_iff_of_neg` and `pown_overflow_iff` say that `overflow` is raised exactly when
the rounding of the real value with an unbounded exponent range exceeds the largest finite
value in magnitude. `rSqrt_underflow_iff`, `hypot_underflow_iff`, `rootn_underflow_iff_of_pos`,
`rootn_underflow_iff_of_neg` and `pown_underflow_iff` say that `underflow` is raised exactly
when `inexact` is raised and the magnitude of the real value is tiny after rounding in the
direction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Algebraic.Directed

open FloatLib.Numerics
open ComparisonRounding
open Posit.Model.RootRounding (compareRoot compareRoot_eq_real)

variable {fmt : FloatFormat}

/-- The mirrored comparator of a comparator of `t` orders `-t`. -/
theorem mirror_eq {compare : ℚ → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (candidate : ℚ) : mirror compare candidate = cmp (-target) (candidate : ℝ) :=
  magnitude_compare hcompare candidate

/-- The rule of `rSqrt` at a positive operand locates the reciprocal of the square root. -/
theorem locates_rSqrt (negative : Bool) {q : ℚ} (hpos : 0 < q) :
    (rSqrtRule (.finite negative q)).Locates (Real.sqrt q)⁻¹ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast hpos
  simp only [rSqrtRule, hpos.ne', ↓reduceIte, not_lt.mpr hpos.le]
  exact compareRoot_eq_real q⁻¹ 2 _ (inv_nonneg.mpr (Real.sqrt_nonneg _)) (by decide)
    (by rw [inv_pow, Real.sq_sqrt hq.le, Rat.cast_inv])

/-- The rule of `hypot` at operands that are not both zero locates the root of the sum of
squares. -/
theorem locates_hypot (left right : Bool) {p q : ℚ} (hne : p ≠ 0 ∨ q ≠ 0) :
    (hypotRule (.finite left p) (.finite right q)).Locates
      (Real.sqrt ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)) := by
  have hzero : ¬(p = 0 ∧ q = 0) := fun h => hne.elim (fun hp => hp h.1) (fun hq => hq h.2)
  simp only [hypotRule, hzero, ↓reduceIte]
  exact compareRoot_eq_real _ 2 _ (Real.sqrt_nonneg _) (by decide)
    (by rw [Real.sq_sqrt (by positivity)]; push_cast; ring)

/-- The real `degree`-th root of a positive number, to the power `|degree|`, is the number for
a positive degree and its reciprocal for a negative one. -/
theorem rpow_inv_pow_natAbs {t : ℝ} (ht : 0 < t) {degree : ℤ} (hdegree : degree ≠ 0) :
    (t ^ ((degree : ℝ)⁻¹)) ^ degree.natAbs = if degree < 0 then t⁻¹ else t := by
  have hnat : degree.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hdegree
  rcases lt_or_gt_of_ne hdegree with hneg | hpos
  · have hcast : (degree : ℝ) = -(degree.natAbs : ℝ) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hneg.le, Int.cast_neg]
      ring
    rw [ite_eq_left hneg, hcast, inv_neg, Real.rpow_neg ht.le, inv_pow,
      Real.rpow_inv_natCast_pow ht.le hnat]
  · have hcast : (degree : ℝ) = (degree.natAbs : ℝ) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos.le]
    rw [ite_eq_right (not_lt.mpr hpos.le), hcast, Real.rpow_inv_natCast_pow ht.le hnat]

/-- The rule of `rootn` at a positive operand and a nonzero degree locates the real root. -/
theorem locates_rootn_of_pos (negative : Bool) {q : ℚ} (hpos : 0 < q) {degree : ℤ}
    (hdegree : degree ≠ 0) :
    (rootnRule degree (.finite negative q)).Locates ((q : ℝ) ^ ((degree : ℝ)⁻¹)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast hpos
  simp only [rootnRule, hdegree, hpos.ne', ↓reduceIte, not_lt.mpr hpos.le]
  refine compareRoot_eq_real _ _ _ (Real.rpow_nonneg hq.le _)
    (Int.natAbs_ne_zero.mpr hdegree) ?_
  rw [rpow_inv_pow_natAbs hq hdegree]
  split_ifs <;> simp

/-- The rule of `rootn` at a negative operand and an odd degree locates the negative real
root. -/
theorem locates_rootn_of_neg (negative : Bool) {q : ℚ} (hneg : q < 0) {degree : ℤ}
    (hodd : degree % 2 ≠ 0) :
    (rootnRule degree (.finite negative q)).Locates (-((-q : ℝ) ^ ((degree : ℝ)⁻¹))) := by
  have hdegree : degree ≠ 0 := by
    rintro rfl
    exact hodd rfl
  have hq : (0 : ℝ) < -q := by exact_mod_cast neg_pos.mpr hneg
  simp only [rootnRule, hdegree, hneg.ne, ↓reduceIte, hneg, hodd]
  refine mirror_eq (compareRoot_eq_real _ _ _ (Real.rpow_nonneg hq.le _)
    (Int.natAbs_ne_zero.mpr hdegree) ?_)
  rw [rpow_inv_pow_natAbs hq hdegree]
  split_ifs <;> simp

/-- The rule of `pown` at a nonzero operand locates the integer power. -/
theorem locates_pown (negative : Bool) {q : ℚ} (hne : q ≠ 0) (exponent : ℤ) :
    (pownRule exponent (.finite negative q)).Locates ((q : ℝ) ^ exponent) := by
  by_cases hzero : exponent = 0
  · simp only [pownRule, hzero, ↓reduceIte, zpow_zero]
    exact_mod_cast Rule.locates_rational 1
  · simp only [pownRule, hzero, hne, ↓reduceIte]
    exact_mod_cast Rule.locates_rational (q ^ exponent)

/--
**`rSqrt` is correctly rounded in every direction.** For every format descriptor and each
rounding direction `mode` and a finite positive operand with the exact value `q`: the result is
finite and denotes `roundAt fmt (√q)⁻¹ mode` when that value is at most the largest finite
magnitude, it is the overflow result of the direction otherwise, and in a format with signed
zeros its sign bit is clear.
-/
theorem rSqrt_roundsTo {mode : IEEERoundingMode} {x : Model fmt}
    {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q) :
    RoundsTo fmt mode (Real.sqrt q)⁻¹ false (rSqrt x mode).value := by
  have htarget : 0 < (Real.sqrt (q : ℝ))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hpos))
  have h := unary_roundsTo (mode := mode) rSqrtRule hq (locates_rSqrt _ hpos) htarget.ne'
    (hint := fun _ _ => none) (Hint.sound_none _) (Hint.signed_none _)
  rwa [decide_eq_false (not_lt.mpr htarget.le)] at h

/-- For finite operands, `hypot` is the table of `hypotRule`. -/
theorem hypot_of_toRat? {x y : Model fmt} {p q : ℚ} (hx : toRat? x = some p)
    (hy : toRat? y = some q) (mode : IEEERoundingMode) :
    hypot x y mode =
      (hypotRule (.finite (signBit x) p) (.finite (signBit y) q)).deliver fmt mode := by
  have hfinite (z : Model fmt) (r : ℚ) (hz : toRat? z = some r) : isInfinite z = false :=
    isInfinite_eq_false_of_isFinite_eq_true z (isFinite_of_toRat?_eq_some hz)
  simp only [hypot, hfinite x p hx, hfinite y q hy, Bool.false_eq_true, or_self, false_and,
    ↓reduceIte]
  exact binary_of_toRat? hypotRule hx hy mode _

/--
**`hypot` is correctly rounded in every direction.** For every format descriptor and each
rounding direction `mode` and finite operands with the exact values `p` and `q` that are not
both zero: the result is finite and denotes `roundAt fmt √(p² + q²) mode` when that value is at
most the largest finite magnitude, it is the overflow result of the direction otherwise, and in
a format with signed zeros its sign bit is clear. The sum of squares is not rounded.
-/
theorem hypot_roundsTo {mode : IEEERoundingMode} {x y : Model fmt}
    {p q : ℚ} (hx : toRat? x = some p) (hy : toRat? y = some q) (hne : p ≠ 0 ∨ q ≠ 0) :
    RoundsTo fmt mode (Real.sqrt ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)) false (hypot x y mode).value := by
  have hsum : (0 : ℝ) < (p : ℝ) ^ 2 + (q : ℝ) ^ 2 := by
    rcases hne with hp | hq
    · have : (p : ℝ) ≠ 0 := by exact_mod_cast hp
      positivity
    · have : (q : ℝ) ≠ 0 := by exact_mod_cast hq
      positivity
  have htarget := Real.sqrt_pos.mpr hsum
  rw [hypot_of_toRat? hx hy]
  have h := Rule.deliver_roundsTo (fmt := fmt) (mode := mode)
    (locates_hypot (signBit x) (signBit y) hne) htarget.ne'
    (hint := fun _ => none) (Hint.sound_none _) (Hint.signed_none _)
  rwa [decide_eq_false (not_lt.mpr htarget.le)] at h

/--
**`rootn` of a positive operand is correctly rounded in every direction.** For every format
descriptor and each rounding direction `mode`, a finite positive operand with the exact value
`q` and a nonzero degree: the result is finite and denotes `roundAt fmt (q ^ (1 / degree))
mode` when that value is at most the largest finite magnitude, it is the overflow result of the
direction otherwise, and in a format with signed zeros its sign bit is clear.
-/
theorem rootn_roundsTo_of_pos {mode : IEEERoundingMode}
    {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) (hpos : 0 < q) {degree : ℤ} (hdegree : degree ≠ 0) :
    RoundsTo fmt mode ((q : ℝ) ^ ((degree : ℝ)⁻¹)) false (rootn x degree mode).value := by
  have htarget : 0 < (q : ℝ) ^ ((degree : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hpos) _
  have h := unary_roundsTo (mode := mode) (rootnRule degree) hq
    (locates_rootn_of_pos _ hpos hdegree)
    htarget.ne' (hint := fun _ _ => none) (Hint.sound_none _) (Hint.signed_none _)
  rwa [decide_eq_false (not_lt.mpr htarget.le)] at h

/--
**`rootn` of a negative operand and an odd degree is correctly rounded in every direction.**
For every format descriptor and each rounding direction `mode`, a finite negative operand with
the exact value `q` and an odd degree: the result is finite and denotes `roundAt fmt (-((-q) ^
(1 / degree))) mode` when that value is at most the largest finite magnitude, it is the
overflow result of the direction otherwise, and in a format with signed zeros its sign bit is
set.
-/
theorem rootn_roundsTo_of_neg {mode : IEEERoundingMode}
    {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) (hneg : q < 0) {degree : ℤ} (hodd : degree % 2 ≠ 0) :
    RoundsTo fmt mode (-((-q : ℝ) ^ ((degree : ℝ)⁻¹))) true (rootn x degree mode).value := by
  have hroot : 0 < (-q : ℝ) ^ ((degree : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by exact_mod_cast neg_pos.mpr hneg) _
  have h := unary_roundsTo (mode := mode) (rootnRule degree) hq
    (locates_rootn_of_neg _ hneg hodd)
    (neg_ne_zero.mpr hroot.ne') (hint := fun _ _ => none) (Hint.sound_none _)
    (Hint.signed_none _)
  rwa [decide_eq_true (neg_lt_zero.mpr hroot)] at h

/-- The cube root of a positive operand is correctly rounded in every direction. -/
theorem cbrt_roundsTo_of_pos {mode : IEEERoundingMode}
    {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q) :
    RoundsTo fmt mode ((q : ℝ) ^ ((3 : ℝ)⁻¹)) false (cbrt x mode).value := by
  simpa [cbrt] using rootn_roundsTo_of_pos hq hpos (degree := 3) (by decide)

/-- The cube root of a negative operand is correctly rounded in every direction. -/
theorem cbrt_roundsTo_of_neg {mode : IEEERoundingMode}
    {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hneg : q < 0) :
    RoundsTo fmt mode (-((-q : ℝ) ^ ((3 : ℝ)⁻¹))) true (cbrt x mode).value := by
  simpa [cbrt] using rootn_roundsTo_of_neg hq hneg (degree := 3) (by decide)

/-- For a finite operand, `pown` is the table of `pownRule`. -/
theorem pown_of_toRat? {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (exponent : ℤ)
    (mode : IEEERoundingMode) :
    pown x exponent mode = (pownRule exponent (.finite (signBit x) q)).deliver fmt mode := by
  unfold pown
  split_ifs with hzero
  · simp [pownRule, hzero.1]
  · exact unary_of_toRat? _ hq mode _

/--
**`pown` is correctly rounded in every direction.** For every format descriptor and each
rounding direction `mode`, a finite nonzero operand with the exact value `q` and every integer
exponent: the result is finite and denotes `roundAt fmt (q ^ exponent) mode` when that value is
at most the largest finite magnitude, it is the overflow result of the direction otherwise, and
in a format with signed zeros it has the sign of `q ^ exponent`.
-/
theorem pown_roundsTo {mode : IEEERoundingMode} {x : Model fmt}
    {q : ℚ} (hq : toRat? x = some q) (hne : q ≠ 0) (exponent : ℤ) :
    RoundsTo fmt mode ((q : ℝ) ^ exponent) (decide ((q : ℝ) ^ exponent < 0))
      (pown x exponent mode).value := by
  rw [pown_of_toRat? hq]
  exact Rule.deliver_roundsTo (locates_pown _ hne exponent)
    (zpow_ne_zero _ (by exact_mod_cast hne)) (Hint.sound_none _) (Hint.signed_none _)

/-- For a finite positive operand and every rounding direction, `rSqrt` raises `inexact`
exactly when its finite result is not `(√q)⁻¹`. -/
theorem rSqrt_inexact_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q)
    (mode : IEEERoundingMode) (hfinite : isFinite (rSqrt x mode).value = true) :
    (rSqrt x mode).status.inexact = true ↔ toReal (rSqrt x mode).value ≠ (Real.sqrt q)⁻¹ := by
  unfold rSqrt at hfinite ⊢
  rw [unary_of_toRat? _ hq] at hfinite ⊢
  exact Rule.deliver_inexact_iff (locates_rSqrt _ hpos) mode (Hint.sound_none _) hfinite

/-- For finite operands that are not both zero and every rounding direction, `hypot` raises
`inexact` exactly when its finite result is not `√(p² + q²)`. -/
theorem hypot_inexact_iff {x y : Model fmt} {p q : ℚ} (hx : toRat? x = some p)
    (hy : toRat? y = some q) (hne : p ≠ 0 ∨ q ≠ 0) (mode : IEEERoundingMode)
    (hfinite : isFinite (hypot x y mode).value = true) :
    (hypot x y mode).status.inexact = true ↔
      toReal (hypot x y mode).value ≠ Real.sqrt ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) := by
  rw [hypot_of_toRat? hx hy] at hfinite ⊢
  exact Rule.deliver_inexact_iff (locates_hypot _ _ hne) mode (Hint.sound_none _) hfinite

/-- For a finite nonzero operand and every rounding direction, `pown` raises `inexact` exactly
when its finite result is not `q ^ exponent`. -/
theorem pown_inexact_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hne : q ≠ 0)
    (exponent : ℤ) (mode : IEEERoundingMode)
    (hfinite : isFinite (pown x exponent mode).value = true) :
    (pown x exponent mode).status.inexact = true ↔
      toReal (pown x exponent mode).value ≠ (q : ℝ) ^ exponent := by
  rw [pown_of_toRat? hq] at hfinite ⊢
  exact Rule.deliver_inexact_iff (locates_pown _ hne exponent) mode (Hint.sound_none _) hfinite

/-- For a finite positive operand, a nonzero degree and every rounding direction, `rootn`
raises `inexact` exactly when its finite result is not `q ^ (1 / n)`. -/
theorem rootn_inexact_iff_of_pos {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (hpos : 0 < q) {degree : ℤ} (hdegree : degree ≠ 0) (mode : IEEERoundingMode)
    (hfinite : isFinite (rootn x degree mode).value = true) :
    (rootn x degree mode).status.inexact = true ↔
      toReal (rootn x degree mode).value ≠ (q : ℝ) ^ ((degree : ℝ)⁻¹) := by
  unfold rootn at hfinite ⊢
  rw [unary_of_toRat? _ hq] at hfinite ⊢
  exact Rule.deliver_inexact_iff (locates_rootn_of_pos _ hpos hdegree) mode (Hint.sound_none _)
    hfinite

/-- For a finite negative operand, an odd degree and every rounding direction, `rootn` raises
`inexact` exactly when its finite result is not `-((-q) ^ (1 / n))`. -/
theorem rootn_inexact_iff_of_neg {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (hneg : q < 0) {degree : ℤ} (hodd : degree % 2 ≠ 0) (mode : IEEERoundingMode)
    (hfinite : isFinite (rootn x degree mode).value = true) :
    (rootn x degree mode).status.inexact = true ↔
      toReal (rootn x degree mode).value ≠ -((-q : ℝ) ^ ((degree : ℝ)⁻¹)) := by
  unfold rootn at hfinite ⊢
  rw [unary_of_toRat? _ hq] at hfinite ⊢
  exact Rule.deliver_inexact_iff (locates_rootn_of_neg _ hneg hodd) mode (Hint.sound_none _)
    hfinite

/--
**`invalid` and `divideByZero` stay clear for `rSqrt`, `hypot`, `rootn` and `pown`.** For
finite operands in the domain, every rounding direction and every format descriptor, neither
flag is raised.
-/
theorem rSqrt_invalid_divideByZero {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (hpos : 0 < q) (mode : IEEERoundingMode) :
    (rSqrt x mode).status.invalid = false ∧ (rSqrt x mode).status.divideByZero = false :=
  unary_invalid_divideByZero rSqrtRule hq (locates_rSqrt _ hpos) mode _

@[inherit_doc rSqrt_invalid_divideByZero]
theorem hypot_invalid_divideByZero {x y : Model fmt} {p q : ℚ} (hx : toRat? x = some p)
    (hy : toRat? y = some q) (hne : p ≠ 0 ∨ q ≠ 0) (mode : IEEERoundingMode) :
    (hypot x y mode).status.invalid = false ∧ (hypot x y mode).status.divideByZero = false := by
  rw [hypot_of_toRat? hx hy]
  exact Rule.deliver_invalid_divideByZero (locates_hypot (signBit x) (signBit y) hne) mode _

@[inherit_doc rSqrt_invalid_divideByZero]
theorem rootn_invalid_divideByZero_of_pos {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (hpos : 0 < q) {degree : ℤ} (hdegree : degree ≠ 0) (mode : IEEERoundingMode) :
    (rootn x degree mode).status.invalid = false ∧
      (rootn x degree mode).status.divideByZero = false :=
  unary_invalid_divideByZero (rootnRule degree) hq (locates_rootn_of_pos _ hpos hdegree) mode _

@[inherit_doc rSqrt_invalid_divideByZero]
theorem rootn_invalid_divideByZero_of_neg {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (hneg : q < 0) {degree : ℤ} (hodd : degree % 2 ≠ 0) (mode : IEEERoundingMode) :
    (rootn x degree mode).status.invalid = false ∧
      (rootn x degree mode).status.divideByZero = false :=
  unary_invalid_divideByZero (rootnRule degree) hq (locates_rootn_of_neg _ hneg hodd) mode _

@[inherit_doc rSqrt_invalid_divideByZero]
theorem pown_invalid_divideByZero {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (hne : q ≠ 0) (exponent : ℤ) (mode : IEEERoundingMode) :
    (pown x exponent mode).status.invalid = false ∧
      (pown x exponent mode).status.divideByZero = false := by
  rw [pown_of_toRat? hq]
  exact Rule.deliver_invalid_divideByZero (locates_pown _ hne exponent) mode _

/--
**`overflow` is the overflow of the standard for `rSqrt`, `hypot`, `rootn` and `pown`.** For
finite operands in the domain, every rounding direction and every format descriptor, `overflow`
is raised exactly when the rounding of the real value on the grid of the format with an
unbounded exponent range exceeds the largest finite value in magnitude (IEEE 754-2019 §7.4).
-/
theorem rSqrt_overflow_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q)
    (mode : IEEERoundingMode) :
    (rSqrt x mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt (Real.sqrt q)⁻¹ mode| :=
  unary_overflow_iff rSqrtRule hq (locates_rSqrt _ hpos)
    (inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hpos))).ne' mode
    (hint := fun _ _ => none) (Hint.sound_none _) (Hint.signed_none _)

/--
**`underflow` is the underflow of the standard for `rSqrt`, `hypot`, `rootn` and `pown`.** For
finite operands in the domain, every rounding direction and every format descriptor,
`underflow` is raised exactly when `inexact` is raised and the magnitude of the real value is
tiny after rounding: its rounding to the precision of the format with an unbounded exponent
range is below the least normal magnitude (IEEE 754-2019 §7.5).
-/
theorem rSqrt_underflow_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q)
    (mode : IEEERoundingMode) :
    (rSqrt x mode).status.underflow = true ↔
      (rSqrt x mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide ((Real.sqrt q)⁻¹ < 0))) |(Real.sqrt q)⁻¹| :=
  unary_underflow_iff rSqrtRule hq (locates_rSqrt _ hpos)
    (inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hpos))).ne' mode
    (hint := fun _ _ => none) (Hint.sound_none _) (Hint.signed_none _)

@[inherit_doc rSqrt_overflow_iff]
theorem hypot_overflow_iff {x y : Model fmt} {p q : ℚ} (hx : toRat? x = some p)
    (hy : toRat? y = some q) (hne : p ≠ 0 ∨ q ≠ 0) (mode : IEEERoundingMode) :
    (hypot x y mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) <
        |roundAt fmt (Real.sqrt ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)) mode| := by
  have hsum : (0 : ℝ) < (p : ℝ) ^ 2 + (q : ℝ) ^ 2 := by
    rcases hne with hp | hq
    · have : (p : ℝ) ≠ 0 := by exact_mod_cast hp
      positivity
    · have : (q : ℝ) ≠ 0 := by exact_mod_cast hq
      positivity
  rw [hypot_of_toRat? hx hy]
  exact Rule.deliver_overflow_iff (locates_hypot (signBit x) (signBit y) hne)
    (Real.sqrt_pos.mpr hsum).ne' mode (hint := fun _ => none) (Hint.sound_none _)
    (Hint.signed_none _)

@[inherit_doc rSqrt_underflow_iff]
theorem hypot_underflow_iff {x y : Model fmt} {p q : ℚ} (hx : toRat? x = some p)
    (hy : toRat? y = some q) (hne : p ≠ 0 ∨ q ≠ 0) (mode : IEEERoundingMode) :
    (hypot x y mode).status.underflow = true ↔
      (hypot x y mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide (Real.sqrt ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) < 0)))
          |Real.sqrt ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)| := by
  have hsum : (0 : ℝ) < (p : ℝ) ^ 2 + (q : ℝ) ^ 2 := by
    rcases hne with hp | hq
    · have : (p : ℝ) ≠ 0 := by exact_mod_cast hp
      positivity
    · have : (q : ℝ) ≠ 0 := by exact_mod_cast hq
      positivity
  rw [hypot_of_toRat? hx hy]
  exact Rule.deliver_underflow_iff (locates_hypot (signBit x) (signBit y) hne)
    (Real.sqrt_pos.mpr hsum).ne' mode (hint := fun _ => none) (Hint.sound_none _)
    (Hint.signed_none _)

@[inherit_doc rSqrt_overflow_iff]
theorem rootn_overflow_iff_of_pos {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (hpos : 0 < q) {degree : ℤ} (hdegree : degree ≠ 0) (mode : IEEERoundingMode) :
    (rootn x degree mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt ((q : ℝ) ^ ((degree : ℝ)⁻¹)) mode| :=
  unary_overflow_iff (rootnRule degree) hq (locates_rootn_of_pos _ hpos hdegree)
    (Real.rpow_pos_of_pos (by exact_mod_cast hpos) _).ne' mode (hint := fun _ _ => none)
    (Hint.sound_none _) (Hint.signed_none _)

@[inherit_doc rSqrt_underflow_iff]
theorem rootn_underflow_iff_of_pos {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (hpos : 0 < q) {degree : ℤ} (hdegree : degree ≠ 0) (mode : IEEERoundingMode) :
    (rootn x degree mode).status.underflow = true ↔
      (rootn x degree mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide ((q : ℝ) ^ ((degree : ℝ)⁻¹) < 0)))
          |(q : ℝ) ^ ((degree : ℝ)⁻¹)| :=
  unary_underflow_iff (rootnRule degree) hq (locates_rootn_of_pos _ hpos hdegree)
    (Real.rpow_pos_of_pos (by exact_mod_cast hpos) _).ne' mode (hint := fun _ _ => none)
    (Hint.sound_none _) (Hint.signed_none _)

@[inherit_doc rSqrt_overflow_iff]
theorem rootn_overflow_iff_of_neg {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (hneg : q < 0) {degree : ℤ} (hodd : degree % 2 ≠ 0) (mode : IEEERoundingMode) :
    (rootn x degree mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt (-((-q : ℝ) ^ ((degree : ℝ)⁻¹))) mode| :=
  unary_overflow_iff (rootnRule degree) hq (locates_rootn_of_neg _ hneg hodd)
    (neg_ne_zero.mpr (Real.rpow_pos_of_pos (by exact_mod_cast neg_pos.mpr hneg) _).ne') mode
    (hint := fun _ _ => none) (Hint.sound_none _) (Hint.signed_none _)

@[inherit_doc rSqrt_underflow_iff]
theorem rootn_underflow_iff_of_neg {x : Model fmt} {q : ℚ} (hq : toRat? x = some q)
    (hneg : q < 0) {degree : ℤ} (hodd : degree % 2 ≠ 0) (mode : IEEERoundingMode) :
    (rootn x degree mode).status.underflow = true ↔
      (rootn x degree mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide (-((-q : ℝ) ^ ((degree : ℝ)⁻¹)) < 0)))
          |-((-q : ℝ) ^ ((degree : ℝ)⁻¹))| :=
  unary_underflow_iff (rootnRule degree) hq (locates_rootn_of_neg _ hneg hodd)
    (neg_ne_zero.mpr (Real.rpow_pos_of_pos (by exact_mod_cast neg_pos.mpr hneg) _).ne') mode
    (hint := fun _ _ => none) (Hint.sound_none _) (Hint.signed_none _)

@[inherit_doc rSqrt_overflow_iff]
theorem pown_overflow_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hne : q ≠ 0)
    (exponent : ℤ) (mode : IEEERoundingMode) :
    (pown x exponent mode).status.overflow = true ↔
      toReal (posMaxFinite fmt) < |roundAt fmt ((q : ℝ) ^ exponent) mode| := by
  rw [pown_of_toRat? hq]
  exact Rule.deliver_overflow_iff (locates_pown _ hne exponent)
    (zpow_ne_zero _ (by exact_mod_cast hne)) mode (Hint.sound_none _) (Hint.signed_none _)

@[inherit_doc rSqrt_underflow_iff]
theorem pown_underflow_iff {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hne : q ≠ 0)
    (exponent : ℤ) (mode : IEEERoundingMode) :
    (pown x exponent mode).status.underflow = true ↔
      (pown x exponent mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide ((q : ℝ) ^ exponent < 0))) |(q : ℝ) ^ exponent| := by
  rw [pown_of_toRat? hq]
  exact Rule.deliver_underflow_iff (locates_pown _ hne exponent)
    (zpow_ne_zero _ (by exact_mod_cast hne)) mode (Hint.sound_none _) (Hint.signed_none _)

end FloatLib.Floats.Formats.BinaryInterchange.Model.Algebraic.Directed
