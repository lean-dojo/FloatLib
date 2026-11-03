/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Finiteness
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof

/-!
# Correctness of IEEE binary arithmetic

The executable operations in `Model` first decode finite operands to exact dyadics, perform
integer arithmetic, and round once in the destination format. This module proves the corresponding
real-number statements uniformly in the exponent and fraction widths for descriptors satisfying
`fmt.isIEEE = true`.

The result-finiteness hypotheses exclude IEEE overflow to infinity. NaNs and infinities are covered
by the executable special-value rules, but they do not have values in this real-number semantics.
A finite sum, product, or fused multiply-add has finite operands
(`isFinite_of_isFinite_add` and its siblings), so the rounding theorems assume only that the
executable result is finite. A sum with a zero, or a product with a zero or with a value of
magnitude one, does not round (`toReal_add_of_isZero_left` and its siblings). The same cases are
stated by decoded value with `toRat?` (`toRat?_add_of_toRat?_eq_some_zero_left` and its
siblings), and a sum or product whose exact value is the decoded value of some encoding decodes
to that value (`toRat?_add_of_representable`, `toRat?_mul_of_representable`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats

/--
On finite operands, nearest-even addition is one `roundDyadic` of an exact dyadic whose real value
is the exact sum.
-/
private theorem add_eq_roundDyadic_of_isFinite {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    ∃ exact : Numerics.Dyadic, add x y = roundDyadic fmt exact ∧
      exact.toReal = toReal x + toReal y := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  refine ⟨addDyadic dx dy, by simp [Proof.add_eq_spec, Spec.add, hdx, hdy], ?_⟩
  rw [Dyadic.toReal_addDyadic]
  simp [toReal_eq, hdx, hdy]

/--
Under a conventional IEEE descriptor a result that is one nearest-even rounding of an exact value
`r` is finite once `|r|` is within the largest finite magnitude.
-/
private theorem isFinite_of_eq_roundDyadic {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {result : Model fmt} {r : ℝ}
    (h : ∃ exact : Numerics.Dyadic, result = roundDyadic fmt exact ∧ exact.toReal = r)
    (hbound : |r| ≤ toReal (posMaxFinite fmt)) : isFinite result = true := by
  obtain ⟨exact, rfl, rfl⟩ := h
  exact isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite fmt hfmt exact hbound

/--
Under a conventional IEEE descriptor a finite result that is one nearest-even rounding of an exact
value `r` denotes `roundAt r`.
-/
private theorem toReal_eq_roundAt_of_eq_roundDyadic {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) {result : Model fmt} {r : ℝ}
    (h : ∃ exact : Numerics.Dyadic, result = roundDyadic fmt exact ∧ exact.toReal = r)
    (hfin : isFinite result = true) : toReal result = roundAt fmt r := by
  obtain ⟨exact, rfl, rfl⟩ := h
  exact toReal_roundDyadic_eq_roundAt fmt hfmt exact hfin

/--
Under a conventional IEEE descriptor a finite sum has finite operands: a NaN operand gives a NaN,
and an infinite operand gives that infinity or the invalid-operation NaN.
-/
theorem isFinite_of_isFinite_add {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {x y : Model fmt} (h : isFinite (add x y) = true) :
    isFinite x = true ∧ isFinite y = true := by
  have hinvalid := isFinite_invalidResult hfmt
  rw [Proof.add_eq_spec, Spec.add] at h
  split at h
  · next dx dy hdx hdy =>
    exact ⟨isFinite_eq_true_of_toDyadic?_some hdx, isFinite_eq_true_of_toDyadic?_some hdy⟩
  · split at h
    · next nan hnan =>
      simp [isFinite_eq_false_of_isNaN (isNaN_of_chooseNaN2_eq_some hnan)] at h
    · split_ifs at h <;> first
        | simp [hinvalid] at h
        | (have := isInf_eq_false_of_isFinite_eq_true _ h; simp_all)

/--
Finite operands whose exact real sum is within the destination's largest finite magnitude cannot
overflow under nearest-even addition.
-/
theorem isFinite_add_of_abs_toReal_add_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x + toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (add x y) = true :=
  isFinite_of_eq_roundDyadic hfmt (add_eq_roundDyadic_of_isFinite x y hx hy) hbound

/--
The triangle bound `|x| + |y| ≤ maxFinite` is a symbolic sufficient condition for finite
nearest-even addition.
-/
theorem isFinite_add_of_abs_add_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x| + |toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (add x y) = true :=
  isFinite_add_of_abs_toReal_add_le_posMaxFinite x y hfmt hx hy
    ((abs_add_le (toReal x) (toReal y)).trans hbound)

/--
Finite addition is exact real addition followed by one nearest-even format rounding.

The hypothesis `hfin` excludes overflow: it asks that the executable sum itself be finite, which
is decidable on the result and forces finite operands. The theorem
`toReal_add_eq_roundAt_of_abs_add_le_posMaxFinite` replaces that observation by a symbolic bound
on the operands.
-/
theorem toReal_add_eq_roundAt {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hfin : isFinite (add x y) = true) :
    toReal (add x y) = roundAt fmt (toReal x + toReal y) := by
  obtain ⟨hx, hy⟩ := isFinite_of_isFinite_add hfmt hfin
  exact toReal_eq_roundAt_of_eq_roundDyadic hfmt (add_eq_roundDyadic_of_isFinite x y hx hy) hfin

/--
Finite addition under a symbolic triangle bound is exact real addition followed by one
nearest-even format rounding.
-/
theorem toReal_add_eq_roundAt_of_abs_add_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x| + |toReal y| ≤ toReal (posMaxFinite fmt)) :
    toReal (add x y) = roundAt fmt (toReal x + toReal y) :=
  toReal_add_eq_roundAt x y hfmt
    (isFinite_add_of_abs_add_le_posMaxFinite x y hfmt hx hy hbound)

/-- Adding a finite value to a zero is exact. -/
theorem toReal_add_of_isZero_left {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hx : isZero x = true) (hy : isFinite y = true) :
    toReal (add x y) = toReal y := by
  have hxf := isFinite_eq_true_of_isZero_eq_true x hx
  have h0 := toReal_eq_zero_of_isZero x hx
  have hout := isFinite_add_of_abs_toReal_add_le_posMaxFinite x y hfmt hxf hy
    (by rw [h0, zero_add]; exact abs_toReal_le_posMaxFinite_of_isFinite y hy)
  rw [toReal_add_eq_roundAt x y hfmt hout, h0, zero_add, roundAt_toReal_eq y hy]

/-- Adding a zero to a finite value is exact. -/
theorem toReal_add_of_isZero_right {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hx : isFinite x = true) (hy : isZero y = true) :
    toReal (add x y) = toReal x := by
  have hyf := isFinite_eq_true_of_isZero_eq_true y hy
  have h0 := toReal_eq_zero_of_isZero y hy
  have hout := isFinite_add_of_abs_toReal_add_le_posMaxFinite x y hfmt hx hyf
    (by rw [h0, add_zero]; exact abs_toReal_le_posMaxFinite_of_isFinite x hx)
  rw [toReal_add_eq_roundAt x y hfmt hout, h0, add_zero, roundAt_toReal_eq x hx]

/--
On finite operands, nearest-even multiplication is the zero of the product sign when an operand is
zero, and otherwise one `roundDyadic` of an exact dyadic whose real value is the exact product.
-/
private theorem mul_eq_of_isFinite {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    (∃ sign, mul x y = zero fmt sign ∧ toReal x * toReal y = 0) ∨
      ∃ exact : Numerics.Dyadic, mul x y = roundDyadic fmt exact ∧
        exact.toReal = toReal x * toReal y := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  by_cases hxzero : dx.significand = 0
  · refine Or.inl ⟨Bool.xor dx.negative dy.negative,
      by simp [Proof.mul_eq_spec, Spec.mul, hdx, hdy, hxzero], ?_⟩
    simp [toReal_eq, hdx, Numerics.Dyadic.toReal, hxzero]
  by_cases hyzero : dy.significand = 0
  · refine Or.inl ⟨Bool.xor dx.negative dy.negative,
      by simp [Proof.mul_eq_spec, Spec.mul, hdx, hdy, hyzero], ?_⟩
    simp [toReal_eq, hdy, Numerics.Dyadic.toReal, hyzero]
  refine Or.inr ⟨{ negative := Bool.xor dx.negative dy.negative
                   significand := dx.significand * dy.significand
                   exponent := dx.exponent + dy.exponent },
    by simp [Proof.mul_eq_spec, Spec.mul, hdx, hdy, hxzero, hyzero], ?_⟩
  rw [Dyadic.toReal_mul]
  simp [toReal_eq, hdx, hdy]

/--
Under a conventional IEEE descriptor a finite product has finite operands: a NaN operand gives a
NaN, and an infinite operand gives an infinity or the invalid-operation NaN.
-/
theorem isFinite_of_isFinite_mul {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {x y : Model fmt} (h : isFinite (mul x y) = true) :
    isFinite x = true ∧ isFinite y = true := by
  have hinvalid := isFinite_invalidResult hfmt
  rw [Proof.mul_eq_spec, Spec.mul] at h
  split at h
  · next dx dy hdx hdy =>
    exact ⟨isFinite_eq_true_of_toDyadic?_some hdx, isFinite_eq_true_of_toDyadic?_some hdy⟩
  · split at h
    · next nan hnan =>
      simp [isFinite_eq_false_of_isNaN (isNaN_of_chooseNaN2_eq_some hnan)] at h
    · split_ifs at h <;> simp [hinvalid, isFinite_nativeOverflow hfmt] at h

/--
Finite operands whose exact real product is within the destination's largest finite magnitude
cannot overflow under nearest-even multiplication.
-/
theorem isFinite_mul_of_abs_mul_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x| * |toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (mul x y) = true := by
  rcases mul_eq_of_isFinite x y hx hy with ⟨sign, hmul, -⟩ | hround
  · rw [hmul]
    exact isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt sign)
  · exact isFinite_of_eq_roundDyadic hfmt hround (by rw [abs_mul]; exact hbound)

/--
Finite multiplication is exact real multiplication followed by one nearest-even rounding.

The hypothesis `hfin` excludes overflow by asking that the executable product be finite, and it
forces finite operands; `toReal_mul_eq_roundAt_of_abs_mul_le_posMaxFinite` supplies it from a
bound on the operands.
-/
theorem toReal_mul_eq_roundAt {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hfin : isFinite (mul x y) = true) :
    toReal (mul x y) = roundAt fmt (toReal x * toReal y) := by
  obtain ⟨hx, hy⟩ := isFinite_of_isFinite_mul hfmt hfin
  rcases mul_eq_of_isFinite x y hx hy with ⟨sign, hmul, hzero⟩ | hround
  · rw [hmul, toReal_zero, hzero, roundAt_zero]
  · exact toReal_eq_roundAt_of_eq_roundDyadic hfmt hround hfin

/--
Finite multiplication under a symbolic magnitude-product bound is exact real multiplication
followed by one nearest-even format rounding.
-/
theorem toReal_mul_eq_roundAt_of_abs_mul_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x| * |toReal y| ≤ toReal (posMaxFinite fmt)) :
    toReal (mul x y) = roundAt fmt (toReal x * toReal y) :=
  toReal_mul_eq_roundAt x y hfmt
    (isFinite_mul_of_abs_mul_le_posMaxFinite x y hfmt hx hy hbound)

/-- Multiplying a zero by a finite value gives exactly zero. -/
theorem toReal_mul_of_isZero_left {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hx : isZero x = true) (hy : isFinite y = true) :
    toReal (mul x y) = 0 := by
  have h0 := toReal_eq_zero_of_isZero x hx
  rw [toReal_mul_eq_roundAt_of_abs_mul_le_posMaxFinite x y hfmt
    (isFinite_eq_true_of_isZero_eq_true x hx) hy (by
      rw [h0, abs_zero, zero_mul]
      exact (abs_nonneg _).trans (abs_toReal_le_posMaxFinite_of_isFinite y hy)),
    h0, zero_mul, roundAt_zero]

/-- Multiplying a finite value by a zero gives exactly zero. -/
theorem toReal_mul_of_isZero_right {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hx : isFinite x = true) (hy : isZero y = true) :
    toReal (mul x y) = 0 := by
  have h0 := toReal_eq_zero_of_isZero y hy
  rw [toReal_mul_eq_roundAt_of_abs_mul_le_posMaxFinite x y hfmt hx
    (isFinite_eq_true_of_isZero_eq_true y hy) (by
      rw [h0, abs_zero, mul_zero]
      exact (abs_nonneg _).trans (abs_toReal_le_posMaxFinite_of_isFinite x hx)),
    h0, mul_zero, roundAt_zero]

/-- Multiplying a value of magnitude one by a finite value is exact. -/
theorem toReal_mul_of_abs_toReal_eq_one_left {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hx : isFinite x = true) (hy : isFinite y = true)
    (h1 : |toReal x| = 1) :
    toReal (mul x y) = toReal x * toReal y := by
  rw [toReal_mul_eq_roundAt_of_abs_mul_le_posMaxFinite x y hfmt hx hy (by
    rw [h1, one_mul]
    exact abs_toReal_le_posMaxFinite_of_isFinite y hy)]
  rcases (abs_eq zero_le_one).1 h1 with h | h <;> rw [h]
  · rw [one_mul, roundAt_toReal_eq y hy]
  · rw [neg_one_mul, roundAt_neg, IEEERoundingMode.negate, roundAt_toReal_eq y hy]

/-- Multiplying a finite value by a value of magnitude one is exact. -/
theorem toReal_mul_of_abs_toReal_eq_one_right {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hx : isFinite x = true) (hy : isFinite y = true)
    (h1 : |toReal y| = 1) :
    toReal (mul x y) = toReal x * toReal y := by
  rw [toReal_mul_eq_roundAt_of_abs_mul_le_posMaxFinite x y hfmt hx hy (by
    rw [h1, mul_one]
    exact abs_toReal_le_posMaxFinite_of_isFinite x hx)]
  rcases (abs_eq zero_le_one).1 h1 with h | h <;> rw [h]
  · rw [mul_one, roundAt_toReal_eq x hx]
  · rw [mul_neg_one, roundAt_neg, IEEERoundingMode.negate, roundAt_toReal_eq x hx]

/-! ## Decoded exact results -/

section Decoded

variable {fmt : FloatFormat} {x y z : Model fmt}

/--
If the exact sum of two decoded values is the decoded value of some `z`, the rounded sum decodes to
that exact sum.
-/
theorem toRat?_add_of_representable (hfmt : fmt.isIEEE = true) {p q : ℚ}
    (hx : toRat? x = some p) (hy : toRat? y = some q) (hz : toRat? z = some (p + q)) :
    toRat? (add x y) = some (p + q) := by
  have hxf := Algebraic.isFinite_of_toRat?_eq_some hx
  have hyf := Algebraic.isFinite_of_toRat?_eq_some hy
  have hzf := Algebraic.isFinite_of_toRat?_eq_some hz
  have hexact : toReal x + toReal y = toReal z := by
    rw [Algebraic.toReal_of_toRat?_eq_some hx, Algebraic.toReal_of_toRat?_eq_some hy,
      Algebraic.toReal_of_toRat?_eq_some hz, Rat.cast_add]
  have hout := isFinite_add_of_abs_toReal_add_le_posMaxFinite x y hfmt hxf hyf
    (by rw [hexact]; exact abs_toReal_le_posMaxFinite_of_isFinite z hzf)
  refine Algebraic.toRat?_eq_some_of_toReal_eq hout ?_
  rw [toReal_add_eq_roundAt x y hfmt hout, hexact, roundAt_toReal_eq z hzf,
    Algebraic.toReal_of_toRat?_eq_some hz]

/--
If the exact product of two decoded values is the decoded value of some `z`, the rounded product
decodes to that exact product.
-/
theorem toRat?_mul_of_representable (hfmt : fmt.isIEEE = true) {p q : ℚ}
    (hx : toRat? x = some p) (hy : toRat? y = some q) (hz : toRat? z = some (p * q)) :
    toRat? (mul x y) = some (p * q) := by
  have hxf := Algebraic.isFinite_of_toRat?_eq_some hx
  have hyf := Algebraic.isFinite_of_toRat?_eq_some hy
  have hzf := Algebraic.isFinite_of_toRat?_eq_some hz
  have hexact : toReal x * toReal y = toReal z := by
    rw [Algebraic.toReal_of_toRat?_eq_some hx, Algebraic.toReal_of_toRat?_eq_some hy,
      Algebraic.toReal_of_toRat?_eq_some hz, Rat.cast_mul]
  have hout := isFinite_mul_of_abs_mul_le_posMaxFinite x y hfmt hxf hyf
    (by rw [← abs_mul, hexact]; exact abs_toReal_le_posMaxFinite_of_isFinite z hzf)
  refine Algebraic.toRat?_eq_some_of_toReal_eq hout ?_
  rw [toReal_mul_eq_roundAt x y hfmt hout, hexact, roundAt_toReal_eq z hzf,
    Algebraic.toReal_of_toRat?_eq_some hz]

/-- Adding a value to one that decodes to zero is exact. -/
theorem toRat?_add_of_toRat?_eq_some_zero_left (hfmt : fmt.isIEEE = true) {q : ℚ}
    (hx : toRat? x = some 0) (hy : toRat? y = some q) : toRat? (add x y) = some q := by
  simpa using toRat?_add_of_representable hfmt hx hy (by rwa [zero_add])

/-- Adding a value that decodes to zero is exact. -/
theorem toRat?_add_of_toRat?_eq_some_zero_right (hfmt : fmt.isIEEE = true) {q : ℚ}
    (hx : toRat? x = some q) (hy : toRat? y = some 0) : toRat? (add x y) = some q := by
  simpa using toRat?_add_of_representable hfmt hx hy (by rwa [add_zero])

/-- The product of a value that decodes to zero and a finite value decodes to zero. -/
theorem toRat?_mul_of_toRat?_eq_some_zero_left (hfmt : fmt.isIEEE = true)
    (hx : toRat? x = some 0) (hy : isFinite y = true) : toRat? (mul x y) = some 0 := by
  obtain ⟨q, hq, -⟩ := Algebraic.exists_toRat?_of_isFinite hy
  simpa using toRat?_mul_of_representable hfmt hx hq (by rwa [zero_mul])

/-- The product of a finite value and a value that decodes to zero decodes to zero. -/
theorem toRat?_mul_of_toRat?_eq_some_zero_right (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : toRat? y = some 0) : toRat? (mul x y) = some 0 := by
  obtain ⟨p, hp, -⟩ := Algebraic.exists_toRat?_of_isFinite hx
  simpa using toRat?_mul_of_representable hfmt hp hy (by rwa [mul_zero])

/-- Multiplying by a value that decodes to `1` or `-1` on the left is exact. -/
theorem toRat?_mul_of_abs_eq_one_left (hfmt : fmt.isIEEE = true) {p q : ℚ}
    (hx : toRat? x = some p) (hp : |p| = 1) (hy : toRat? y = some q) :
    toRat? (mul x y) = some (p * q) := by
  have hxf := Algebraic.isFinite_of_toRat?_eq_some hx
  have hyf := Algebraic.isFinite_of_toRat?_eq_some hy
  have hone : |toReal x| = 1 := by rw [Algebraic.toReal_of_toRat?_eq_some hx]; exact_mod_cast hp
  have hout := isFinite_mul_of_abs_mul_le_posMaxFinite x y hfmt hxf hyf
    (by rw [hone, one_mul]; exact abs_toReal_le_posMaxFinite_of_isFinite y hyf)
  refine Algebraic.toRat?_eq_some_of_toReal_eq hout ?_
  rw [toReal_mul_of_abs_toReal_eq_one_left x y hfmt hxf hyf hone,
    Algebraic.toReal_of_toRat?_eq_some hx, Algebraic.toReal_of_toRat?_eq_some hy, Rat.cast_mul]

/-- Multiplying by a value that decodes to `1` or `-1` on the right is exact. -/
theorem toRat?_mul_of_abs_eq_one_right (hfmt : fmt.isIEEE = true) {p q : ℚ}
    (hx : toRat? x = some p) (hy : toRat? y = some q) (hq : |q| = 1) :
    toRat? (mul x y) = some (p * q) := by
  have hxf := Algebraic.isFinite_of_toRat?_eq_some hx
  have hyf := Algebraic.isFinite_of_toRat?_eq_some hy
  have hone : |toReal y| = 1 := by rw [Algebraic.toReal_of_toRat?_eq_some hy]; exact_mod_cast hq
  have hout := isFinite_mul_of_abs_mul_le_posMaxFinite x y hfmt hxf hyf
    (by rw [hone, mul_one]; exact abs_toReal_le_posMaxFinite_of_isFinite x hxf)
  refine Algebraic.toRat?_eq_some_of_toReal_eq hout ?_
  rw [toReal_mul_of_abs_toReal_eq_one_right x y hfmt hxf hyf hone,
    Algebraic.toReal_of_toRat?_eq_some hx, Algebraic.toReal_of_toRat?_eq_some hy, Rat.cast_mul]

end Decoded

/--
On finite IEEE operands, nearest-even fused multiply-add is one `roundDyadic` of an exact dyadic
whose real value is the exact fused result.
-/
private theorem fma_eq_roundDyadic_of_isFinite
    {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true) :
    ∃ exact : Numerics.Dyadic, fma x y z = roundDyadic fmt exact ∧
      exact.toReal = toReal x * toReal y + toReal z := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  obtain ⟨dz, hdz⟩ := exists_toDyadic?_of_isFinite hz
  let product : Numerics.Dyadic :=
    { negative := Bool.xor dx.negative dy.negative
      significand := dx.significand * dy.significand
      exponent := dx.exponent + dy.exponent }
  have hencoding : fmt.encoding = .ieee :=
    ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  have hxSNaN : IEEE.isSNaN x = false := by
    simpa [isSNaN, hencoding] using isSNaN_eq_false_of_toDyadic?_some hdx
  have hySNaN : IEEE.isSNaN y = false := by
    simpa [isSNaN, hencoding] using isSNaN_eq_false_of_toDyadic?_some hdy
  have hzSNaN : IEEE.isSNaN z = false := by
    simpa [isSNaN, hencoding] using isSNaN_eq_false_of_toDyadic?_some hdz
  refine ⟨addDyadic product dz, ?_, ?_⟩
  · simp [Proof.fma_eq_spec, Spec.fma, chooseNaN3, isSNaN, hencoding, hdx, hdy, hdz,
      hxSNaN, hySNaN, hzSNaN,
      isNaN_eq_false_of_toDyadic?_some,
      isInf_eq_false_of_toDyadic?_some, product]
  · rw [Dyadic.toReal_addDyadic,
      show product.toReal = dx.toReal * dy.toReal by
        simpa [product] using Dyadic.toReal_mul dx dy]
    simp [toReal_eq, hdx, hdy, hdz]

/--
Under a conventional IEEE descriptor a finite fused multiply-add has finite operands: a NaN
operand gives a NaN, and an infinite operand gives an infinity or the invalid-operation NaN.
-/
theorem isFinite_of_isFinite_fma {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {x y z : Model fmt} (h : isFinite (fma x y z) = true) :
    isFinite x = true ∧ isFinite y = true ∧ isFinite z = true := by
  have hinvalid := isFinite_invalidResult hfmt
  rw [Proof.fma_eq_spec, Spec.fma] at h
  split at h
  · next nan hnan =>
    simp [isFinite_eq_false_of_isNaN (isNaN_of_chooseNaN3_eq_some hnan)] at h
  · next hnan =>
    rw [chooseNaN3_eq_none_iff] at hnan
    split_ifs at h <;> (try simp [hinvalid, isFinite_nativeOverflow hfmt] at h) <;>
      (try (have := isInf_eq_false_of_isFinite_eq_true _ h; simp_all; done))
    · split at h <;> simp [hinvalid, isFinite_nativeOverflow hfmt] at h
    · split at h
      · next dx dy dz hdx hdy hdz =>
        exact ⟨isFinite_eq_true_of_toDyadic?_some hdx, isFinite_eq_true_of_toDyadic?_some hdy,
          isFinite_eq_true_of_toDyadic?_some hdz⟩
      · simp [hinvalid] at h

/--
Finite operands whose exact fused result is within the destination's largest finite magnitude
cannot overflow under nearest-even fused multiply-add.
-/
theorem isFinite_fma_of_abs_toReal_fma_le_posMaxFinite
    {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hbound : |toReal x * toReal y + toReal z| ≤ toReal (posMaxFinite fmt)) :
    isFinite (fma x y z) = true :=
  isFinite_of_eq_roundDyadic hfmt (fma_eq_roundDyadic_of_isFinite x y z hfmt hx hy hz) hbound

/--
The triangle bound `|x| * |y| + |z| ≤ maxFinite` is a symbolic sufficient condition for finite
nearest-even fused multiply-add.
-/
theorem isFinite_fma_of_abs_mul_add_le_posMaxFinite
    {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hbound :
      |toReal x| * |toReal y| + |toReal z| ≤ toReal (posMaxFinite fmt)) :
    isFinite (fma x y z) = true := by
  apply isFinite_fma_of_abs_toReal_fma_le_posMaxFinite x y z hfmt hx hy hz
  calc
    |toReal x * toReal y + toReal z| ≤
        |toReal x * toReal y| + |toReal z| :=
      abs_add_le _ _
    _ = |toReal x| * |toReal y| + |toReal z| := by rw [abs_mul]
    _ ≤ toReal (posMaxFinite fmt) := hbound

/--
Finite fused multiply-add is exact real multiplication and addition followed by one rounding.

The hypothesis `hfin` excludes overflow by asking that the executable result be finite, and it
forces finite operands; `toReal_fma_eq_roundAt_of_abs_mul_add_le_posMaxFinite` supplies it from a
bound on the operands.
-/
theorem toReal_fma_eq_roundAt {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hfin : isFinite (fma x y z) = true) :
    toReal (fma x y z) = roundAt fmt (toReal x * toReal y + toReal z) := by
  obtain ⟨hx, hy, hz⟩ := isFinite_of_isFinite_fma hfmt hfin
  exact toReal_eq_roundAt_of_eq_roundDyadic hfmt
    (fma_eq_roundDyadic_of_isFinite x y z hfmt hx hy hz) hfin

/--
Finite fused multiply-add under a symbolic triangle bound is exact real FMA followed by one
nearest-even format rounding.
-/
theorem toReal_fma_eq_roundAt_of_abs_mul_add_le_posMaxFinite
    {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hbound :
      |toReal x| * |toReal y| + |toReal z| ≤ toReal (posMaxFinite fmt)) :
    toReal (fma x y z) = roundAt fmt (toReal x * toReal y + toReal z) :=
  toReal_fma_eq_roundAt x y z hfmt
    (isFinite_fma_of_abs_mul_add_le_posMaxFinite x y z hfmt hx hy hz hbound)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
