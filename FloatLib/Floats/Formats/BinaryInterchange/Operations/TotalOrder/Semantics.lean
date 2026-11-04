/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Encoding
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Proof

/-!
# Numerical and exceptional-value rules for binary total order

Here the order laws of binary total order come from the order on complete exact data. Numerical
theorems connect the predicate to dyadic, real and extended-real comparison. For exceptional
values we state the IEEE sign and signaling-class priorities as theorems, and also the payload
direction FloatLib chose where the standard leaves it to the implementation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- The model predicate is the shared order on complete decoded data. -/
theorem totalOrder_eq_exactValue {fmt : FloatFormat} (x y : Model fmt) :
    totalOrder x y = ExactValue.totalOrder (exactValue x) (exactValue y) := rfl

/-- All binary words precede themselves, including signaling NaNs. -/
@[simp] theorem totalOrder_refl {fmt : FloatFormat} (x : Model fmt) :
    totalOrder x x = true :=
  ExactValue.totalOrder_refl _

/-- Totality is independent of field width, bias, and exceptional-value policy. -/
theorem totalOrder_total {fmt : FloatFormat} (x y : Model fmt) :
    totalOrder x y = true ∨ totalOrder y x = true :=
  ExactValue.totalOrder_total _ _

/-- Binary total ordering is transitive for every descriptor. -/
theorem totalOrder_trans {fmt : FloatFormat} {x y z : Model fmt}
    (hxy : totalOrder x y = true) (hyz : totalOrder y z = true) :
    totalOrder x z = true :=
  ExactValue.totalOrder_trans hxy hyz

/-- Mutual ordering identifies the complete decoded data for every descriptor. -/
theorem totalOrder_both_iff_exactValue_eq {fmt : FloatFormat} (x y : Model fmt) :
    totalOrder x y = true ∧ totalOrder y x = true ↔ exactValue x = exactValue y :=
  ExactValue.totalOrder_both_iff _ _

/-- Complete decoded data determine their binary word, so total order is antisymmetric. -/
theorem totalOrder_antisymm {fmt : FloatFormat}
    {x y : Model fmt} (hxy : totalOrder x y = true) (hyx : totalOrder y x = true) :
    x = y :=
  exactValue_injective (ExactValue.totalOrder_antisymm hxy hyx)

/-- Mutual comparison holds if and only if the operands are bitwise identical. -/
theorem totalOrder_both_iff {fmt : FloatFormat}
    (x y : Model fmt) :
    totalOrder x y = true ∧ totalOrder y x = true ↔ x = y := by
  rw [totalOrder_both_iff_exactValue_eq, exactValue_injective.eq_iff]

/-- Successful finite decoding transports the complete signed numerical ordering rule. -/
theorem totalOrder_iff_of_toDyadic? {fmt : FloatFormat} {x y : Model fmt}
    {a b : Numerics.Dyadic} (hx : toDyadic? x = some a) (hy : toDyadic? y = some b) :
    totalOrder x y = true ↔
      a.toRat < b.toRat ∨ a.toRat = b.toRat ∧
        ((a.negative = true ∧ b.negative = false) ∨ a.negative = b.negative ∧
          (if a.negative then b.exponent ≤ a.exponent else a.exponent ≤ b.exponent)) := by
  rw [totalOrder, exactValue_eq_finite_of_toDyadic?_eq_some hx,
    exactValue_eq_finite_of_toDyadic?_eq_some hy, ExactValue.totalOrder_finite_iff]

/-- A strict real order of decoded finite values is the strict order of their rationals. -/
private theorem toRat_lt_of_toReal_lt {fmt : FloatFormat} {x y : Model fmt}
    {a b : Numerics.Dyadic} (ha : toDyadic? x = some a) (hb : toDyadic? y = some b)
    (h : toReal x < toReal y) : a.toRat < b.toRat := by
  have hab : a.toReal < b.toReal := by simpa [toReal_eq, ha, hb] using h
  exact_mod_cast (show (a.toRat : ℝ) < (b.toRat : ℝ) by simpa using hab)

/-- Strict numerical increase of finite binary values implies total ordering. -/
theorem totalOrder_of_toReal_lt {fmt : FloatFormat} {x y : Model fmt}
    (hx : isFinite x = true) (hy : isFinite y = true) (h : toReal x < toReal y) :
    totalOrder x y = true := by
  obtain ⟨a, ha⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨b, hb⟩ := exists_toDyadic?_of_isFinite hy
  exact (totalOrder_iff_of_toDyadic? ha hb).2 (Or.inl (toRat_lt_of_toReal_lt ha hb h))

/-- Strict numerical decrease of finite binary values fails total ordering. -/
theorem totalOrder_eq_false_of_toReal_gt {fmt : FloatFormat} {x y : Model fmt}
    (hx : isFinite x = true) (hy : isFinite y = true) (h : toReal y < toReal x) :
    totalOrder x y = false := by
  obtain ⟨a, ha⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨b, hb⟩ := exists_toDyadic?_of_isFinite hy
  have hrat := toRat_lt_of_toReal_lt hb ha h
  simpa [totalOrder, exactValue_eq_finite_of_toDyadic?_eq_some ha,
    exactValue_eq_finite_of_toDyadic?_eq_some hb] using
    ExactValue.totalOrder_finite_eq_false_of_gt hrat

/-- A successful numerical comparison excludes NaNs on both sides. -/
private theorem not_nan_of_compare_some {fmt : FloatFormat} {x y : Model fmt}
    {order : Ordering} (h : compare x y = some order) :
    isNaN x = false ∧ isNaN y = false := by
  have hnone : compare x y ≠ none := by simp [h]
  simpa using mt (compare_eq_none_iff x y).2 hnone

/-- The existing numerical comparator's strict order is respected, including infinities. -/
theorem totalOrder_of_compare_eq_lt {fmt : FloatFormat} {x y : Model fmt}
    (h : compare x y = some .lt) : totalOrder x y = true := by
  obtain ⟨hxNaN, hyNaN⟩ := not_nan_of_compare_some h
  cases hxInf : isInf x <;> cases hyInf : isInf y
  · have hx := isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hxNaN hxInf
    have hy := isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hyNaN hyInf
    exact totalOrder_of_toReal_lt hx hy
      ((compare_eq_some_lt_iff_toReal_lt_of_isFinite x y hx hy).1 h)
  · have hx := isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hxNaN hxInf
    obtain ⟨a, ha⟩ := exists_toDyadic?_of_isFinite hx
    rw [totalOrder, exactValue_eq_finite_of_toDyadic?_eq_some ha,
      exactValue_eq_infinity_of_isInf hyInf]
    cases hs : signBit y <;>
      simp_all [compare, compareNonNaN]
  · have hy := isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hyNaN hyInf
    obtain ⟨b, hb⟩ := exists_toDyadic?_of_isFinite hy
    rw [totalOrder, exactValue_eq_infinity_of_isInf hxInf,
      exactValue_eq_finite_of_toDyadic?_eq_some hb]
    cases hs : signBit x <;>
      simp_all [compare, compareNonNaN]
  · rw [totalOrder, exactValue_eq_infinity_of_isInf hxInf,
      exactValue_eq_infinity_of_isInf hyInf]
    cases hs : signBit x <;> cases ht : signBit y <;>
      simp_all [compare, compareNonNaN]

/-- The existing numerical comparator's reversed strict order fails total ordering. -/
theorem totalOrder_eq_false_of_compare_eq_gt {fmt : FloatFormat} {x y : Model fmt}
    (h : compare x y = some .gt) : totalOrder x y = false := by
  obtain ⟨hxNaN, hyNaN⟩ := not_nan_of_compare_some h
  obtain ⟨a, ha⟩ := exists_toEReal?_of_isNaN_eq_false x hxNaN
  obtain ⟨b, hb⟩ := exists_toEReal?_of_isNaN_eq_false y hyNaN
  have hlt := (compare_eq_some_gt_iff_toEReal_gt ha hb).1 h
  have hreverse := totalOrder_of_compare_eq_lt
    ((compare_eq_some_lt_iff_toEReal_lt hb ha).2 hlt)
  apply Bool.eq_false_iff.mpr
  intro hforward
  have hxy := totalOrder_antisymm hforward hreverse
  have hab : a = b := Option.some.inj (ha.symm.trans (hxy ▸ hb))
  exact (ne_of_gt hlt) hab

/-- Total order extends extended-real strict order on non-NaNs. -/
theorem totalOrder_of_toEReal_lt {fmt : FloatFormat} {x y : Model fmt} {a b : EReal}
    (hx : toEReal? x = some a) (hy : toEReal? y = some b) (h : a < b) :
    totalOrder x y = true :=
  totalOrder_of_compare_eq_lt ((compare_eq_some_lt_iff_toEReal_lt hx hy).2 h)

/-- Extended-real strict decrease fails total order on non-NaNs. -/
theorem totalOrder_eq_false_of_toEReal_gt
    {fmt : FloatFormat} {x y : Model fmt} {a b : EReal}
    (hx : toEReal? x = some a) (hy : toEReal? y = some b) (h : b < a) :
    totalOrder x y = false :=
  totalOrder_eq_false_of_compare_eq_gt ((compare_eq_some_gt_iff_toEReal_gt hx hy).2 h)

/-- Zeros are ordered by their stored signs. -/
theorem totalOrder_zero_iff {fmt : FloatFormat} {x y : Model fmt}
    (hx : isZero x = true) (hy : isZero y = true) :
    totalOrder x y = (signBit x || !signBit y) := by
  rw [totalOrder,
    exactValue_eq_finite_of_toDyadic?_eq_some (toDyadic?_eq_zero_of_isZero_eq_true x hx),
    exactValue_eq_finite_of_toDyadic?_eq_some (toDyadic?_eq_zero_of_isZero_eq_true y hy)]
  cases signBit x <;> cases signBit y <;>
    apply Bool.eq_iff_iff.mpr <;>
    rw [ExactValue.totalOrder_finite_iff] <;> simp

/--
The negative-sign zero precedes the positive zero. In a format without signed zero both are
positive zero, which precedes itself.
-/
@[simp] theorem totalOrder_negZero_posZero (fmt : FloatFormat) :
    totalOrder (zero fmt true) (zero fmt false) = true := by
  rw [totalOrder_zero_iff (isZero_zero _ _) (isZero_zero _ _)]
  simp

/-- In a signed-zero format, positive zero does not precede negative zero. -/
@[simp] theorem totalOrder_posZero_negZero {fmt : FloatFormat}
    (hfmt : fmt.supportsSignedZero = true) :
    totalOrder (zero fmt false) (zero fmt true) = false := by
  rw [totalOrder_zero_iff (isZero_zero _ _) (isZero_zero _ _)]
  simp [zero, hfmt]

/-- A value that is not a NaN interprets as a finite number or as an infinity of its sign. -/
theorem exactValue_finite_or_infinity_of_isNaN_eq_false {fmt : FloatFormat}
    {x : Model fmt} (hx : isNaN x = false) :
    (∃ d, exactValue x = .finite d) ∨ exactValue x = .infinity (signBit x) := by
  cases hinf : isInf x
  · obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite
      (isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hx hinf)
    exact Or.inl ⟨d, exactValue_eq_finite_of_toDyadic?_eq_some hd⟩
  · exact Or.inr (exactValue_eq_infinity_of_isInf hinf)

/-- A NaN precedes a number just when its sign bit is negative. -/
theorem totalOrder_nan_number {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = true) (hy : isNaN y = false) :
    totalOrder x y = signBit x := by
  rw [totalOrder, exactValue_eq_nan_of_isNaN hx]
  rcases exactValue_finite_or_infinity_of_isNaN_eq_false hy with ⟨d, hd⟩ | hinf
  · rw [hd]
    exact ExactValue.totalOrder_nan_finite _ _ _ _
  · rw [hinf]
    exact ExactValue.totalOrder_nan_infinity _ _ _ _

/-- A number precedes a NaN just when that NaN has positive sign. -/
theorem totalOrder_number_nan {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = false) (hy : isNaN y = true) :
    totalOrder x y = !signBit y := by
  rw [totalOrder, exactValue_eq_nan_of_isNaN hy]
  rcases exactValue_finite_or_infinity_of_isNaN_eq_false hx with ⟨d, hd⟩ | hinf
  · rw [hd]
    exact ExactValue.totalOrder_finite_nan _ _ _ _
  · rw [hinf]
    exact ExactValue.totalOrder_infinity_nan _ _ _ _

/-- Complete sign, signaling-class, and payload rule for two binary NaNs. -/
theorem totalOrder_nan_iff {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = true) (hy : isNaN y = true) :
    totalOrder x y = true ↔
      (signBit x = true ∧ signBit y = false) ∨ signBit x = signBit y ∧
        (if signBit x then
          (isSNaN x = false ∧ isSNaN y = true) ∨
            isSNaN x = isSNaN y ∧ fracField y ≤ fracField x
        else
          (isSNaN x = true ∧ isSNaN y = false) ∨
            isSNaN x = isSNaN y ∧ fracField x ≤ fracField y) := by
  rw [totalOrder, exactValue_eq_nan_of_isNaN hx, exactValue_eq_nan_of_isNaN hy,
    ExactValue.totalOrder_nan_iff]

/-- Positive NaNs in the same NaN class are ordered by increasing fraction payload. -/
theorem totalOrder_posNaN_payload {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = true) (hy : isNaN y = true)
    (hsx : signBit x = false) (hsy : signBit y = false)
    (hclass : isSNaN x = isSNaN y) :
    totalOrder x y = true ↔ fracField x ≤ fracField y := by
  rw [totalOrder_nan_iff hx hy]
  simp [hsx, hsy, hclass]

/-- Negative NaNs in the same NaN class are ordered by decreasing fraction payload. -/
theorem totalOrder_negNaN_payload {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = true) (hy : isNaN y = true)
    (hsx : signBit x = true) (hsy : signBit y = true)
    (hclass : isSNaN x = isSNaN y) :
    totalOrder x y = true ↔ fracField y ≤ fracField x := by
  rw [totalOrder_nan_iff hx hy]
  simp [hsx, hsy, hclass]

end FloatLib.Floats.Formats.BinaryInterchange.Model
