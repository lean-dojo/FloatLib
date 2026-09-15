/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Sign

/-!
# Total ordering by magnitude

Magnitude comparison is a total preorder on complete data: mutual comparison identifies the
absolute data, including NaN signaling status and payload. It agrees with absolute numerical
comparison on finite operands. In signed-zero formats, including every IEEE encoding, it is
exactly `totalOrder (abs x) (abs y)`, as specified by IEEE 754-2019 §5.7.2.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

namespace ExactValue

/-- Clearing a dyadic's sign computes the absolute value of its exact rational denotation. -/
theorem dyadic_toRat_clearSign (d : Numerics.Dyadic) :
    ({ d with negative := false } : Numerics.Dyadic).toRat = |d.toRat| := by
  cases d with
  | mk sign significand exponent =>
      cases sign <;>
        simp [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand, abs_mul,
          abs_of_nonneg (zpow_nonneg (by norm_num : (0 : Rat) ≤ 2) exponent)]

/-- Finite magnitude order compares absolute numerical values, then their exponents. -/
theorem totalOrderMag_finite_iff (a b : Numerics.Dyadic) :
    totalOrderMag (.finite a) (.finite b) = true ↔
      |a.toRat| < |b.toRat| ∨ |a.toRat| = |b.toRat| ∧ a.exponent ≤ b.exponent := by
  change totalOrder (.finite { a with negative := false })
    (.finite { b with negative := false }) = true ↔ _
  rw [totalOrder_finite_iff]
  simp [dyadic_toRat_clearSign]

/-- A strict increase in absolute numerical value gives magnitude ordering. -/
theorem totalOrderMag_finite_of_lt {a b : Numerics.Dyadic} (h : |a.toRat| < |b.toRat|) :
    totalOrderMag (.finite a) (.finite b) = true :=
  (totalOrderMag_finite_iff a b).2 (Or.inl h)

/-- A strict decrease in absolute numerical value fails magnitude ordering. -/
theorem totalOrderMag_finite_eq_false_of_gt {a b : Numerics.Dyadic}
    (h : |b.toRat| < |a.toRat|) : totalOrderMag (.finite a) (.finite b) = false := by
  apply Bool.eq_false_iff.mpr
  intro horder
  rcases (totalOrderMag_finite_iff a b).1 horder with hlt | ⟨heq, _⟩
  · exact (not_lt_of_ge h.le) hlt
  · exact (ne_of_lt h) heq.symm

/-- NaN magnitudes place signaling before quiet, with increasing payloads within each class. -/
theorem totalOrderMag_nan_iff (s t q r : Bool) (p n : Nat) :
    totalOrderMag (.nan s q p) (.nan t r n) = true ↔
      (q = true ∧ r = false) ∨ q = r ∧ p ≤ n := by
  change totalOrder (.nan false q p) (.nan false r n) = true ↔ _
  rw [totalOrder_nan_iff]
  simp

end ExactValue

/-- Magnitude comparison uses the same exact order for every binary descriptor. -/
theorem totalOrderMag_eq_exactValue {fmt : FloatFormat} (x y : Model fmt) :
    totalOrderMag x y = ExactValue.totalOrderMag (exactValue x) (exactValue y) := rfl

/-- IEEE's definition using encoded absolute value holds for every signed-zero format. -/
theorem totalOrderMag_eq_totalOrder_abs {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.supportsSignedZero = true) :
    totalOrderMag x y = totalOrder (abs x) (abs y) := by
  simp [totalOrderMag, totalOrder, ExactValue.totalOrderMag,
    exactValue_abs_of_supportsSignedZero _ hfmt]

/-- The encoded-absolute-value definition holds for every IEEE encoding, with arbitrary bias. -/
theorem totalOrderMag_eq_totalOrder_abs_of_ieee {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.encoding = .ieee) :
    totalOrderMag x y = totalOrder (abs x) (abs y) :=
  totalOrderMag_eq_totalOrder_abs x y (by simp [FloatFormat.supportsSignedZero, hfmt])

/-- Magnitude order is reflexive on every binary datum. -/
@[simp] theorem totalOrderMag_refl {fmt : FloatFormat} (x : Model fmt) :
    totalOrderMag x x = true := ExactValue.totalOrderMag_refl _

/-- Magnitude order is total, including NaN magnitudes. -/
theorem totalOrderMag_total {fmt : FloatFormat} (x y : Model fmt) :
    totalOrderMag x y = true ∨ totalOrderMag y x = true :=
  ExactValue.totalOrderMag_total _ _

/-- Magnitude order is transitive for every descriptor. -/
theorem totalOrderMag_trans {fmt : FloatFormat} {x y z : Model fmt}
    (hxy : totalOrderMag x y = true) (hyz : totalOrderMag y z = true) :
    totalOrderMag x z = true := ExactValue.totalOrderMag_trans hxy hyz

/-- Mutual magnitude comparison identifies absolute complete data, including NaN metadata. -/
theorem totalOrderMag_both_iff_exactValue_abs_eq {fmt : FloatFormat} (x y : Model fmt) :
    totalOrderMag x y = true ∧ totalOrderMag y x = true ↔
      ExactValue.abs (exactValue x) = ExactValue.abs (exactValue y) :=
  ExactValue.totalOrderMag_both_iff _ _

/-- For signed-zero formats, mutual magnitude comparison identifies absolute encoded words. -/
theorem totalOrderMag_both_iff_abs_eq {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.supportsSignedZero = true) :
    totalOrderMag x y = true ∧ totalOrderMag y x = true ↔ abs x = abs y := by
  rw [totalOrderMag_eq_totalOrder_abs x y hfmt,
    totalOrderMag_eq_totalOrder_abs y x hfmt, totalOrder_both_iff]

/-- The full finite magnitude rule is uniform in format width, bias, and encoding policy. -/
theorem totalOrderMag_iff_of_toDyadic? {fmt : FloatFormat} {x y : Model fmt}
    {a b : Numerics.Dyadic} (hx : toDyadic? x = some a) (hy : toDyadic? y = some b) :
    totalOrderMag x y = true ↔
      |a.toRat| < |b.toRat| ∨ |a.toRat| = |b.toRat| ∧ a.exponent ≤ b.exponent := by
  rw [totalOrderMag, exactValue_eq_finite_of_toDyadic?_eq_some hx,
    exactValue_eq_finite_of_toDyadic?_eq_some hy, ExactValue.totalOrderMag_finite_iff]

/-- Strict increase in absolute real value gives magnitude ordering for finite operands. -/
theorem totalOrderMag_of_abs_toReal_lt {fmt : FloatFormat} {x y : Model fmt}
    (hx : isFinite x = true) (hy : isFinite y = true) (h : |toReal x| < |toReal y|) :
    totalOrderMag x y = true := by
  obtain ⟨a, ha⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨b, hb⟩ := exists_toDyadic?_of_isFinite hy
  have hab : |a.toReal| < |b.toReal| := by simpa [toReal_eq, ha, hb] using h
  have hrat : |a.toRat| < |b.toRat| := by
    exact_mod_cast (show |(a.toRat : ℝ)| < |(b.toRat : ℝ)| by simpa using hab)
  exact (totalOrderMag_iff_of_toDyadic? ha hb).2 (Or.inl hrat)

/-- Strict decrease in absolute real value fails magnitude ordering for finite operands. -/
theorem totalOrderMag_eq_false_of_abs_toReal_gt {fmt : FloatFormat} {x y : Model fmt}
    (hx : isFinite x = true) (hy : isFinite y = true) (h : |toReal y| < |toReal x|) :
    totalOrderMag x y = false := by
  obtain ⟨a, ha⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨b, hb⟩ := exists_toDyadic?_of_isFinite hy
  have hab : |b.toReal| < |a.toReal| := by simpa [toReal_eq, ha, hb] using h
  have hrat : |b.toRat| < |a.toRat| := by
    exact_mod_cast (show |(b.toRat : ℝ)| < |(a.toRat : ℝ)| by simpa using hab)
  simpa [totalOrderMag, exactValue_eq_finite_of_toDyadic?_eq_some ha,
    exactValue_eq_finite_of_toDyadic?_eq_some hb] using
    ExactValue.totalOrderMag_finite_eq_false_of_gt hrat

/-- All zero signs have the same magnitude. -/
theorem totalOrderMag_zero {fmt : FloatFormat} {x y : Model fmt}
    (hx : isZero x = true) (hy : isZero y = true) : totalOrderMag x y = true := by
  rw [totalOrderMag_iff_of_toDyadic?
    (toDyadic?_eq_zero_of_isZero_eq_true x hx) (toDyadic?_eq_zero_of_isZero_eq_true y hy)]
  simp

/-- A NaN magnitude is strictly above every numerical magnitude, regardless of its sign. -/
theorem totalOrderMag_nan_number {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = true) (hy : isNaN y = false) : totalOrderMag x y = false := by
  rw [totalOrderMag, exactValue_eq_nan_of_isNaN hx]
  cases hinf : isInf y
  · obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite
      (isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hy hinf)
    rw [exactValue_eq_finite_of_toDyadic?_eq_some hd]
    simp [ExactValue.totalOrderMag, ExactValue.abs]
  · rw [exactValue_eq_infinity_of_isInf hinf]
    simp [ExactValue.totalOrderMag, ExactValue.abs]

/-- Every numerical magnitude precedes every NaN magnitude. -/
theorem totalOrderMag_number_nan {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = false) (hy : isNaN y = true) : totalOrderMag x y = true := by
  rcases totalOrderMag_total x y with h | h
  · exact h
  · rw [totalOrderMag_nan_number hy hx] at h
    contradiction

/-- NaN magnitude order ignores signs and compares signaling class before payload. -/
theorem totalOrderMag_nan_iff {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = true) (hy : isNaN y = true) :
    totalOrderMag x y = true ↔
      (isSNaN x = true ∧ isSNaN y = false) ∨
        isSNaN x = isSNaN y ∧ fracField x ≤ fracField y := by
  rw [totalOrderMag, exactValue_eq_nan_of_isNaN hx, exactValue_eq_nan_of_isNaN hy,
    ExactValue.totalOrderMag_nan_iff]

/-- Magnitude equality of NaNs retains both signaling class and complete fraction payload. -/
theorem totalOrderMag_nan_both_iff {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = true) (hy : isNaN y = true) :
    totalOrderMag x y = true ∧ totalOrderMag y x = true ↔
      isSNaN x = isSNaN y ∧ fracField x = fracField y := by
  rw [totalOrderMag_both_iff_exactValue_abs_eq,
    exactValue_eq_nan_of_isNaN hx, exactValue_eq_nan_of_isNaN hy]
  simp [ExactValue.abs]

end FloatLib.Floats.Formats.BinaryInterchange.Model
