/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Runtime
import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Total ordering of complete exact representations

The key used by `ExactValue.totalOrder` is injective, so its order is antisymmetric on complete
data, not just on numerical denotations. Finite comparison agrees with rational order and breaks
numerical ties by sign and exponent. Separate theorems give the NaN class and payload rules.
Magnitude order is a total preorder: mutual comparison identifies complete data after clearing
their signs, including NaN class and payload.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue

open FloatLib.Numerics

/-- At a fixed sign and exponent, the exact rational determines the complete dyadic. -/
theorem dyadic_eq_of_toRat_eq_of_negative_eq_of_exponent_eq
    {a b : Numerics.Dyadic} (hvalue : a.toRat = b.toRat)
    (hsign : a.negative = b.negative) (hexponent : a.exponent = b.exponent) :
    a = b := by
  apply Numerics.Dyadic.ext hsign _ hexponent
  have hscale : (2 : Rat) ^ b.exponent ≠ 0 := zpow_ne_zero _ (by norm_num)
  simp only [Numerics.Dyadic.toRat, hexponent, mul_left_inj' hscale] at hvalue
  change (a.signedSignificand : Rat) = (b.signedSignificand : Rat) at hvalue
  have hsigned : a.signedSignificand = b.signedSignificand := by exact_mod_cast hvalue
  simpa using congrArg Int.natAbs hsigned

/-- Equality of ordering coordinates preserves every field of a complete exact value. -/
theorem totalOrderKey_injective : Function.Injective totalOrderKey := by
  intro x y h
  cases x with
  | finite a =>
      cases y with
      | finite b =>
          have hvalue : a.toRat = b.toRat := congrArg (fun k => (ofLex (ofLex k).2).1) h
          have hsign : a.negative = b.negative := by
            have ht := congrArg (fun k => (ofLex (ofLex (ofLex k).2).2).1) h
            cases ha : a.negative <;> cases hb : b.negative <;>
              simp_all [totalOrderKey, finiteTotalOrderKey]
          have hexponent : a.exponent = b.exponent := by
            have ht := congrArg (fun k => (ofLex (ofLex (ofLex k).2).2).2) h
            cases ha : a.negative <;> simp_all [totalOrderKey, finiteTotalOrderKey]
          exact congrArg finite
            (dyadic_eq_of_toRat_eq_of_negative_eq_of_exponent_eq hvalue hsign hexponent)
      | infinity s => cases s <;> simp [totalOrderKey] at h
      | nan s q p => cases s <;> simp [totalOrderKey] at h
  | infinity s =>
      cases y with
      | finite d => cases s <;> simp [totalOrderKey] at h
      | infinity t => cases s <;> cases t <;> simp_all [totalOrderKey]
      | nan t q p => cases s <;> cases t <;> simp [totalOrderKey] at h
  | nan s q p =>
      cases y with
      | finite d => cases s <;> simp [totalOrderKey] at h
      | infinity t => cases s <;> cases t <;> simp [totalOrderKey] at h
      | nan t r n =>
          cases s <;> cases t <;> cases q <;> cases r <;>
            simp_all [totalOrderKey]

/-- The executable Boolean is precisely the mathematical order on exact coordinates. -/
@[simp] theorem totalOrder_eq_true_iff (x y : ExactValue) :
    totalOrder x y = true ↔ totalOrderKey x ≤ totalOrderKey y := by
  cases x with
  | finite a =>
      cases y with
      | finite b =>
          simp only [totalOrder, Numerics.Dyadic.Internal.compareScalable_eq_compare]
          cases hc : Numerics.Dyadic.compare a b with
          | lt =>
              have h := (Numerics.Dyadic.compare_eq_lt_iff a b).1 hc
              simp [totalOrderKey, Prod.Lex.toLex_le_toLex, h]
          | eq =>
              have h := (Numerics.Dyadic.compare_eq_eq_iff a b).1 hc
              simp [totalOrderKey, Prod.Lex.toLex_le_toLex, h]
          | gt =>
              have h := (Numerics.Dyadic.compare_eq_gt_iff a b).1 hc
              simp [totalOrderKey, Prod.Lex.toLex_le_toLex, not_lt_of_ge h.le, ne_of_gt h]
      | infinity s =>
          cases s <;> simp [totalOrder, totalOrderKey, Prod.Lex.toLex_le_toLex]
      | nan s q p =>
          cases s <;> simp [totalOrder, totalOrderKey, Prod.Lex.toLex_le_toLex]
  | infinity s =>
      cases s <;> cases y <;> simp [totalOrder, totalOrderKey, Prod.Lex.toLex_le_toLex]
  | nan s q p =>
      cases s <;> cases y <;> simp [totalOrder, totalOrderKey, Prod.Lex.toLex_le_toLex]

/-- Every complete datum precedes itself, including signaling NaNs. -/
@[simp] theorem totalOrder_refl (x : ExactValue) : totalOrder x x = true := by
  simp

/-- Any two complete data are comparable. -/
theorem totalOrder_total (x y : ExactValue) :
    totalOrder x y = true ∨ totalOrder y x = true := by
  simpa using le_total (totalOrderKey x) (totalOrderKey y)

/-- Exact total ordering is transitive, including all exceptional-value classes. -/
theorem totalOrder_trans {x y z : ExactValue}
    (hxy : totalOrder x y = true) (hyz : totalOrder y z = true) :
    totalOrder x z = true :=
  (totalOrder_eq_true_iff _ _).2
    (le_trans ((totalOrder_eq_true_iff _ _).1 hxy) ((totalOrder_eq_true_iff _ _).1 hyz))

/-- Mutual ordering identifies the complete datum, including NaN sign, class, and payload. -/
theorem totalOrder_antisymm {x y : ExactValue}
    (hxy : totalOrder x y = true) (hyx : totalOrder y x = true) : x = y :=
  totalOrderKey_injective
    (le_antisymm ((totalOrder_eq_true_iff _ _).1 hxy) ((totalOrder_eq_true_iff _ _).1 hyx))

/-- Mutual comparison is exactly equality of complete representations. -/
theorem totalOrder_both_iff (x y : ExactValue) :
    totalOrder x y = true ∧ totalOrder y x = true ↔ x = y := by
  constructor
  · rintro ⟨hxy, hyx⟩
    exact totalOrder_antisymm hxy hyx
  · rintro rfl
    simp

/--
Finite total order agrees with numerical order. Ties place negative signs first, then order
exponents upward for positive values and downward for negative values.
-/
theorem totalOrder_finite_iff (a b : Numerics.Dyadic) :
    totalOrder (.finite a) (.finite b) = true ↔
      a.toRat < b.toRat ∨ a.toRat = b.toRat ∧
        ((a.negative = true ∧ b.negative = false) ∨
          a.negative = b.negative ∧
            (if a.negative then b.exponent ≤ a.exponent else a.exponent ≤ b.exponent)) := by
  cases ha : a.negative <;> cases hb : b.negative <;>
    simp [totalOrderKey, finiteTotalOrderKey, Prod.Lex.toLex_le_toLex, ha, hb]

/-- Strict numerical increase always gives total ordering. -/
theorem totalOrder_finite_of_lt {a b : Numerics.Dyadic} (h : a.toRat < b.toRat) :
    totalOrder (.finite a) (.finite b) = true :=
  (totalOrder_finite_iff a b).2 (Or.inl h)

/-- Strict numerical decrease always fails total ordering. -/
theorem totalOrder_finite_eq_false_of_gt {a b : Numerics.Dyadic} (h : b.toRat < a.toRat) :
    totalOrder (.finite a) (.finite b) = false := by
  apply Bool.eq_false_iff.mpr
  intro horder
  rcases (totalOrder_finite_iff a b).1 horder with hlt | ⟨heq, _⟩
  · exact (not_lt_of_ge h.le) hlt
  · exact (ne_of_lt h) heq.symm

/-- For equal numerical values of the same sign, exponents break the tie. -/
theorem totalOrder_finite_of_value_eq
    {a b : Numerics.Dyadic} (hvalue : a.toRat = b.toRat) (hsign : a.negative = b.negative) :
    totalOrder (.finite a) (.finite b) = true ↔
      (if a.negative then b.exponent ≤ a.exponent else a.exponent ≤ b.exponent) := by
  rw [totalOrder_finite_iff]
  cases ha : a.negative <;> simp_all

/-- Negative zero precedes positive zero. -/
@[simp] theorem totalOrder_negZero_posZero (exponent : Int) :
    totalOrder (.finite ⟨true, 0, exponent⟩) (.finite ⟨false, 0, exponent⟩) = true := by
  rw [totalOrder_finite_iff]
  simp

/-- Positive zero does not precede negative zero. -/
@[simp] theorem totalOrder_posZero_negZero (exponent : Int) :
    totalOrder (.finite ⟨false, 0, exponent⟩) (.finite ⟨true, 0, exponent⟩) = false := by
  apply Bool.eq_false_iff.mpr
  rw [ne_eq, totalOrder_finite_iff]
  simp

/-- Every finite value lies strictly above negative infinity. -/
@[simp] theorem totalOrder_negInf_finite (d : Numerics.Dyadic) :
    totalOrder (.infinity true) (.finite d) = true := rfl

/-- A finite value cannot precede negative infinity. -/
@[simp] theorem totalOrder_finite_negInf (d : Numerics.Dyadic) :
    totalOrder (.finite d) (.infinity true) = false := rfl

/-- Every finite value lies strictly below positive infinity. -/
@[simp] theorem totalOrder_finite_posInf (d : Numerics.Dyadic) :
    totalOrder (.finite d) (.infinity false) = true := rfl

/-- Positive infinity cannot precede a finite value. -/
@[simp] theorem totalOrder_posInf_finite (d : Numerics.Dyadic) :
    totalOrder (.infinity false) (.finite d) = false := rfl

/-- Signed infinities follow their numerical order. -/
@[simp] theorem totalOrder_infinity (s t : Bool) :
    totalOrder (.infinity s) (.infinity t) = (s || !t) := by
  cases s <;> cases t <;> simp [totalOrder, totalOrderKey, Prod.Lex.toLex_le_toLex]

/-- A NaN precedes every finite number exactly when the NaN has negative sign. -/
@[simp] theorem totalOrder_nan_finite (s q : Bool) (p : Nat) (d : Numerics.Dyadic) :
    totalOrder (.nan s q p) (.finite d) = s := rfl

/-- Every finite number precedes a NaN exactly when that NaN has positive sign. -/
@[simp] theorem totalOrder_finite_nan (d : Numerics.Dyadic) (s q : Bool) (p : Nat) :
    totalOrder (.finite d) (.nan s q p) = !s := rfl

/-- NaN placement relative to infinity depends only on the NaN sign. -/
@[simp] theorem totalOrder_nan_infinity (s q : Bool) (p : Nat) (t : Bool) :
    totalOrder (.nan s q p) (.infinity t) = s := by
  cases s <;> cases t <;> simp [totalOrder, totalOrderKey, Prod.Lex.toLex_le_toLex]

/-- Infinity precedes precisely the positive NaNs. -/
@[simp] theorem totalOrder_infinity_nan (t s q : Bool) (p : Nat) :
    totalOrder (.infinity t) (.nan s q p) = !s := by
  cases s <;> cases t <;> simp [totalOrder, totalOrderKey, Prod.Lex.toLex_le_toLex]

/--
Complete NaN rule: sign first, then signaling before quiet for positive NaNs and the reverse
for negative NaNs, then FloatLib's ascending/descending payload convention.
-/
theorem totalOrder_nan_iff (s t q r : Bool) (p n : Nat) :
    totalOrder (.nan s q p) (.nan t r n) = true ↔
      (s = true ∧ t = false) ∨ s = t ∧
        (if s then
          (q = false ∧ r = true) ∨ q = r ∧ n ≤ p
        else
          (q = true ∧ r = false) ∨ q = r ∧ p ≤ n) := by
  cases s <;> cases t <;> cases q <;> cases r <;>
    simp [totalOrderKey, Prod.Lex.toLex_le_toLex]

/-- Positive NaN payloads increase within either NaN class. -/
theorem totalOrder_posNaN_payload (q : Bool) (p n : Nat) :
    totalOrder (.nan false q p) (.nan false q n) = true ↔ p ≤ n := by
  rw [totalOrder_nan_iff]
  simp

/-- Negative NaN payloads decrease within either NaN class. -/
theorem totalOrder_negNaN_payload (q : Bool) (p n : Nat) :
    totalOrder (.nan true q p) (.nan true q n) = true ↔ n ≤ p := by
  rw [totalOrder_nan_iff]
  simp

/-- Clearing a sign twice is the same as clearing it once. -/
@[simp] theorem abs_abs (x : ExactValue) : abs (abs x) = abs x := by
  cases x <;> rfl

/-- Magnitude order is reflexive even on NaNs. -/
@[simp] theorem totalOrderMag_refl (x : ExactValue) : totalOrderMag x x = true :=
  totalOrder_refl _

/-- Every pair of magnitudes is comparable. -/
theorem totalOrderMag_total (x y : ExactValue) :
    totalOrderMag x y = true ∨ totalOrderMag y x = true :=
  totalOrder_total _ _

/-- Magnitude ordering is transitive. -/
theorem totalOrderMag_trans {x y z : ExactValue}
    (hxy : totalOrderMag x y = true) (hyz : totalOrderMag y z = true) :
    totalOrderMag x z = true :=
  totalOrder_trans hxy hyz

/-- Mutual magnitude ordering identifies absolute data, retaining NaN class and payload. -/
theorem totalOrderMag_both_iff (x y : ExactValue) :
    totalOrderMag x y = true ∧ totalOrderMag y x = true ↔ abs x = abs y :=
  totalOrder_both_iff _ _

end FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
