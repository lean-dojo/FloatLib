/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.TotalOrder.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Comparison.Proof

/-!
# Total-order laws and IEEE decimal tie rules

Key injectivity establishes antisymmetry for full datums. The finite and NaN
theorems identify the numerical, cohort, sign and payload ordering rules; the
order laws alone would not establish agreement with those rules.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Datum

private theorem finiteValue_coefficient_injective (s : Bool) (q : Int) :
    Function.Injective (fun c : Nat => finiteValue s c q) := by
  intro c d h
  have hm := congrArg (fun x : ℚ => |x|) h
  rw [finiteValue_abs, finiteValue_abs] at hm
  have hp : (10 : ℚ) ^ q ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
  exact Nat.cast_injective (mul_right_cancel₀ hp hm)

/-- The ordering key loses no datum information, including NaN payloads or zero quanta. -/
theorem orderKey_injective : Function.Injective orderKey := by
  intro x y h
  cases x with
  | finite s c q =>
      cases y with
      | finite t d r =>
          cases s <;> cases t <;> simp [orderKey, Prod.mk.injEq] at h
          all_goals
            rcases h with ⟨hv, rfl⟩
            congr 1
            exact finiteValue_coefficient_injective _ _ hv
      | infinity t => cases s <;> cases t <;> simp [orderKey] at h
      | nan t u p => cases s <;> cases t <;> simp [orderKey] at h
  | infinity s =>
      cases y with
      | finite t d r => cases s <;> cases t <;> simp [orderKey] at h
      | infinity t => cases s <;> cases t <;> simp_all [orderKey]
      | nan t u p => cases s <;> cases t <;> simp [orderKey] at h
  | nan s t p =>
      cases y with
      | finite u d r => cases s <;> cases u <;> simp [orderKey] at h
      | infinity u => cases s <;> cases u <;> simp [orderKey] at h
      | nan u v k =>
          cases s <;> cases u <;> cases t <;> cases v <;> simp_all [orderKey]

@[simp] theorem totalOrder_self (x : Datum) : x.totalOrder x = true := by
  simp [totalOrder]

theorem totalOrder_trans {x y z : Datum}
    (hxy : x.totalOrder y = true) (hyz : y.totalOrder z = true) :
    x.totalOrder z = true :=
  decide_eq_true (le_trans (of_decide_eq_true hxy) (of_decide_eq_true hyz))

theorem totalOrder_total (x y : Datum) :
    x.totalOrder y = true ∨ y.totalOrder x = true := by
  simpa only [totalOrder, decide_eq_true_eq] using le_total x.orderKey y.orderKey

/-- Both directions hold precisely when the complete datums are identical. -/
theorem totalOrder_antisymm_iff (x y : Datum) :
    (x.totalOrder y = true ∧ y.totalOrder x = true) ↔ x = y := by
  simp only [totalOrder, decide_eq_true_eq, le_antisymm_iff.symm]
  exact orderKey_injective.eq_iff

/-- On positive finite datums, numerical value precedes increasing quantum. -/
theorem totalOrder_positive_finite_iff (c d : Nat) (q r : Int) :
    (.finite false c q : Datum).totalOrder (.finite false d r) = true ↔
      finiteValue false c q < finiteValue false d r ∨
        finiteValue false c q = finiteValue false d r ∧ q ≤ r := by
  simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]

/-- On negative finite datums, increasing numerical value precedes decreasing quantum. -/
theorem totalOrder_negative_finite_iff (c d : Nat) (q r : Int) :
    (.finite true c q : Datum).totalOrder (.finite true d r) = true ↔
      finiteValue true c q < finiteValue true d r ∨
        finiteValue true c q = finiteValue true d r ∧ r ≤ q := by
  simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]

/-- Negative finite datums precede positive ones, including the two zero signs. -/
@[simp] theorem totalOrder_negative_positive (c d : Nat) (q r : Int) :
    (.finite true c q : Datum).totalOrder (.finite false d r) = true := by
  simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]

@[simp] theorem totalOrder_positive_negative (c d : Nat) (q r : Int) :
    (.finite false c q : Datum).totalOrder (.finite true d r) = false := by
  simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]

/-- The quantum tie rule applies to signed zero as well as nonzero cohorts. -/
theorem totalOrder_zero_iff (s : Bool) (q r : Int) :
    (.finite s 0 q : Datum).totalOrder (.finite s 0 r) = true ↔
      if s then r ≤ q else q ≤ r := by
  cases s <;>
    simp [totalOrder_positive_finite_iff, totalOrder_negative_finite_iff, finiteValue]

/-- Positive signaling NaNs precede quiet NaNs regardless of payload. -/
@[simp] theorem totalOrder_positive_signaling_quiet (p k : Nat) :
    (.nan false true p : Datum).totalOrder (.nan false false k) = true := by
  simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]

/-- Negative quiet NaNs precede signaling NaNs regardless of payload. -/
@[simp] theorem totalOrder_negative_quiet_signaling (p k : Nat) :
    (.nan true false p : Datum).totalOrder (.nan true true k) = true := by
  simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]

/-- This implementation's equal-kind NaN payload order reverses with the sign.
IEEE 754-2019 §5.10(d)(5)(iii) permits this choice. -/
theorem totalOrder_nan_payload_iff (s t : Bool) (p k : Nat) :
    (.nan s t p : Datum).totalOrder (.nan s t k) = true ↔
      if s then k ≤ p else p ≤ k := by
  cases s <;> cases t <;> simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]

/-- Every negative NaN precedes every positive NaN, irrespective of kind or payload. -/
@[simp] theorem totalOrder_negative_positive_nan (t u : Bool) (p k : Nat) :
    (.nan true t p : Datum).totalOrder (.nan false u k) = true := by
  simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]

theorem totalOrder_negative_nan_numeric (t : Bool) (p : Nat) (x : Datum)
    (hx : x.isNaN = false) :
    (.nan true t p : Datum).totalOrder x = true := by
  cases x with
  | finite s c q => cases s <;> simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]
  | infinity s => cases s <;> simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]
  | nan s u k => simp [isNaN] at hx

theorem totalOrder_numeric_positive_nan (t : Bool) (p : Nat) (x : Datum)
    (hx : x.isNaN = false) :
    x.totalOrder (.nan false t p) = true := by
  cases x with
  | finite s c q => cases s <;> simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]
  | infinity s => cases s <;> simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]
  | nan s u k => simp [isNaN] at hx

@[simp] theorem totalOrder_negative_infinity_finite (s : Bool) (c : Nat) (q : Int) :
    (.infinity true : Datum).totalOrder (.finite s c q) = true := by
  cases s <;> simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]

@[simp] theorem totalOrder_finite_positive_infinity (s : Bool) (c : Nat) (q : Int) :
    (.finite s c q : Datum).totalOrder (.infinity false) = true := by
  cases s <;> simp [totalOrder, orderKey, Prod.Lex.toLex_le_toLex]

@[simp] theorem totalOrderMag_self (x : Datum) : x.totalOrderMag x = true :=
  totalOrder_self x.abs

theorem totalOrderMag_trans {x y z : Datum}
    (hxy : x.totalOrderMag y = true) (hyz : y.totalOrderMag z = true) :
    x.totalOrderMag z = true := totalOrder_trans hxy hyz

theorem totalOrderMag_total (x y : Datum) :
    x.totalOrderMag y = true ∨ y.totalOrderMag x = true :=
  totalOrder_total x.abs y.abs

/-- Magnitude ordering identifies precisely datums differing at most in sign. -/
theorem totalOrderMag_antisymm_iff (x y : Datum) :
    (x.totalOrderMag y = true ∧ y.totalOrderMag x = true) ↔ x.abs = y.abs :=
  totalOrder_antisymm_iff x.abs y.abs

end FloatLib.Floats.Formats.DecimalInterchange.Datum
