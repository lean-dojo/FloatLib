/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.KernelPath.Arithmetic
public import FloatLib.Floats.Formats.P3109.Arithmetic.Extrema.Runtime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The kernel P3109 comparisons and extrema compute the reference ones

P3109 Interim Report v4.1 (14 September 2026), §§4.11 and 4.12, an unapproved draft. The
comparisons and the extrema of the report act on classes and ratios of natural numbers with no
normalization: two ratios are compared on their cross products.

* `compareLess_closed`, `compareEqual_closed`: `Arithmetic.CompareLess` and `CompareEqual` on
  closed values given by class, sign and ratio are `lessOf` and `equalOf`, false for a NaN
  operand.
* `minimum_closed`, `maximum_closed`, `minimumMagnitude_closed`, `maximumMagnitude_closed`: the
  four extrema that propagate NaN select the operand that `baseSel` names, as the two cases of
  `order_closed` and of `magnitude_closed`.
  `numberVariant_closed` and `finiteVariant_closed` carry a selection through the number variant
  and the finite variant, so each of the ten extrema of §4.11 selects the operand that
  `extremumSel` names. `clamp_closed`: the clamp of §4.11.4.
* `compareLess_eq`, `compareEqual_eq`, `compareLessEqual_eq`, `compareGreater_eq`,
  `compareGreaterEqual_eq`: the five comparisons of two encodings of independent formats.
* `binary_eq_extremum`: an operation that selects on closed values (`Selects`) is `extremum` on
  encodings, projected once. `minimum_selects`, `maximum_selects`, `minimumMagnitude_selects`
  and `maximumMagnitude_selects`, with `Selects.number` and `Selects.finite`, are the ten
  extrema, and `clamp_eq` is the clamp, for every descriptor of every operand and of the
  destination, every rounding mode with every random word and every saturation mode.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.KernelPath

open FloatLib.Numerics FloatLib.Numerics.Kernel
open FloatLib.Floats.Formats.P3109

/-! ## Comparisons of signed ratios -/

/-- A signed numerator times a natural number. -/
theorem signed_mul (s n e : Nat) :
    (if s = 0 then (n : Rat) else -(n : Rat)) * (e : Rat) =
      if s = 0 then ((n * e : Nat) : Rat) else -((n * e : Nat) : Rat) := by
  split_ifs <;> push_cast <;> ring

/-- `ratioLess` on natural numbers. -/
theorem ratioLess_true_iff (sa sb x y : Nat) :
    ratioLess sa sb x y = true ↔
      (sa = sb ∧ ((sa = 0 ∧ x < y) ∨ (sa ≠ 0 ∧ y < x))) ∨ (sa ≠ sb ∧ sa = 1 ∧ 0 < x + y) := by
  unfold ratioLess
  kernel_notation
  split_ifs <;> simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] <;> omega

/-- `ratioLess` is the strict order of the two signed numbers. -/
theorem ratioLess_iff (sa sb x y : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1) :
    ratioLess sa sb x y = true ↔
      (if sa = 0 then (x : Rat) else -(x : Rat)) <
        (if sb = 0 then (y : Rat) else -(y : Rat)) := by
  have : (0 : Rat) ≤ (x : Rat) := Nat.cast_nonneg x
  have : (0 : Rat) ≤ (y : Rat) := Nat.cast_nonneg y
  rw [ratioLess_true_iff]
  by_cases ha : sa = 0 <;> by_cases hb : sb = 0
  · rw [ite_eq_left ha, ite_eq_left hb]
    constructor
    · intro h
      have : x < y := by omega
      exact_mod_cast this
    · intro h
      have : x < y := by exact_mod_cast h
      omega
  · rw [ite_eq_left ha, ite_eq_right hb]
    constructor
    · intro h
      omega
    · intro h
      linarith
  · rw [ite_eq_right ha, ite_eq_left hb]
    constructor
    · intro h
      have h1 : 0 < x + y := by omega
      have : (0 : Rat) < (x : Rat) + (y : Rat) := by exact_mod_cast h1
      linarith
    · intro h
      have : 0 < x + y := by
        by_contra hc
        have hx0 : x = 0 := by omega
        have hy0 : y = 0 := by omega
        rw [hx0, hy0] at h
        simp at h
      omega
  · rw [ite_eq_right ha, ite_eq_right hb, neg_lt_neg_iff]
    constructor
    · intro h
      have : y < x := by omega
      exact_mod_cast this
    · intro h
      have : y < x := by exact_mod_cast h
      omega

/-- `ratioEqual` on natural numbers. -/
theorem ratioEqual_true_iff (sa sb x y : Nat) :
    ratioEqual sa sb x y = true ↔ (sa = sb ∧ x = y) ∨ (sa ≠ sb ∧ x + y = 0) := by
  unfold ratioEqual
  kernel_notation
  split_ifs <;> simp only [Nat.beq_eq] <;> omega

/-- `ratioEqual` is the equality of the two signed numbers. -/
theorem ratioEqual_iff (sa sb x y : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1) :
    ratioEqual sa sb x y = true ↔
      (if sa = 0 then (x : Rat) else -(x : Rat)) =
        (if sb = 0 then (y : Rat) else -(y : Rat)) := by
  have : (0 : Rat) ≤ (x : Rat) := Nat.cast_nonneg x
  have : (0 : Rat) ≤ (y : Rat) := Nat.cast_nonneg y
  rw [ratioEqual_true_iff]
  by_cases ha : sa = 0 <;> by_cases hb : sb = 0
  · rw [ite_eq_left ha, ite_eq_left hb]
    constructor
    · intro h
      have : x = y := by omega
      rw [this]
    · intro h
      have : x = y := by exact_mod_cast h
      omega
  · rw [ite_eq_left ha, ite_eq_right hb]
    constructor
    · intro h
      have hx0 : x = 0 := by omega
      have hy0 : y = 0 := by omega
      rw [hx0, hy0]
      simp
    · intro h
      have h1 : (x : Rat) + (y : Rat) = 0 := by linarith
      have : x + y = 0 := by exact_mod_cast h1
      omega
  · rw [ite_eq_right ha, ite_eq_left hb]
    constructor
    · intro h
      have hx0 : x = 0 := by omega
      have hy0 : y = 0 := by omega
      rw [hx0, hy0]
      simp
    · intro h
      have h1 : (x : Rat) + (y : Rat) = 0 := by linarith
      have : x + y = 0 := by exact_mod_cast h1
      omega
  · rw [ite_eq_right ha, ite_eq_right hb, neg_inj]
    constructor
    · intro h
      have : x = y := by omega
      rw [this]
    · intro h
      have : x = y := by exact_mod_cast h
      omega

/-- Two signed ratios with nonzero denominators compare as their cross products. -/
theorem ratio_lt_iff (sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1) (hda : da ≠ 0)
    (hdb : db ≠ 0) :
    (if sa = 0 then (na : Rat) else -(na : Rat)) / (da : Rat) <
        (if sb = 0 then (nb : Rat) else -(nb : Rat)) / (db : Rat) ↔
      ratioLess sa sb (na * db) (nb * da) = true := by
  have hda' : (0 : Rat) < (da : Rat) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hda)
  have hdb' : (0 : Rat) < (db : Rat) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdb)
  rw [div_lt_iff₀ hda', div_mul_eq_mul_div, lt_div_iff₀ hdb', signed_mul, signed_mul,
    ratioLess_iff _ _ _ _ hsa hsb]

/-- Two signed ratios with nonzero denominators are equal when their cross products are. -/
theorem ratio_eq_iff (sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1) (hda : da ≠ 0)
    (hdb : db ≠ 0) :
    (if sa = 0 then (na : Rat) else -(na : Rat)) / (da : Rat) =
        (if sb = 0 then (nb : Rat) else -(nb : Rat)) / (db : Rat) ↔
      ratioEqual sa sb (na * db) (nb * da) = true := by
  have hda' : (da : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hda
  have hdb' : (db : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hdb
  rw [div_eq_iff hda', div_mul_eq_mul_div, eq_div_iff hdb', signed_mul, signed_mul,
    ratioEqual_iff _ _ _ _ hsa hsb]

/-! ## Comparisons of closed values -/

/-- The kernel test of equality is the decision of the equality. -/
theorem beq_eq_decide (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_eq]

/-- The kernel test of the order is the decision of the order. -/
theorem ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]

/-- `lessOf` with the notation of the library. -/
theorem lessOf_eq (ca cb sa sb x y : Nat) :
    lessOf ca cb sa sb x y =
      if 3 ≤ ca ∨ 3 ≤ cb then false
      else if ca = 0 then (if cb = 0 then ratioLess sa sb x y else decide (cb = 1))
      else (decide (ca = 2) && decide (cb ≤ 1)) := by
  unfold lessOf
  kernel_notation
  simp only [Bool.or_eq_true, beq_eq_decide, ble_eq_decide, decide_eq_true_eq]

/-- `equalOf` with the notation of the library. -/
theorem equalOf_eq (ca cb sa sb x y : Nat) :
    equalOf ca cb sa sb x y =
      if 3 ≤ ca ∨ 3 ≤ cb then false
      else if ca = 0 then (decide (cb = 0) && ratioEqual sa sb x y)
      else decide (ca = cb) := by
  unfold equalOf
  kernel_notation
  simp only [Bool.or_eq_true, beq_eq_decide, ble_eq_decide, decide_eq_true_eq]

set_option hygiene false in
/--
`closed_classes Op [lemmas]` proves an equation between the operation `Op` on the closed values
of the classes `ca` and `cb` and a function of the classes, by the sixteen pairs of classes:
`simp` with the definition of `Op` and the lemmas decides a pair of classes below three, and a
class of at least three makes its operand NaN.
-/
local macro "closed_classes " op:ident "[" lemmas:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    unfold closed
    rcases (by omega : ca = 0 ∨ ca = 1 ∨ ca = 2 ∨ 3 ≤ ca) with rfl | rfl | rfl | ha <;>
      rcases (by omega : cb = 0 ∨ cb = 1 ∨ cb = 2 ∨ 3 ≤ cb) with rfl | rfl | rfl | hb
    all_goals first
      | (simp [$op:ident, Arithmetic.nan, $lemmas,*]; done)
      | (have h1 : ¬ca = 0 := by omega
         have h2 : ¬ca = 1 := by omega
         have h3 : ¬ca = 2 := by omega
         simp [$op:ident, Arithmetic.nan, h1, h2, h3, ha])
      | (have h1 : ¬cb = 0 := by omega
         have h2 : ¬cb = 1 := by omega
         have h3 : ¬cb = 2 := by omega
         simp [$op:ident, Arithmetic.nan, h1, h2, h3, hb])))

/--
P3109 interim report v4.1, §4.12: `Arithmetic.CompareLess` on two closed values given by class,
sign and ratio is `lessOf` on the classes, the signs and the cross products of the ratios.
-/
theorem compareLess_closed (ca cb sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1)
    (hda : da ≠ 0) (hdb : db ≠ 0) :
    Arithmetic.CompareLess (closed ca sa na da) (closed cb sb nb db) =
      lessOf ca cb sa sb (na * db) (nb * da) := by
  have hratio := ratio_lt_iff sa sb na nb da db hsa hsb hda hdb
  rw [lessOf_eq]
  closed_classes Arithmetic.CompareLess [hratio]

/--
P3109 interim report v4.1, §4.12: `Arithmetic.CompareEqual` on two closed values given by class,
sign and ratio is `equalOf` on the classes, the signs and the cross products of the ratios.
-/
theorem compareEqual_closed (ca cb sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1)
    (hda : da ≠ 0) (hdb : db ≠ 0) :
    Arithmetic.CompareEqual (closed ca sa na da) (closed cb sb nb db) =
      equalOf ca cb sa sb (na * db) (nb * da) := by
  have hratio := ratio_eq_iff sa sb na nb da db hsa hsb hda hdb
  rw [equalOf_eq]
  closed_classes Arithmetic.CompareEqual [_root_.beq_eq_decide, hratio]

/-! ## Selections -/

/-- The closed value that the selector `k` names among two closed values: the first for zero,
the second for one and NaN for any other selector. -/
def selected (k ca cb sa sb na nb da db : Nat) : NumericalValue Rat :=
  closed (pickOf k ca cb 3) (pickOf k sa sb 0) (pickOf k na nb 0) (pickOf k da db 1)

/-- `pickOf` with the notation of the library. -/
theorem pickOf_eq (k a b z : Nat) :
    pickOf k a b z = if k = 0 then a else if k = 1 then b else z := by
  unfold pickOf
  kernel_notation

/-- A selection among two sign bits is a sign bit. -/
theorem pickOf_le_one (k : Nat) {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : pickOf k a b 0 ≤ 1 := by
  rw [pickOf_eq]
  split_ifs <;> omega

/-- A selection among two nonzero denominators is not zero. -/
theorem pickOf_ne_zero (k : Nat) {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) : pickOf k a b 1 ≠ 0 := by
  rw [pickOf_eq]
  split_ifs <;> omega

/-- The selected closed value, by cases on the selector. -/
theorem selected_eq (k ca cb sa sb na nb da db : Nat) :
    selected k ca cb sa sb na nb da db =
      if k = 0 then closed ca sa na da else if k = 1 then closed cb sb nb db
      else Arithmetic.nan := by
  unfold selected
  simp only [pickOf_eq]
  by_cases h0 : k = 0
  · simp [h0]
  · by_cases h1 : k = 1
    · simp [h1]
    · simp [h0, h1, closed]

/-- The closed value of a class of at least three is NaN. -/
theorem closed_nan {c : Nat} (hc : 3 ≤ c) (s n d : Nat) : closed c s n d = Arithmetic.nan := by
  have h0 : ¬c = 0 := by omega
  have h1 : ¬c = 1 := by omega
  have h2 : ¬c = 2 := by omega
  simp [closed, h0, h1, h2]

/-- The closed value of a class below three is not exceptional. -/
theorem closed_ne_exceptional {c : Nat} (hc : c < 3) (s n d : Nat) (e : ExceptionalValue) :
    closed c s n d ≠ .exceptional e := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> simp [closed]

/-- NaN, or a closed value, as one closed value. -/
theorem ite_nan_closed (g : Bool) (c s n d : Nat) :
    (if g = true then Arithmetic.nan else closed c s n d) =
      closed (if g = true then 3 else c) s n d := by
  cases g <;> simp [closed]

/-- `orderSel` with the notation of the library. -/
theorem orderSel_eq (mx : Nat) (less : Bool) :
    orderSel mx less = if less = true then mx else 1 - mx := by
  unfold orderSel
  kernel_notation

/-- `absClass` with the notation of the library. -/
theorem absClass_eq (c : Nat) : absClass c = if c = 2 then 1 else c := by
  unfold absClass
  kernel_notation

/-- `baseSel` with the notation of the library. -/
theorem baseSel_eq (mx mag ca cb sa sb x y : Nat) :
    baseSel mx mag ca cb sa sb x y =
      if 3 ≤ ca ∨ 3 ≤ cb then 2
      else if mag = 0 then orderSel mx (lessOf ca cb sa sb x y)
      else if lessOf (absClass ca) (absClass cb) 0 0 x y = true then mx
      else if lessOf (absClass cb) (absClass ca) 0 0 y x = true then 1 - mx
      else orderSel mx (lessOf ca cb sa sb x y) := by
  unfold baseSel
  kernel_notation
  simp only [Bool.or_eq_true, Nat.ble_eq]

/-- `numberSel` with the notation of the library. -/
theorem numberSel_eq (var ca cb k : Nat) :
    numberSel var ca cb k =
      if var = 0 then k
      else if 3 ≤ ca then (if 3 ≤ cb then 2 else 1) else if 3 ≤ cb then 0 else k := by
  unfold numberSel
  kernel_notation

/-- `finiteSel` with the notation of the library. -/
theorem finiteSel_eq (var ca cb k : Nat) :
    finiteSel var ca cb k =
      if var = 2 then
        (if ca = 0 ∧ (cb = 1 ∨ cb = 2) then 0 else if (ca = 1 ∨ ca = 2) ∧ cb = 0 then 1 else k)
      else k := by
  unfold finiteSel
  kernel_notation
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq]

/-! ## The extrema on values that are not NaN -/

/-- The minimum of two values that are not NaN. -/
theorem minimum_of_ne (l r : NumericalValue Rat) (hl : ∀ e, l ≠ .exceptional e)
    (hr : ∀ e, r ≠ .exceptional e) :
    Arithmetic.Minimum l r = if Arithmetic.CompareLess l r = true then l else r := by
  cases l <;> cases r <;> first | rfl | exact absurd rfl (hl _) | exact absurd rfl (hr _)

/-- The maximum of two values that are not NaN. -/
theorem maximum_of_ne (l r : NumericalValue Rat) (hl : ∀ e, l ≠ .exceptional e)
    (hr : ∀ e, r ≠ .exceptional e) :
    Arithmetic.Maximum l r = if Arithmetic.CompareLess l r = true then r else l := by
  cases l <;> cases r <;> first | rfl | exact absurd rfl (hl _) | exact absurd rfl (hr _)

/-- The minimum by magnitude, on the comparisons of the magnitudes. -/
theorem minimumMagnitude_eq_ite (l r : NumericalValue Rat) :
    Arithmetic.MinimumMagnitude l r =
      if Arithmetic.CompareLess (Arithmetic.Abs l) (Arithmetic.Abs r) = true then l
      else if Arithmetic.CompareLess (Arithmetic.Abs r) (Arithmetic.Abs l) = true then r
      else Arithmetic.Minimum l r := by
  cases l <;> cases r <;> rfl

/-- The maximum by magnitude, on the comparisons of the magnitudes. -/
theorem maximumMagnitude_eq_ite (l r : NumericalValue Rat) :
    Arithmetic.MaximumMagnitude l r =
      if Arithmetic.CompareLess (Arithmetic.Abs l) (Arithmetic.Abs r) = true then r
      else if Arithmetic.CompareLess (Arithmetic.Abs r) (Arithmetic.Abs l) = true then l
      else Arithmetic.Maximum l r := by
  cases l <;> cases r <;> rfl

/-- The four extrema that propagate NaN give NaN for a NaN first operand. -/
theorem extrema_nan_left (r : NumericalValue Rat) :
    Arithmetic.Minimum Arithmetic.nan r = Arithmetic.nan ∧
      Arithmetic.Maximum Arithmetic.nan r = Arithmetic.nan ∧
      Arithmetic.MinimumMagnitude Arithmetic.nan r = Arithmetic.nan ∧
      Arithmetic.MaximumMagnitude Arithmetic.nan r = Arithmetic.nan := by
  cases r <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The four extrema that propagate NaN give NaN for a NaN second operand. -/
theorem extrema_nan_right (l : NumericalValue Rat) :
    Arithmetic.Minimum l Arithmetic.nan = Arithmetic.nan ∧
      Arithmetic.Maximum l Arithmetic.nan = Arithmetic.nan ∧
      Arithmetic.MinimumMagnitude l Arithmetic.nan = Arithmetic.nan ∧
      Arithmetic.MaximumMagnitude l Arithmetic.nan = Arithmetic.nan := by
  cases l <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The extrema of closed values -/

/-- An operation that gives NaN for a NaN operand selects NaN on closed values with a NaN
class. -/
theorem selected_of_nan (op : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (hleft : ∀ r, op Arithmetic.nan r = Arithmetic.nan)
    (hright : ∀ l, op l Arithmetic.nan = Arithmetic.nan) (ca cb sa sb na nb da db : Nat)
    (hnan : 3 ≤ ca ∨ 3 ≤ cb) :
    op (closed ca sa na da) (closed cb sb nb db) = selected 2 ca cb sa sb na nb da db := by
  have hsel : selected 2 ca cb sa sb na nb da db = Arithmetic.nan := by
    rw [selected_eq]
    simp
  rw [hsel]
  rcases hnan with h | h
  · rw [closed_nan h, hleft]
  · rw [closed_nan h, hright]

/--
An operation that gives NaN for a NaN operand, and on other values the lesser operand for
`mx = 0` or the greater for `mx = 1`, the second at equal operands of a minimum and the first of
a maximum, selects on two closed values the operand that `baseSel mx 0` names.
-/
theorem order_closed {op : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat}
    {mx : Nat} (hmx : mx ≤ 1) (hleft : ∀ r, op Arithmetic.nan r = Arithmetic.nan)
    (hright : ∀ l, op l Arithmetic.nan = Arithmetic.nan)
    (hop : ∀ l r, (∀ e, l ≠ .exceptional e) → (∀ e, r ≠ .exceptional e) →
      op l r = if Arithmetic.CompareLess l r = true then (if mx = 0 then l else r)
        else (if mx = 0 then r else l))
    (ca cb sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1) (hda : da ≠ 0)
    (hdb : db ≠ 0) :
    op (closed ca sa na da) (closed cb sb nb db) =
      selected (baseSel mx 0 ca cb sa sb (na * db) (nb * da)) ca cb sa sb na nb da db := by
  rw [baseSel_eq]
  by_cases hnan : 3 ≤ ca ∨ 3 ≤ cb
  · rw [ite_eq_left hnan]
    exact selected_of_nan _ hleft hright _ _ _ _ _ _ _ _ hnan
  · rw [ite_eq_right hnan, ite_eq_left rfl, orderSel_eq, selected_eq,
      hop _ _ (closed_ne_exceptional (by omega) _ _ _) (closed_ne_exceptional (by omega) _ _ _),
      compareLess_closed _ _ _ _ _ _ _ _ hsa hsb hda hdb]
    rcases (by omega : mx = 0 ∨ mx = 1) with rfl | rfl <;>
      by_cases hlt : lessOf ca cb sa sb (na * db) (nb * da) = true <;> simp [hlt]

/--
P3109 interim report v4.1, §4.11.1: `Arithmetic.Minimum` on two closed values given by class,
sign and ratio is the operand that `baseSel 0 0` names, NaN for a NaN operand.
-/
theorem minimum_closed (ca cb sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1)
    (hda : da ≠ 0) (hdb : db ≠ 0) :
    Arithmetic.Minimum (closed ca sa na da) (closed cb sb nb db) =
      selected (baseSel 0 0 ca cb sa sb (na * db) (nb * da)) ca cb sa sb na nb da db :=
  order_closed (Nat.zero_le 1) (fun r => (extrema_nan_left r).1)
    (fun l => (extrema_nan_right l).1) minimum_of_ne ca cb sa sb na nb da db hsa hsb hda hdb

/--
P3109 interim report v4.1, §4.11.1: `Arithmetic.Maximum` on two closed values given by class,
sign and ratio is the operand that `baseSel 1 0` names, NaN for a NaN operand.
-/
theorem maximum_closed (ca cb sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1)
    (hda : da ≠ 0) (hdb : db ≠ 0) :
    Arithmetic.Maximum (closed ca sa na da) (closed cb sb nb db) =
      selected (baseSel 1 0 ca cb sa sb (na * db) (nb * da)) ca cb sa sb na nb da db :=
  order_closed (Nat.le_refl 1) (fun r => (extrema_nan_left r).2.1)
    (fun l => (extrema_nan_right l).2.1) maximum_of_ne ca cb sa sb na nb da db hsa hsb hda hdb

/--
An operation that gives NaN for a NaN operand, and on other values the operand of lesser
magnitude for `mx = 0` or of greater magnitude for `mx = 1`, and at equal magnitudes what `base`
gives, selects on two closed values the operand that `baseSel mx 1` names, when `base` selects
the one that `baseSel mx 0` names.
-/
theorem magnitude_closed {op base : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat}
    {mx : Nat} (hmx : mx ≤ 1) (hleft : ∀ r, op Arithmetic.nan r = Arithmetic.nan)
    (hright : ∀ l, op l Arithmetic.nan = Arithmetic.nan)
    (hop : ∀ l r, op l r =
      if Arithmetic.CompareLess (Arithmetic.Abs l) (Arithmetic.Abs r) = true then
        (if mx = 0 then l else r)
      else if Arithmetic.CompareLess (Arithmetic.Abs r) (Arithmetic.Abs l) = true then
        (if mx = 0 then r else l)
      else base l r)
    (hbase : ∀ ca cb sa sb na nb da db : Nat, sa ≤ 1 → sb ≤ 1 → da ≠ 0 → db ≠ 0 →
      base (closed ca sa na da) (closed cb sb nb db) =
        selected (baseSel mx 0 ca cb sa sb (na * db) (nb * da)) ca cb sa sb na nb da db)
    (ca cb sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1) (hda : da ≠ 0)
    (hdb : db ≠ 0) :
    op (closed ca sa na da) (closed cb sb nb db) =
      selected (baseSel mx 1 ca cb sa sb (na * db) (nb * da)) ca cb sa sb na nb da db := by
  rw [baseSel_eq]
  by_cases hnan : 3 ≤ ca ∨ 3 ≤ cb
  · rw [ite_eq_left hnan]
    exact selected_of_nan _ hleft hright _ _ _ _ _ _ _ _ hnan
  · rw [ite_eq_right hnan, ite_eq_right Nat.one_ne_zero, orderSel_eq, selected_eq,
      hop, abs_closed, abs_closed,
      compareLess_closed _ _ _ _ _ _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) hda hdb,
      compareLess_closed _ _ _ _ _ _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) hdb hda,
      hbase _ _ _ _ _ _ _ _ hsa hsb hda hdb, baseSel_eq, ite_eq_right hnan,
      ite_eq_left rfl, orderSel_eq, selected_eq, absClass_eq, absClass_eq]
    rcases (by omega : mx = 0 ∨ mx = 1) with rfl | rfl <;>
      by_cases h1 : lessOf (if ca = 2 then 1 else ca) (if cb = 2 then 1 else cb) 0 0 (na * db)
          (nb * da) = true <;>
      by_cases h2 : lessOf (if cb = 2 then 1 else cb) (if ca = 2 then 1 else ca) 0 0 (nb * da)
          (na * db) = true <;>
      by_cases h3 : lessOf ca cb sa sb (na * db) (nb * da) = true <;> simp [h1, h2, h3]

/--
P3109 interim report v4.1, §4.11.2: `Arithmetic.MinimumMagnitude` on two closed values given by
class, sign and ratio is the operand that `baseSel 0 1` names: the one of smaller magnitude, the
minimum at equal magnitudes, and NaN for a NaN operand.
-/
theorem minimumMagnitude_closed (ca cb sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1)
    (hda : da ≠ 0) (hdb : db ≠ 0) :
    Arithmetic.MinimumMagnitude (closed ca sa na da) (closed cb sb nb db) =
      selected (baseSel 0 1 ca cb sa sb (na * db) (nb * da)) ca cb sa sb na nb da db :=
  magnitude_closed (Nat.zero_le 1) (fun r => (extrema_nan_left r).2.2.1)
    (fun l => (extrema_nan_right l).2.2.1) minimumMagnitude_eq_ite minimum_closed
    ca cb sa sb na nb da db hsa hsb hda hdb

/--
P3109 interim report v4.1, §4.11.2: `Arithmetic.MaximumMagnitude` on two closed values given by
class, sign and ratio is the operand that `baseSel 1 1` names: the one of larger magnitude, the
maximum at equal magnitudes, and NaN for a NaN operand.
-/
theorem maximumMagnitude_closed (ca cb sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1)
    (hda : da ≠ 0) (hdb : db ≠ 0) :
    Arithmetic.MaximumMagnitude (closed ca sa na da) (closed cb sb nb db) =
      selected (baseSel 1 1 ca cb sa sb (na * db) (nb * da)) ca cb sa sb na nb da db :=
  magnitude_closed (Nat.le_refl 1) (fun r => (extrema_nan_left r).2.2.2)
    (fun l => (extrema_nan_right l).2.2.2) maximumMagnitude_eq_ite maximum_closed
    ca cb sa sb na nb da db hsa hsb hda hdb

/--
P3109 interim report v4.1, §4.11.1: the number variant of an operation that selects `k` on two
closed values selects `numberSel var … k` for `var ≠ 0`: the other operand for a single NaN.
-/
theorem numberVariant_closed
    (op : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (var k ca cb sa sb na nb da db : Nat) (hvar : var ≠ 0)
    (h : op (closed ca sa na da) (closed cb sb nb db) = selected k ca cb sa sb na nb da db) :
    Arithmetic.numberVariant op (closed ca sa na da) (closed cb sb nb db) =
      selected (numberSel var ca cb k) ca cb sa sb na nb da db := by
  rw [numberSel_eq, ite_eq_right hvar]
  by_cases ha : 3 ≤ ca <;> by_cases hb : 3 ≤ cb
  · rw [ite_eq_left ha, ite_eq_left hb, selected_eq, closed_nan ha, closed_nan hb]
    simp [Arithmetic.numberVariant, Arithmetic.nan]
  · rw [ite_eq_left ha, ite_eq_right hb, selected_eq, closed_nan ha]
    have hne := closed_ne_exceptional (Nat.lt_of_not_le hb) sb nb db
    generalize closed cb sb nb db = r at hne ⊢
    cases r with
    | finite _ => simp [Arithmetic.numberVariant, Arithmetic.nan]
    | infinity _ => simp [Arithmetic.numberVariant, Arithmetic.nan]
    | exceptional _ => exact absurd rfl (hne _)
  · rw [ite_eq_right ha, ite_eq_left hb, selected_eq, closed_nan hb]
    have hne := closed_ne_exceptional (Nat.lt_of_not_le ha) sa na da
    generalize closed ca sa na da = l at hne ⊢
    cases l with
    | finite _ => simp [Arithmetic.numberVariant, Arithmetic.nan]
    | infinity _ => simp [Arithmetic.numberVariant, Arithmetic.nan]
    | exceptional _ => exact absurd rfl (hne _)
  · rw [ite_eq_right ha, ite_eq_right hb, ← h]
    have hl := closed_ne_exceptional (Nat.lt_of_not_le ha) sa na da
    have hr := closed_ne_exceptional (Nat.lt_of_not_le hb) sb nb db
    generalize closed ca sa na da = l at hl ⊢
    generalize closed cb sb nb db = r at hr ⊢
    cases l <;> cases r <;> first | rfl | exact absurd rfl (hl _) | exact absurd rfl (hr _)

/--
P3109 interim report v4.1, §4.11.3: the finite variant of an operation that selects `k` on two
closed values selects `finiteSel 2 … k`: the finite operand of a finite value and an infinity.
-/
theorem finiteVariant_closed
    (op : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (k ca cb sa sb na nb da db : Nat)
    (h : op (closed ca sa na da) (closed cb sb nb db) = selected k ca cb sa sb na nb da db) :
    Arithmetic.finiteVariant op (closed ca sa na da) (closed cb sb nb db) =
      selected (finiteSel 2 ca cb k) ca cb sa sb na nb da db := by
  rw [finiteSel_eq, ite_eq_left rfl]
  rcases (by omega : ca = 0 ∨ ca = 1 ∨ ca = 2 ∨ 3 ≤ ca) with rfl | rfl | rfl | ha <;>
    rcases (by omega : cb = 0 ∨ cb = 1 ∨ cb = 2 ∨ 3 ≤ cb) with rfl | rfl | rfl | hb
  all_goals first
    | (simp [selected_eq, closed, Arithmetic.finiteVariant]; done)
    | (simp [← h, closed, Arithmetic.finiteVariant]; done)
    | (have h1 : ¬ca = 0 := by omega
       have h2 : ¬ca = 1 := by omega
       have h3 : ¬ca = 2 := by omega
       simp [← h, closed, Arithmetic.finiteVariant, Arithmetic.nan, h1, h2, h3])
    | (have h1 : ¬cb = 0 := by omega
       have h2 : ¬cb = 1 := by omega
       have h3 : ¬cb = 2 := by omega
       simp [← h, closed, Arithmetic.finiteVariant, Arithmetic.nan, h1, h2, h3])

/--
P3109 interim report v4.1, §4.11.4: `Arithmetic.Clamp` on three closed values given by class,
sign and ratio: NaN when the upper bound is below the lower one, and otherwise the minimum of
the upper bound and the maximum `m` of the value and the lower bound, each a selection.
-/
theorem clamp_closed (cv cl ch sv sl sh nv nl nh dv dl dh : Nat) (hsv : sv ≤ 1) (hsl : sl ≤ 1)
    (hsh : sh ≤ 1) (hdv : dv ≠ 0) (hdl : dl ≠ 0) (hdh : dh ≠ 0) (m : Nat)
    (hm : m = baseSel 1 0 cv cl sv sl (nv * dl) (nl * dv)) :
    Arithmetic.Clamp (closed cv sv nv dv) (closed cl sl nl dl) (closed ch sh nh dh) =
      if lessOf ch cl sh sl (nh * dl) (nl * dh) = true then Arithmetic.nan
      else
        selected
          (baseSel 0 0 (pickOf m cv cl 3) ch (pickOf m sv sl 0) sh (pickOf m nv nl 0 * dh)
            (nh * pickOf m dv dl 1))
          (pickOf m cv cl 3) ch (pickOf m sv sl 0) sh (pickOf m nv nl 0) nh (pickOf m dv dl 1)
          dh := by
  subst hm
  unfold Arithmetic.Clamp Arithmetic.CompareGreater
  rw [compareLess_closed _ _ _ _ _ _ _ _ hsh hsl hdh hdl,
    maximum_closed _ _ _ _ _ _ _ _ hsv hsl hdv hdl]
  unfold selected
  rw [minimum_closed _ _ _ _ _ _ _ _ (pickOf_le_one _ hsv hsl) hsh (pickOf_ne_zero _ hdv hdl)
    hdh]
  rfl

/-! ## The comparisons on encodings -/

variable {leftFormat rightFormat thirdFormat : Format}

/-- P3109 interim report v4.1, §4.12: `less` on two encodings of independent formats is the
reference strict comparison of their values, false for a NaN operand. -/
theorem compareLess_eq (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat) :
    ExecFloat.P3109.CompareLess x y =
      less leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
        rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
        x.toNatBits y.toNatBits := by
  unfold ExecFloat.P3109.CompareLess
  rw [toClosedRat_eq x, toClosedRat_eq y,
    compareLess_closed _ _ _ _ _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _)
      (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _)]
  rfl

/-- P3109 interim report v4.1, §4.12: `equal` on two encodings of independent formats is the
reference equality of their values, false for a NaN operand. -/
theorem compareEqual_eq (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat) :
    ExecFloat.P3109.CompareEqual x y =
      equal leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
        rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
        x.toNatBits y.toNatBits := by
  unfold ExecFloat.P3109.CompareEqual
  rw [toClosedRat_eq x, toClosedRat_eq y,
    compareEqual_closed _ _ _ _ _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _)
      (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _)]
  rfl

/-- P3109 interim report v4.1, §4.12: `lessEqual` on two encodings of independent formats is
the reference comparison of their values, false for a NaN operand. -/
theorem compareLessEqual_eq (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat) :
    ExecFloat.P3109.CompareLessEqual x y =
      lessEqual leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
        rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
        x.toNatBits y.toNatBits := by
  unfold ExecFloat.P3109.CompareLessEqual Arithmetic.CompareLessEqual
  rw [toClosedRat_eq x, toClosedRat_eq y,
    compareLess_closed _ _ _ _ _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _)
      (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _),
    compareEqual_closed _ _ _ _ _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _)
      (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _)]
  rfl

/-- P3109 interim report v4.1, §4.12: the reverse strict comparison is `less` with the operands
exchanged. -/
theorem compareGreater_eq (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat) :
    ExecFloat.P3109.CompareGreater x y =
      less rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
        leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
        y.toNatBits x.toNatBits :=
  compareLess_eq y x

/-- P3109 interim report v4.1, §4.12: the reverse comparison is `lessEqual` with the operands
exchanged. -/
theorem compareGreaterEqual_eq (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) :
    ExecFloat.P3109.CompareGreaterEqual x y =
      lessEqual rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
        leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
        y.toNatBits x.toNatBits :=
  compareLessEqual_eq y x

/-! ## The extrema on encodings -/

/-- On closed values given by class, sign and ratio, `op` selects the operand that
`extremumSel mx mag var` names, on the classes, the signs and the cross products of the
ratios. -/
def Selects (op : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (mx mag var : Nat) : Prop :=
  ∀ ca cb sa sb na nb da db : Nat, sa ≤ 1 → sb ≤ 1 → da ≠ 0 → db ≠ 0 →
    op (closed ca sa na da) (closed cb sb nb db) =
      selected (extremumSel mx mag var ca cb sa sb (na * db) (nb * da)) ca cb sa sb na nb da db

/-- P3109 interim report v4.1, §4.11.1: `Minimum` selects with the options `0 0 0`. -/
theorem minimum_selects : Selects Arithmetic.Minimum 0 0 0 :=
  fun _ _ _ _ _ _ _ _ => minimum_closed _ _ _ _ _ _ _ _

/-- P3109 interim report v4.1, §4.11.1: `Maximum` selects with the options `1 0 0`. -/
theorem maximum_selects : Selects Arithmetic.Maximum 1 0 0 :=
  fun _ _ _ _ _ _ _ _ => maximum_closed _ _ _ _ _ _ _ _

/-- P3109 interim report v4.1, §4.11.2: `MinimumMagnitude` selects with the options
`0 1 0`. -/
theorem minimumMagnitude_selects : Selects Arithmetic.MinimumMagnitude 0 1 0 :=
  fun _ _ _ _ _ _ _ _ => minimumMagnitude_closed _ _ _ _ _ _ _ _

/-- P3109 interim report v4.1, §4.11.2: `MaximumMagnitude` selects with the options
`1 1 0`. -/
theorem maximumMagnitude_selects : Selects Arithmetic.MaximumMagnitude 1 1 0 :=
  fun _ _ _ _ _ _ _ _ => maximumMagnitude_closed _ _ _ _ _ _ _ _

/-- P3109 interim report v4.1, §4.11.1: the number variant of an extremum that propagates NaN
selects with `var = 1`. -/
theorem Selects.number {op : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat}
    {mx mag : Nat} (h : Selects op mx mag 0) : Selects (Arithmetic.numberVariant op) mx mag 1 :=
  fun _ _ _ _ _ _ _ _ hsa hsb hda hdb =>
    numberVariant_closed op 1 _ _ _ _ _ _ _ _ _ Nat.one_ne_zero (h _ _ _ _ _ _ _ _ hsa hsb hda hdb)

/-- P3109 interim report v4.1, §4.11.3: the finite variant of the number variant of an extremum
selects with `var = 2`. -/
theorem Selects.finite {op : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat}
    {mx mag : Nat} (h : Selects op mx mag 1) : Selects (Arithmetic.finiteVariant op) mx mag 2 :=
  fun _ _ _ _ _ _ _ _ hsa hsb hda hdb =>
    finiteVariant_closed op _ _ _ _ _ _ _ _ _ (h _ _ _ _ _ _ _ _ hsa hsb hda hdb)

/--
P3109 interim report v4.1, §4.11: a binary operation that selects with the options `mx`, `mag`
and `var` is `extremum mx mag var` on encodings: its result on two values of independent
formats, projected once into the destination, for every descriptor, rounding mode, random word
and saturation mode. The ten extrema of the report are its instances `minimum_selects`,
`maximum_selects`, `minimumMagnitude_selects`, `maximumMagnitude_selects`, their `number` and
the `finite` of the first two `number`.
-/
theorem binary_eq_extremum
    {op : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat} {mx mag var : Nat}
    (h : Selects op mx mag var) (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.binary op x y target mode saturation =
      ExecFloat.P3109.ofNatBits
        (extremum mx mag var leftFormat.bitWidth leftFormat.precision (sgOf leftFormat)
          (exOf leftFormat) rightFormat.bitWidth rightFormat.precision (sgOf rightFormat)
          (exOf rightFormat) target.bitWidth target.precision (sgOf target) (exOf target)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits
          y.toNatBits) := by
  unfold ExecFloat.P3109.binary
  rw [toClosedRat_eq x, toClosedRat_eq y,
    h _ _ _ _ _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _) (denominatorOf_ne_zero _ _ _ _)
      (denominatorOf_ne_zero _ _ _ _)]
  unfold selected
  rw [projectRat_eq _ _ _ _ _ _ _ (pickOf_le_one _ (signOf_le _ _ _) (signOf_le _ _ _))
    (fun _ _ => pickOf_ne_zero _ (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _))]
  rfl

/--
P3109 interim report v4.1, §4.11.4: `clamp` on three encodings of independent formats stores
the reference clamp of the first value between the second and the third, NaN for a NaN operand
and for reversed bounds, projected once into the destination.
-/
theorem clamp_eq (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat)
    (z : ExecFloat.P3109 thirdFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.Clamp x y z target mode saturation =
      ExecFloat.P3109.ofNatBits
        (clamp leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          thirdFormat.bitWidth thirdFormat.precision (sgOf thirdFormat) (exOf thirdFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits y.toNatBits
          z.toNatBits) := by
  unfold ExecFloat.P3109.Clamp ExecFloat.P3109.ternary
  rw [toClosedRat_eq x, toClosedRat_eq y, toClosedRat_eq z,
    clamp_closed _ _ _ _ _ _ _ _ _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _) (signOf_le _ _ _)
      (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _)
      (denominatorOf_ne_zero _ _ _ _) _ rfl]
  unfold selected
  rw [ite_nan_closed,
    projectRat_eq _ _ _ _ _ _ _
      (pickOf_le_one _ (pickOf_le_one _ (signOf_le _ _ _) (signOf_le _ _ _)) (signOf_le _ _ _))
      (fun _ _ => pickOf_ne_zero _
        (pickOf_ne_zero _ (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _))
        (denominatorOf_ne_zero _ _ _ _))]
  unfold clamp
  kernel_notation

end FloatLib.Floats.Formats.P3109.KernelPath
