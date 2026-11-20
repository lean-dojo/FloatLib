/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Reduction.ScaledProduct.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Reduction.Proof

/-!
# The decimal scaled products round the exact scaled product once

For finite operands whose exact product `P` is not zero, in every decimal format and rounding
direction:

* `scaledProd_eq_project`: the scale factor of `scaledProd` is `Int.log 10 |P|`, the decimal
  exponent of the leading digit of `P`, and its product and flags are those of one `project` of
  `P / 10 ^ Int.log 10 |P|`. `scaledProdSum_eq_project` and `scaledProdDiff_eq_project` are the
  same statement for the product of the sums and of the differences of the operands.
* `abs_scaled_mem`: that scaled exact product has a magnitude in `[1, 10)`.
* `scaledProd_inexact_iff`: `inexact` is raised exactly when `pr × 10 ^ sf` is not `P`.
* `scaledProd_status`: a format that holds the decade from one to ten in its normal range
  raises neither `overflow` nor `underflow`. `Format.unitDecade_of_quantum` gives the two
  premises from the quantum range, and they hold for decimal32, decimal64 and decimal128.

`scaledProd_valid` and its siblings say that every result is a datum of the format, for all
operands.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/--
A format whose least quantum exponent is at most `1 - precision` and whose largest is at least
`2 - precision` holds the decade from one to ten in its normal range: the least normal
magnitude is at most one, and the largest finite magnitude at least ten.
-/
theorem Format.unitDecade_of_quantum (f : Format) (hlow : f.minQuantum ≤ 1 - (f.precision : Int))
    (hhigh : 2 - (f.precision : Int) ≤ f.maxQuantum) :
    f.minNormal ≤ 1 ∧
      (10 : ℚ) ≤ ((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum := by
  have hp := f.precision_pos
  have hten : (1 : ℚ) ≤ 10 := by norm_num
  constructor
  · calc f.minNormal
        ≤ (10 : ℚ) ^ (f.precision - 1) * (10 : ℚ) ^ (1 - (f.precision : Int)) :=
          mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hten hlow) (by positivity)
      _ = 1 := by
          rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0),
            show ((f.precision - 1 : Nat) : Int) + (1 - (f.precision : Int)) = 0 by omega,
            zpow_zero]
  · have hbound : 10 ^ (f.precision - 1) ≤ f.coefficientBound - 1 := by
      rw [f.coefficientBound_eq]
      have hsplit : 10 ^ f.precision = 10 * 10 ^ (f.precision - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hp]
      have hpos : 0 < 10 ^ (f.precision - 1) := by positivity
      omega
    calc (10 : ℚ)
        = (10 : ℚ) ^ (f.precision - 1) * (10 : ℚ) ^ (2 - (f.precision : Int)) := by
          rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0),
            show ((f.precision - 1 : Nat) : Int) + (2 - (f.precision : Int)) = 1 by omega,
            zpow_one]
      _ ≤ ((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum :=
          mul_le_mul (by exact_mod_cast hbound) (zpow_le_zpow_right₀ hten hhigh)
            (by positivity) (by positivity)

/--
A projection of a value with a magnitude in `[1, 10)` raises neither `overflow` nor
`underflow`, in a format that holds that decade in its normal range.
-/
theorem project_status_of_unitDecade (f : Format) (mode : RoundingMode) {x : ℚ}
    (hlow : 1 ≤ |x|) (hhigh : |x| < 10) (hmin : f.minNormal ≤ 1)
    (hmax : (10 : ℚ) ≤ ((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum)
    (preferred : Int) (negativeZero : Bool) :
    (project f mode x preferred negativeZero).status.overflow = false ∧
      (project f mode x preferred negativeZero).status.underflow = false := by
  constructor
  · by_contra hoverflow
    have h := (projectMagnitude_overflow_iff f mode _ |x| preferred).mp
      (by simpa [project] using hoverflow)
    have hlt := maxFinite_lt_of_roundedPair_overflow f mode _ (abs_nonneg x) h
    linarith
  · by_contra hunderflow
    have h := (project_underflow_iff f mode x preferred negativeZero).mp (by simpa using hunderflow)
    linarith [h.1]

namespace Arithmetic

open BinaryInterchange (ScaledProduct)

namespace Reduction

/-- The opposite of a finite term has the opposite value. -/
theorem Term.value?_neg {term : Term} {exact : ℚ} (h : term.value? = some exact) :
    term.neg.value? = some (-exact) := by
  cases term <;> simp_all [Term.neg, Term.value?]

/-- The sum of two finite terms has the sum of their values. -/
theorem Term.value?_add (mode : RoundingMode) {left right : Term} {p q : ℚ}
    (hp : left.value? = some p) (hq : right.value? = some q) :
    (left.add mode right).value? = some (p + q) := by
  cases left <;> cases right <;> simp_all [Term.add, Term.value?]

/-- The scaled exact product: a nonzero rational divided by the power of ten of its leading
digit has a magnitude in `[1, 10)`. -/
theorem abs_scaled_mem {value : ℚ} (hne : value ≠ 0) :
    1 ≤ |value / (10 : ℚ) ^ Int.log 10 (|value|)| ∧
      |value / (10 : ℚ) ^ Int.log 10 (|value|)| < 10 := by
  have hpos : 0 < |value| := abs_pos.mpr hne
  have hpow : 0 < (10 : ℚ) ^ Int.log 10 |value| := zpow_pos (by norm_num) _
  have hlower := Int.zpow_log_le_self (b := 10) (by norm_num) hpos
  have hupper := Int.lt_zpow_succ_log_self (b := 10) (by norm_num) |value|
  rw [Nat.cast_ofNat] at hlower hupper
  rw [abs_div, abs_of_pos hpow]
  refine ⟨(one_le_div₀ hpow).mpr hlower, (div_lt_iff₀ hpow).mpr ?_⟩
  rwa [zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm] at hupper

/-- Finite factors only multiply their values into the exact product. -/
theorem foldl_push_product_of_values :
    ∀ (factors : List Term) (exacts : List ℚ) (start : Product),
      factors.map Term.value? = exacts.map some →
      ∃ quantum negative, factors.foldl Product.push start =
        { start with
          value := start.value * exacts.prod, quantum := quantum, negative := negative }
  | [], exacts, start, h => by
      cases exacts with
      | nil => exact ⟨start.quantum, start.negative, by simp⟩
      | cons exact rest => simp at h
  | factor :: factors, exacts, start, h => by
      cases exacts with
      | nil => simp at h
      | cons exact rest =>
          simp only [List.map_cons, List.cons.injEq] at h
          cases factor with
          | finite s value quantum =>
              obtain rfl : value = exact := by simpa [Term.value?] using h.1
              obtain ⟨quantum', negative', hfold⟩ :=
                foldl_push_product_of_values factors rest (start.push (.finite s value quantum))
                  h.2
              refine ⟨quantum', negative', ?_⟩
              rw [List.foldl_cons, hfold]
              simp [Product.push, mul_assoc]
          | infinity s => simp [Term.value?] at h
          | nan s t p => simp [Term.value?] at h
          | invalid => simp [Term.value?] at h

/--
A scaled product of finite factors whose exact product `P` is not zero is one rounding of
`P / 10 ^ Int.log 10 |P|`, with the scale factor `Int.log 10 |P|`.
-/
theorem Product.deliver_of_values (f : Format) (mode : RoundingMode) (factors : List Term)
    (exacts : List ℚ) (h : factors.map Term.value? = exacts.map some)
    (hne : exacts.prod ≠ 0) :
    ∃ preferred,
      (product factors).deliver f mode =
        scaled (project f mode (exacts.prod / (10 : ℚ) ^ Int.log 10 |exacts.prod|) preferred)
          (Int.log 10 |exacts.prod|) := by
  obtain ⟨quantum, negative, hfold⟩ := foldl_push_product_of_values factors exacts {} h
  refine ⟨quantum - Int.log 10 |exacts.prod|, ?_⟩
  rw [product, hfold]
  simp [Product.deliver, hne]

/-- The outcome of a scaled product is a datum of the format. -/
theorem Product.deliver_valid (f : Format) (mode : RoundingMode) (product : Product) :
    (product.deliver f mode).product.Valid f := by
  unfold Product.deliver
  dsimp only [scaled]
  split
  · exact nanResult_valid f _ _ false
  · split_ifs
    · exact invalidResult_valid f
    · trivial
    · exact project_valid ..
    · exact project_valid ..

end Reduction

open Reduction

/-- `scaledProd` always returns a datum of the format. -/
theorem scaledProd_valid (f : Format) (mode : RoundingMode) (values : Array Datum) :
    (scaledProd f mode values).product.Valid f :=
  Product.deliver_valid f mode _

/-- `scaledProdSum` returns a datum of the format whenever the lengths agree. -/
theorem scaledProdSum_valid (f : Format) (mode : RoundingMode) (left right : Array Datum)
    {result : ScaledProduct Datum} (h : scaledProdSum f mode left right = .ok result) :
    result.product.Valid f := by
  unfold scaledProdSum at h
  split at h
  · cases h
    exact Product.deliver_valid f mode _
  · cases h

/-- `scaledProdDiff` returns a datum of the format whenever the lengths agree. -/
theorem scaledProdDiff_valid (f : Format) (mode : RoundingMode) (left right : Array Datum)
    {result : ScaledProduct Datum} (h : scaledProdDiff f mode left right = .ok result) :
    result.product.Valid f := by
  unfold scaledProdDiff at h
  split at h
  · cases h
    exact Product.deliver_valid f mode _
  · cases h

/--
**The decimal `scaledProd` rounds the exact scaled product once.** For finite operands with the
exact values `exacts` whose product `P` is not zero, the scale factor is `Int.log 10 |P|`, and
the product and the flags are those of one `project` of `P / 10 ^ Int.log 10 |P|`, in every
format and rounding direction.
-/
theorem scaledProd_eq_project (f : Format) (mode : RoundingMode) (values : Array Datum)
    (exacts : List ℚ) (hexact : values.toList.map Datum.toRat? = exacts.map some)
    (hne : exacts.prod ≠ 0) :
    ∃ preferred,
      scaledProd f mode values =
        scaled (project f mode (exacts.prod / (10 : ℚ) ^ Int.log 10 |exacts.prod|) preferred)
          (Int.log 10 |exacts.prod|) :=
  Product.deliver_of_values f mode (values.toList.map Term.ofDatum) exacts
    (by simpa [Function.comp_def, Term.value?_ofDatum] using hexact) hne

/--
**The decimal `scaledProdSum` rounds the exact scaled product of the sums once**, for finite
operands with the exact values `xs` and `ys` in arrays of one length, when no sum is zero.
-/
theorem scaledProdSum_eq_project (f : Format) (mode : RoundingMode) (left right : Array Datum)
    (xs ys : List ℚ) (hleft : left.toList.map Datum.toRat? = xs.map some)
    (hright : right.toList.map Datum.toRat? = ys.map some) (hsize : left.size = right.size)
    (hne : (List.zipWith (· + ·) xs ys).prod ≠ 0) :
    ∃ preferred,
      scaledProdSum f mode left right =
        .ok (scaled (project f mode ((List.zipWith (· + ·) xs ys).prod /
          (10 : ℚ) ^ Int.log 10 |(List.zipWith (· + ·) xs ys).prod|) preferred)
          (Int.log 10 |(List.zipWith (· + ·) xs ys).prod|)) := by
  obtain ⟨preferred, h⟩ := Product.deliver_of_values f mode _ _
    (map_value?_zipWith (fun left right => left.add mode right) (· + ·)
      (fun hp hq => Term.value?_add mode hp hq) _ _ xs ys hleft hright) hne
  exact ⟨preferred, by simp only [scaledProdSum, hsize, ↓reduceIte, h]⟩

/--
**The decimal `scaledProdDiff` rounds the exact scaled product of the differences once**, for
finite operands with the exact values `xs` and `ys` in arrays of one length, when no
difference is zero.
-/
theorem scaledProdDiff_eq_project (f : Format) (mode : RoundingMode) (left right : Array Datum)
    (xs ys : List ℚ) (hleft : left.toList.map Datum.toRat? = xs.map some)
    (hright : right.toList.map Datum.toRat? = ys.map some) (hsize : left.size = right.size)
    (hne : (List.zipWith (· - ·) xs ys).prod ≠ 0) :
    ∃ preferred,
      scaledProdDiff f mode left right =
        .ok (scaled (project f mode ((List.zipWith (· - ·) xs ys).prod /
          (10 : ℚ) ^ Int.log 10 |(List.zipWith (· - ·) xs ys).prod|) preferred)
          (Int.log 10 |(List.zipWith (· - ·) xs ys).prod|)) := by
  obtain ⟨preferred, h⟩ := Product.deliver_of_values f mode _ _
    (map_value?_zipWith (fun left right => left.add mode right.neg) (· - ·)
      (fun hp hq => by
        rw [sub_eq_add_neg]
        exact Term.value?_add mode hp (Term.value?_neg hq)) _ _ xs ys hleft hright) hne
  exact ⟨preferred, by simp only [scaledProdDiff, hsize, ↓reduceIte, h]⟩

/--
In every rounding direction, the decimal `scaledProd` of finite operands with a nonzero exact
product raises `inexact` exactly when `pr × 10 ^ sf` is not that product.
-/
theorem scaledProd_inexact_iff (f : Format) (mode : RoundingMode) (values : Array Datum)
    (exacts : List ℚ) (hexact : values.toList.map Datum.toRat? = exacts.map some)
    (hne : exacts.prod ≠ 0) (value : ℚ)
    (hvalue : (scaledProd f mode values).product.toRat? = some value) :
    (scaledProd f mode values).status.inexact = true ↔
      value * (10 : ℚ) ^ (scaledProd f mode values).scaleFactor ≠ exacts.prod := by
  obtain ⟨preferred, h⟩ := scaledProd_eq_project f mode values exacts hexact hne
  rw [h] at hvalue ⊢
  have hpow : (10 : ℚ) ^ Int.log 10 |exacts.prod| ≠ 0 := zpow_ne_zero _ (by norm_num)
  rw [show (scaled (project f mode (exacts.prod / (10 : ℚ) ^ Int.log 10 |exacts.prod|)
      preferred) (Int.log 10 |exacts.prod|)).status.inexact =
        (project f mode (exacts.prod / (10 : ℚ) ^ Int.log 10 |exacts.prod|)
          preferred).status.inexact from rfl,
    project_inexact_iff f mode _ value preferred false hvalue, Ne, eq_div_iff hpow]
  rfl

/--
The decimal `scaledProd` of finite operands with a nonzero exact product raises neither
`overflow` nor `underflow` in a format that holds the decade from one to ten in its normal
range (`Format.unitDecade_of_quantum`).
-/
theorem scaledProd_status (f : Format) (mode : RoundingMode) (values : Array Datum)
    (exacts : List ℚ) (hexact : values.toList.map Datum.toRat? = exacts.map some)
    (hne : exacts.prod ≠ 0) (hmin : f.minNormal ≤ 1)
    (hmax : (10 : ℚ) ≤ ((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum) :
    (scaledProd f mode values).status.overflow = false ∧
      (scaledProd f mode values).status.underflow = false := by
  obtain ⟨preferred, h⟩ := scaledProd_eq_project f mode values exacts hexact hne
  rw [h]
  exact project_status_of_unitDecade f mode (abs_scaled_mem hne).1 (abs_scaled_mem hne).2 hmin
    hmax preferred false

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
