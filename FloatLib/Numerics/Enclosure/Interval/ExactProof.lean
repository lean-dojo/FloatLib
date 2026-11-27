/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Exact
public import FloatLib.Numerics.Enclosure.Interval.Hyperbolic
public import FloatLib.Numerics.Enclosure.Interval.OperationsProof

/-!
# Endpoints and containment of the exact rational interval operations

The endpoint theorems give each endpoint of an operation of `Interval.Exact` in ordinary
notation. For example, `mul_lo` says that the lower endpoint of `mul I J` is
`min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))`. The `_lo` and `_hi`
theorems are `simp` lemmas, so a proof never has to unfold the kernel definitions. `powNat_def`,
`absMax_eq` and `intersect_def` state three of the operations whole.

The bridge theorems compare the partial operations of `Interval.Runtime` and
`Interval.Operations` with exact rational endpoints, `Internal.rationalOutwardRounding`, to the
exact ones. `add?`, `neg?`, `sub?`, `mul?`, `abs?` and `pow?` always return the exact interval
(`add?_eq` and the others). `inv?` and `div?` return it exactly when the denominator lies strictly
on one side of zero, `hull?` when both inputs are ordered, and `intersect?` when the intersection
is not empty. At `ℚ`, `absBounds` is `abs` and `powBounds` is `powNat`. Scaling by a nonnegative
factor is the product with a point (`scaleNonneg_eq_mul`), and `divAbsLower` is a quotient by a
point (`divAbsLower_eq_div`).

The containment theorems say that each operation contains the real result for all real members
of its inputs, under the condition that the operation documents for its denominator, factor or
bound. Most of them follow from the containment theorems of the partial operations through the
bridge theorems.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval.Exact

/-! ### Endpoints -/

/-- The lower endpoint of a sum is the sum of the lower endpoints. -/
@[simp] theorem add_lo (I J : Interval ℚ) : (add I J).lo = I.lo + J.lo :=
  Kernel.Q.add_eq _ _

/-- The upper endpoint of a sum is the sum of the upper endpoints. -/
@[simp] theorem add_hi (I J : Interval ℚ) : (add I J).hi = I.hi + J.hi :=
  Kernel.Q.add_eq _ _

/-- The lower endpoint of a negation is the negated upper endpoint. -/
@[simp] theorem neg_lo (I : Interval ℚ) : (neg I).lo = -I.hi :=
  Kernel.Q.neg_eq _

/-- The upper endpoint of a negation is the negated lower endpoint. -/
@[simp] theorem neg_hi (I : Interval ℚ) : (neg I).hi = -I.lo :=
  Kernel.Q.neg_eq _

/-- The lower endpoint of a difference subtracts the upper endpoint of `J`. -/
@[simp] theorem sub_lo (I J : Interval ℚ) : (sub I J).lo = I.lo - J.hi :=
  Kernel.Q.sub_eq _ _

/-- The upper endpoint of a difference subtracts the lower endpoint of `J`. -/
@[simp] theorem sub_hi (I J : Interval ℚ) : (sub I J).hi = I.hi - J.lo :=
  Kernel.Q.sub_eq _ _

/-- The lower endpoint of a product is the least of the four endpoint products. -/
@[simp] theorem mul_lo (I J : Interval ℚ) :
    (mul I J).lo = min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)) := by
  simp only [mul, Kernel.Q.mul_eq, Kernel.Q.min_eq]

/-- The upper endpoint of a product is the greatest of the four endpoint products. -/
@[simp] theorem mul_hi (I J : Interval ℚ) :
    (mul I J).hi = max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)) := by
  simp only [mul, Kernel.Q.mul_eq, Kernel.Q.max_eq]

/-- At `ℚ`, the absolute-value range `absBounds` of `Interval.Operations` is `abs`. -/
theorem absBounds_eq (I : Interval ℚ) : absBounds I = abs I := by
  simp only [abs, neg, Kernel.Q.casesOn_le, Kernel.Q.neg_eq, Kernel.Q.max_eq]
  rfl

/-- The lower endpoint of `abs I` is `I.lo`, `-I.hi` or zero, by the sign of `I`. -/
@[simp] theorem abs_lo (I : Interval ℚ) :
    (abs I).lo = if 0 ≤ I.lo then I.lo else if I.hi ≤ 0 then -I.hi else 0 := by
  rw [← absBounds_eq, absBounds]
  split_ifs <;> rfl

/-- The upper endpoint of `abs I` is `I.hi`, `-I.lo` or `max (-I.lo) I.hi`, by the sign of `I`. -/
@[simp] theorem abs_hi (I : Interval ℚ) :
    (abs I).hi = if 0 ≤ I.lo then I.hi else if I.hi ≤ 0 then -I.lo else max (-I.lo) I.hi := by
  rw [← absBounds_eq, absBounds]
  split_ifs <;> rfl

/-- `powNat` in ordinary notation: `[1, 1]`, the powers of the endpoints of `abs I`, or the powers
of the endpoints of `I`, for a zero, even or odd exponent. -/
theorem powNat_def (I : Interval ℚ) (n : ℕ) :
    powNat I n =
      if n = 0 then point 1
      else if n % 2 = 0 then ⟨(abs I).lo ^ n, (abs I).hi ^ n⟩
      else ⟨I.lo ^ n, I.hi ^ n⟩ := by
  have hbeq (a b : ℕ) : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]
  unfold powNat
  rw [Kernel.Z.casesOn_eq_ite (hbeq n 0), Kernel.Z.casesOn_eq_ite (hbeq (Nat.mod n 2) 0)]
  simp only [Kernel.Q.pow_eq]
  rfl

/-- The lower endpoint of `powNat I n`, for a zero, even or odd exponent. -/
@[simp] theorem powNat_lo (I : Interval ℚ) (n : ℕ) :
    (powNat I n).lo = if n = 0 then 1 else if n % 2 = 0 then (abs I).lo ^ n else I.lo ^ n := by
  rw [powNat_def]
  split_ifs <;> rfl

/-- The upper endpoint of `powNat I n`, for a zero, even or odd exponent. -/
@[simp] theorem powNat_hi (I : Interval ℚ) (n : ℕ) :
    (powNat I n).hi = if n = 0 then 1 else if n % 2 = 0 then (abs I).hi ^ n else I.hi ^ n := by
  rw [powNat_def]
  split_ifs <;> rfl

/-- The lower endpoint of a scaled interval is the scaled lower endpoint. -/
@[simp] theorem scaleNonneg_lo (q : ℚ) (I : Interval ℚ) : (scaleNonneg q I).lo = q * I.lo :=
  Kernel.Q.mul_eq _ _

/-- The upper endpoint of a scaled interval is the scaled upper endpoint. -/
@[simp] theorem scaleNonneg_hi (q : ℚ) (I : Interval ℚ) : (scaleNonneg q I).hi = q * I.hi :=
  Kernel.Q.mul_eq _ _

/-- The lower endpoint of a reciprocal is the reciprocal of the upper endpoint. -/
@[simp] theorem inv_lo (I : Interval ℚ) : (inv I).lo = I.hi⁻¹ :=
  Kernel.Q.inv_eq _

/-- The upper endpoint of a reciprocal is the reciprocal of the lower endpoint. -/
@[simp] theorem inv_hi (I : Interval ℚ) : (inv I).hi = I.lo⁻¹ :=
  Kernel.Q.inv_eq _

/-- The lower endpoint of a quotient is the least of the four endpoint quotients. -/
@[simp] theorem div_lo (I J : Interval ℚ) :
    (div I J).lo = min (min (I.lo / J.hi) (I.lo / J.lo)) (min (I.hi / J.hi) (I.hi / J.lo)) := by
  simp only [div, mul_lo, inv_lo, inv_hi, div_eq_mul_inv]

/-- The upper endpoint of a quotient is the greatest of the four endpoint quotients. -/
@[simp] theorem div_hi (I J : Interval ℚ) :
    (div I J).hi = max (max (I.lo / J.hi) (I.lo / J.lo)) (max (I.hi / J.hi) (I.hi / J.lo)) := by
  simp only [div, mul_hi, inv_lo, inv_hi, div_eq_mul_inv]

/-- `absMax I` is the larger absolute value of the two endpoints. -/
theorem absMax_eq (I : Interval ℚ) : absMax I = max |I.lo| |I.hi| := by
  simp only [absMax, Kernel.Q.max_eq, Kernel.Q.abs_eq]

/-- `absMax I` is nonnegative. -/
theorem absMax_nonneg (I : Interval ℚ) : 0 ≤ absMax I :=
  absMax_eq I ▸ (abs_nonneg _).trans (le_max_left _ _)

/-- The lower endpoint of the symmetric quotient bound is `-(absMax I / δ)`. -/
@[simp] theorem divAbsLower_lo (I : Interval ℚ) (δ : ℚ) :
    (divAbsLower I δ).lo = -(absMax I / δ) := by
  simp only [divAbsLower, Kernel.Q.neg_eq, Kernel.Q.div_eq]

/-- The upper endpoint of the symmetric quotient bound is `absMax I / δ`. -/
@[simp] theorem divAbsLower_hi (I : Interval ℚ) (δ : ℚ) :
    (divAbsLower I δ).hi = absMax I / δ :=
  Kernel.Q.div_eq _ _

/-- The lower endpoint of a hull is the smaller lower endpoint. -/
@[simp] theorem hull_lo (I J : Interval ℚ) : (hull I J).lo = min I.lo J.lo :=
  Kernel.Q.min_eq _ _

/-- The upper endpoint of a hull is the larger upper endpoint. -/
@[simp] theorem hull_hi (I J : Interval ℚ) : (hull I J).hi = max I.hi J.hi :=
  Kernel.Q.max_eq _ _

/-- An intersection has the larger lower endpoint and the smaller upper endpoint. -/
theorem intersect_def (I J : Interval ℚ) :
    intersect I J = ⟨max I.lo J.lo, min I.hi J.hi⟩ := by
  simp only [intersect, Kernel.Q.max_eq, Kernel.Q.min_eq]

/-- The lower endpoint of an intersection is `max I.lo J.lo`. -/
@[simp] theorem intersect_lo (I J : Interval ℚ) :
    (intersect I J).lo = max I.lo J.lo := Kernel.Q.max_eq _ _

/-- The upper endpoint of an intersection is `min I.hi J.hi`. -/
@[simp] theorem intersect_hi (I J : Interval ℚ) :
    (intersect I J).hi = min I.hi J.hi := Kernel.Q.min_eq _ _

/-! ### The partial operations at exact rational endpoints -/

/-- With exact rational endpoints, `add?` returns the exact sum. -/
theorem add?_eq (I J : Interval ℚ) :
    add? Internal.rationalOutwardRounding I J = some (add I J) := by
  simp only [add, Kernel.Q.add_eq]
  rfl

/-- With exact rational endpoints, `neg?` returns the exact negation. -/
theorem neg?_eq (I : Interval ℚ) : neg? Internal.rationalOutwardRounding I = some (neg I) := by
  simp only [neg, Kernel.Q.neg_eq]
  rfl

/-- With exact rational endpoints, `sub?` returns the exact difference. -/
theorem sub?_eq (I J : Interval ℚ) :
    sub? Internal.rationalOutwardRounding I J = some (sub I J) := by
  simp only [sub, Kernel.Q.sub_eq]
  rfl

/-- With exact rational endpoints, `mul?` returns the four-corner product. -/
theorem mul?_eq (I J : Interval ℚ) :
    mul? Internal.rationalOutwardRounding I J = some (mul I J) := by
  simp only [mul, Kernel.Q.mul_eq, Kernel.Q.min_eq, Kernel.Q.max_eq]
  rfl

/-- With exact rational endpoints, `abs?` returns the absolute-value range. -/
theorem abs?_eq (I : Interval ℚ) : abs? Internal.rationalOutwardRounding I = some (abs I) := by
  rw [← absBounds_eq]
  rfl

/-- At `ℚ`, the power bounds `powBounds` of `Interval.Operations` are `powNat`. -/
theorem powBounds_eq (I : Interval ℚ) (n : ℕ) : powBounds I n = powNat I n := by
  rw [powNat_def, powBounds]
  simp only [binaryPow_eq_pow, absBounds_eq]

/-- With exact rational endpoints, `pow?` returns the exact power range. -/
theorem pow?_eq (I : Interval ℚ) (n : ℕ) :
    pow? Internal.rationalOutwardRounding I n = some (powNat I n) := by
  rw [← powBounds_eq]
  rfl

/-- With exact rational endpoints, `inv?` returns the reciprocal exactly when `I` lies strictly on
one side of zero. -/
theorem inv?_eq (I : Interval ℚ) :
    inv? Internal.rationalOutwardRounding I =
      if I.hi < 0 ∨ 0 < I.lo then some (inv I) else none := by
  simp only [inv, Kernel.Q.inv_eq]
  rfl

/-- With exact rational endpoints, `div?` returns the four-corner quotient exactly when `J` lies
strictly on one side of zero. -/
theorem div?_eq (I J : Interval ℚ) :
    div? Internal.rationalOutwardRounding I J =
      if J.hi < 0 ∨ 0 < J.lo then some (div I J) else none := by
  rw [show div I J = ⟨minOfFour (I.lo / J.lo) (I.lo / J.hi) (I.hi / J.lo) (I.hi / J.hi),
      maxOfFour (I.lo / J.lo) (I.lo / J.hi) (I.hi / J.lo) (I.hi / J.hi)⟩ by
    change (⟨(div I J).lo, (div I J).hi⟩ : Interval ℚ) = _
    rw [div_lo, div_hi, min_comm (I.lo / J.hi), min_comm (I.hi / J.hi), max_comm (I.lo / J.hi),
      max_comm (I.hi / J.hi)]]
  rfl

/-- With exact rational endpoints, `hull?` returns the hull exactly when both inputs are
ordered. -/
theorem hull?_eq (I J : Interval ℚ) :
    hull? Internal.rationalOutwardRounding I J =
      if I.lo ≤ I.hi ∧ J.lo ≤ J.hi then some (hull I J) else none := by
  rw [show hull I J = ⟨if I.lo ≤ J.lo then I.lo else J.lo, if I.hi ≤ J.hi then J.hi else I.hi⟩ by
    change (⟨(hull I J).lo, (hull I J).hi⟩ : Interval ℚ) = _
    rw [hull_lo, hull_hi, min_def, max_def]]
  rfl

/-- With exact rational endpoints, `intersect?` returns the intersection exactly when it is not
empty. -/
theorem intersect?_eq (I J : Interval ℚ) :
    intersect? Internal.rationalOutwardRounding I J =
      if max I.lo J.lo ≤ min I.hi J.hi then some (intersect I J) else none := by
  change (if max I.lo J.lo ≤ min I.hi J.hi then
      some (⟨if I.lo ≤ J.lo then J.lo else I.lo, if I.hi ≤ J.hi then I.hi else J.hi⟩ : Interval ℚ)
    else none) = _
  rw [intersect_def, max_def, min_def]

/-- For a nonnegative factor and an ordered interval, scaling is the product with `[q, q]`. -/
theorem scaleNonneg_eq_mul {q : ℚ} {I : Interval ℚ} (hq : 0 ≤ q) (h : I.lo ≤ I.hi) :
    scaleNonneg q I = mul (point q) I := by
  have hle := mul_le_mul_of_nonneg_left h hq
  change (⟨(scaleNonneg q I).lo, (scaleNonneg q I).hi⟩ : Interval ℚ) =
    ⟨(mul (point q) I).lo, (mul (point q) I).hi⟩
  simp only [scaleNonneg_lo, scaleNonneg_hi, mul_lo, mul_hi, point, min_self, max_self,
    min_eq_left hle, max_eq_right hle]

/-- For `0 ≤ δ`, the symmetric quotient bound is the quotient of `[-absMax I, absMax I]` by
`[δ, δ]`. -/
theorem divAbsLower_eq_div {I : Interval ℚ} {δ : ℚ} (hδ : 0 ≤ δ) :
    divAbsLower I δ = div ⟨-absMax I, absMax I⟩ (point δ) := by
  have hm := neg_le_self (div_nonneg (absMax_nonneg I) hδ)
  change (⟨(divAbsLower I δ).lo, (divAbsLower I δ).hi⟩ : Interval ℚ) =
    ⟨(div ⟨-absMax I, absMax I⟩ (point δ)).lo, (div ⟨-absMax I, absMax I⟩ (point δ)).hi⟩
  simp only [divAbsLower_lo, divAbsLower_hi, div_lo, div_hi, point, neg_div, min_self, max_self,
    min_eq_left hm, max_eq_right hm]

/-! ### Containment -/

/-- A sum contains the sum of any two members. -/
theorem containsReal_add {I J : Interval ℚ} {x y : ℝ} (hx : I.ContainsReal some x)
    (hy : J.ContainsReal some y) : (add I J).ContainsReal some (x + y) :=
  containsReal_add? Internal.rationalOutwardRounding (add?_eq I J) hx hy

/-- A negation contains the negation of every member. -/
theorem containsReal_neg {I : Interval ℚ} {x : ℝ} (hx : I.ContainsReal some x) :
    (neg I).ContainsReal some (-x) :=
  containsReal_neg? Internal.rationalOutwardRounding (neg?_eq I) hx

/-- A difference contains the difference of any two members. -/
theorem containsReal_sub {I J : Interval ℚ} {x y : ℝ} (hx : I.ContainsReal some x)
    (hy : J.ContainsReal some y) : (sub I J).ContainsReal some (x - y) :=
  containsReal_sub? Internal.rationalOutwardRounding (sub?_eq I J) hx hy

/-- A product contains the product of any two members. -/
theorem containsReal_mul {I J : Interval ℚ} {x y : ℝ} (hx : I.ContainsReal some x)
    (hy : J.ContainsReal some y) : (mul I J).ContainsReal some (x * y) :=
  containsReal_mul? Internal.rationalOutwardRounding (mul?_eq I J) hx hy

/-- The absolute-value range contains the absolute value of every member. -/
theorem containsReal_abs {I : Interval ℚ} {x : ℝ} (hx : I.ContainsReal some x) :
    (abs I).ContainsReal some |x| :=
  containsReal_abs? Internal.rationalOutwardRounding (abs?_eq I) hx

/-- The power range contains the `n`th power of every member. -/
theorem containsReal_powNat {I : Interval ℚ} {x : ℝ} (n : ℕ) (hx : I.ContainsReal some x) :
    (powNat I n).ContainsReal some (x ^ n) :=
  containsReal_pow? Internal.rationalOutwardRounding n (pow?_eq I n) hx

/-- Scaling by a nonnegative factor contains the scaled value of every member. -/
theorem containsReal_scaleNonneg {q : ℚ} {I : Interval ℚ} {x : ℝ} (hq : 0 ≤ q)
    (hx : I.ContainsReal some x) : (scaleNonneg q I).ContainsReal some (q * x) := by
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
  rw [containsReal_some_iff] at hx ⊢
  rw [scaleNonneg_lo, scaleNonneg_hi, Rat.cast_mul, Rat.cast_mul]
  exact ⟨mul_le_mul_of_nonneg_left hx.1 hq', mul_le_mul_of_nonneg_left hx.2 hq'⟩

/-- The reciprocal of an interval strictly on one side of zero contains every reciprocal. -/
theorem containsReal_inv {I : Interval ℚ} (h : I.hi < 0 ∨ 0 < I.lo) {x : ℝ}
    (hx : I.ContainsReal some x) : (inv I).ContainsReal some x⁻¹ :=
  containsReal_inv? Internal.rationalOutwardRounding (by rw [inv?_eq, ite_eq_left h]) hx

/-- A quotient by an interval strictly on one side of zero contains the quotient of any two
members. -/
theorem containsReal_div {I J : Interval ℚ} (h : J.hi < 0 ∨ 0 < J.lo) {x y : ℝ}
    (hx : I.ContainsReal some x) (hy : J.ContainsReal some y) :
    (div I J).ContainsReal some (x / y) :=
  containsReal_div? Internal.rationalOutwardRounding (by rw [div?_eq, ite_eq_left h]) hx hy

/-- Every member of `I` has absolute value at most `absMax I`. -/
theorem abs_le_absMax {I : Interval ℚ} {x : ℝ} (hx : I.ContainsReal some x) :
    |x| ≤ (absMax I : ℝ) := by
  rw [containsReal_some_iff] at hx
  rw [absMax_eq, Rat.cast_max, Rat.cast_abs, Rat.cast_abs]
  exact abs_le_max_abs_abs hx.1 hx.2

/-- For `0 < δ`, the symmetric quotient bound contains `x / y` for every member `x` of `I` and
every real `y` with `δ ≤ |y|`. -/
theorem containsReal_divAbsLower {I : Interval ℚ} {δ : ℚ} (hδ : 0 < δ) {x y : ℝ}
    (hx : I.ContainsReal some x) (hy : (δ : ℝ) ≤ |y|) :
    (divAbsLower I δ).ContainsReal some (x / y) := by
  have hquot : |x / y| ≤ ((absMax I / δ : ℚ) : ℝ) := by
    rw [abs_div, Rat.cast_div]
    exact (div_le_div_of_nonneg_right (abs_le_absMax hx) (abs_nonneg y)).trans
      (div_le_div_of_nonneg_left (Rat.cast_nonneg.mpr (absMax_nonneg I)) (Rat.cast_pos.mpr hδ)
        hy)
  rw [containsReal_some_iff, divAbsLower_lo, divAbsLower_hi, Rat.cast_neg]
  exact abs_le.mp hquot

/-- A hull contains every member of either interval. -/
theorem containsReal_hull {I J : Interval ℚ} {x : ℝ}
    (hx : I.ContainsReal some x ∨ J.ContainsReal some x) : (hull I J).ContainsReal some x := by
  simp only [containsReal_some_iff, hull_lo, hull_hi, Rat.cast_min, Rat.cast_max] at hx ⊢
  rcases hx with hx | hx
  · exact ⟨min_le_of_left_le hx.1, le_max_of_le_left hx.2⟩
  · exact ⟨min_le_of_right_le hx.1, le_max_of_le_right hx.2⟩

/-- A real number belongs to the intersection exactly when it belongs to both intervals. -/
theorem containsReal_intersect_iff (I J : Interval ℚ) (x : ℝ) :
    (intersect I J).ContainsReal some x ↔ I.ContainsReal some x ∧ J.ContainsReal some x := by
  simp only [containsReal_some_iff, intersect_lo, intersect_hi, Rat.cast_max, Rat.cast_min,
    max_le_iff, le_min_iff, and_and_and_comm]

/-- An intersection contains every common member of the two intervals. -/
theorem containsReal_intersect {I J : Interval ℚ} {x : ℝ} (hI : I.ContainsReal some x)
    (hJ : J.ContainsReal some x) : (intersect I J).ContainsReal some x :=
  (containsReal_intersect_iff I J x).2 ⟨hI, hJ⟩

end FloatLib.Numerics.Interval.Exact
