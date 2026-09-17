/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.DotProduct.Runtime
public import FloatLib.Floats.Formats.OCP.MX.Standard.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error

/-!
# Numerical correctness of exact MX dot products

The executable list reductions are related to finite sums of decoded rational products and to
the factored shared-scale formula of OCP MX 1.0 §6.1. For finite input lanes and a finite
binary32 result, the result is one nearest-even rounding of the exact real dot across any
number of blocks. Its error is at most half an ULP, including gradual underflow; there is no
accumulation error.
-/

public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange
open scoped BigOperators

namespace DotProduct

private theorem foldl_finite (values : List Rat) (initial : Rat) :
    (values.map NumericalValue.finite).foldl add (.finite initial) =
      .finite (initial + values.sum) := by
  induction values generalizing initial with
  | nil => simp
  | cons value values ih =>
    simp only [List.map_cons, List.foldl_cons, add, ih, List.sum_cons]
    rw [add_assoc]

/-- Exact finite reduction agrees with the algebraic sum, independently of cancellation. -/
theorem sum_finite (values : List Rat) :
    sum (values.map NumericalValue.finite) = .finite values.sum := by
  simpa [sum] using foldl_finite values 0

/-- An indexed finite reduction agrees with the mathematical finite sum. -/
theorem sum_ofFn_finite {n : Nat} (values : Fin n → Rat) :
    sum (List.ofFn fun i => .finite (values i)) = .finite (∑ i, values i) := by
  simpa only [List.map_ofFn, Function.comp_def, Fin.sum_ofFn] using
    sum_finite (List.ofFn values)

private theorem foldl_infinity (values : List (NumericalValue Rat)) (sign : Bool)
    (h : ∀ value ∈ values, (∃ q, value = .finite q) ∨ value = .infinity sign) :
    values.foldl add (.infinity sign) = .infinity sign := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    have htail : ∀ value ∈ values, (∃ q, value = .finite q) ∨ value = .infinity sign :=
      fun value hv => h value (List.mem_cons_of_mem _ hv)
    rcases h value (by simp) with ⟨q, rfl⟩ | rfl
    · simpa [add] using ih htail
    · simpa [add] using ih htail

/--
An infinity survives a reduction whose other terms are finite or infinities of the same sign.
The hypothesis excludes both invalid products and opposite-infinity cancellation.
-/
theorem sum_eq_infinity (values : List (NumericalValue Rat)) (sign : Bool)
    (h : ∀ value ∈ values, (∃ q, value = .finite q) ∨ value = .infinity sign)
    (hmem : .infinity sign ∈ values) :
    sum values = .infinity sign := by
  have hfold (values : List (NumericalValue Rat)) (initial : Rat)
      (h : ∀ value ∈ values, (∃ q, value = .finite q) ∨ value = .infinity sign)
      (hmem : .infinity sign ∈ values) :
      values.foldl add (.finite initial) = .infinity sign := by
    induction values generalizing initial with
    | nil => simp at hmem
    | cons value values ih =>
      have htail : ∀ value ∈ values, (∃ q, value = .finite q) ∨ value = .infinity sign :=
        fun value hv => h value (List.mem_cons_of_mem _ hv)
      rcases h value (by simp) with ⟨q, rfl⟩ | rfl
      · exact ih (initial + q) htail (by simpa using hmem)
      · simpa [add] using foldl_infinity values sign htail
  exact hfold values 0 h hmem

private theorem signed_ratio_real (value : Rat) :
    Model.signedScaledRatToReal (value.num < 0) value.num.natAbs value.den 0 =
      (value : ℝ) := by
  rw [Rat.cast_def]
  by_cases h : value.num < 0
  · simp [Model.signedScaledRatToReal, Model.scaledRatToReal, Model.bpow, h, abs_of_neg h,
      neg_div]
  · simp [Model.signedScaledRatToReal, Model.scaledRatToReal, Model.bpow, h,
      abs_of_nonneg (le_of_not_gt h)]

/--
The existing binary rational packer realizes the independent nearest-even real projection.
Finiteness excludes overflow, where a real-valued error is not defined.
-/
theorem toReal_roundFloat32_finite (value : Rat)
    (hfinite : Model.isFinite (roundFloat32 (.finite value)) = true) :
    Model.toReal (roundFloat32 (.finite value)) = Model.roundAt .binary32 (value : ℝ) := by
  by_cases hzero : value = 0
  · subst value
    simp [roundFloat32]
  · have hn : value.num.natAbs ≠ 0 := by
      simpa using Rat.num_ne_zero.mpr hzero
    rw [roundFloat32, Model.roundRat,
      Model.toReal_roundRatScaled_eq_roundAt _ _ _ _ _ (by decide) hn value.den_nz hfinite,
      signed_ratio_real]

end DotProduct

/-- One exceptional lane product poisons an exact reduction, regardless of its position. -/
theorem DotProduct.sum_eq_nan_of_mem (values : List (NumericalValue Rat))
    (h : .exceptional .nan ∈ values) : DotProduct.sum values = .exceptional .nan := by
  have habsorb (rest : List (NumericalValue Rat)) :
      rest.foldl DotProduct.add (.exceptional .nan) = .exceptional .nan := by
    induction rest with
    | nil => rfl
    | cons value rest ih =>
      simpa only [List.foldl_cons, DotProduct.add] using ih
  have hfold (rest : List (NumericalValue Rat)) (initial : NumericalValue Rat)
      (hmem : .exceptional .nan ∈ rest) :
      rest.foldl DotProduct.add initial = .exceptional .nan := by
    induction rest generalizing initial with
    | nil => simp at hmem
    | cons value rest ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst value
        cases initial <;> simpa [DotProduct.add] using habsorb rest
      · exact ih _ htail
  exact hfold values _ h

/-- A lane-local NaN on the left propagates through multiplication and the full block sum. -/
theorem dotExact_eq_nan_of_left_lane {leftProfile rightProfile : Profile}
    (left : Block leftProfile) (right : Block rightProfile) (lane : Fin 32)
    (exceptional : ExceptionalValue)
    (h : left.decodeLane lane = .exceptional exceptional) :
    dotExact left right = .exceptional .nan := by
  apply DotProduct.sum_eq_nan_of_mem
  rw [List.mem_ofFn]
  refine ⟨lane, ?_⟩
  simp [h, DotProduct.mul]

/-- A lane-local NaN on the right also poisons the full dot. -/
theorem dotExact_eq_nan_of_right_lane {leftProfile rightProfile : Profile}
    (left : Block leftProfile) (right : Block rightProfile) (lane : Fin 32)
    (exceptional : ExceptionalValue)
    (h : right.decodeLane lane = .exceptional exceptional) :
    dotExact left right = .exceptional .nan := by
  apply DotProduct.sum_eq_nan_of_mem
  rw [List.mem_ofFn]
  refine ⟨lane, ?_⟩
  simp only [h, NumericalValue.map_exceptional]
  cases (left.decodeLane lane).map SignedRat.value <;> rfl

/-- A NaN shared scale on either operand poisons the dot independently of element bits. -/
theorem dotExact_eq_nan_of_scale {leftProfile rightProfile : Profile}
    (left : Block leftProfile) (right : Block rightProfile)
    (h : left.scale.exponent? = none ∨ right.scale.exponent? = none) :
    dotExact left right = .exceptional .nan := by
  rcases h with h | h
  · exact dotExact_eq_nan_of_left_lane left right 0 .nan
      (Block.decodeLane_of_nan_scale left 0 h)
  · exact dotExact_eq_nan_of_right_lane left right 0 .nan
      (Block.decodeLane_of_nan_scale right 0 h)

/-- A zero lane multiplied by infinity is invalid even when every other product is finite. -/
theorem dotExact_eq_nan_of_zero_infinity {leftProfile rightProfile : Profile}
    (left : Block leftProfile) (right : Block rightProfile) (lane : Fin 32)
    (zero : SignedRat) (sign : Bool)
    (hzero : zero.value = 0)
    (hleft : left.decodeLane lane = .finite zero)
    (hright : right.decodeLane lane = .infinity sign) :
    dotExact left right = .exceptional .nan := by
  apply DotProduct.sum_eq_nan_of_mem
  rw [List.mem_ofFn]
  exact ⟨lane, by simp [hleft, hright, hzero, DotProduct.mul]⟩

/-- An invalid block dot propagates to the final binary32 NaN across any number of blocks. -/
theorem dotGeneral_eq_nan_of_block {leftProfile rightProfile : Profile} {n : Nat}
    (left : Vector (Block leftProfile) n) (right : Vector (Block rightProfile) n)
    (block : Fin n) (h : dotExact left[block.val] right[block.val] = .exceptional .nan) :
    dotGeneral left right = Model.canonicalNaN .binary32 := by
  have hsum : dotGeneralExact left right = .exceptional .nan :=
    DotProduct.sum_eq_nan_of_mem _ (List.mem_ofFn.mpr ⟨block, h⟩)
  simp [dotGeneral, hsum, DotProduct.roundFloat32]

/-- With no blocks there are no exceptional operands, and the result is positive zero. -/
@[simp] theorem dotGeneral_empty {leftProfile rightProfile : Profile}
    (left : Vector (Block leftProfile) 0) (right : Vector (Block rightProfile) 0) :
    dotGeneral left right = Model.posZero .binary32 := by
  simp [dotGeneral, dotGeneralExact, DotProduct.sum, DotProduct.roundFloat32]

/-- Finite decoded lanes are multiplied and accumulated exactly, even when they cancel. -/
theorem dotExact_finite {leftProfile rightProfile : Profile}
    (left : Block leftProfile) (right : Block rightProfile)
    (a b : Fin 32 → SignedRat)
    (ha : ∀ i, left.decodeLane i = .finite (a i))
    (hb : ∀ i, right.decodeLane i = .finite (b i)) :
    dotExact left right = .finite (∑ i, (a i).value * (b i).value) := by
  simp only [dotExact, ha, hb, NumericalValue.map, DotProduct.mul]
  exact DotProduct.sum_ofFn_finite _

/-- A finite one-block result is one nearest-even rounding of its exact real dot. -/
theorem toReal_dot_eq_roundAt {leftProfile rightProfile : Profile}
    (left : Block leftProfile) (right : Block rightProfile)
    (a b : Fin 32 → SignedRat)
    (ha : ∀ i, left.decodeLane i = .finite (a i))
    (hb : ∀ i, right.decodeLane i = .finite (b i))
    (hfinite : Model.isFinite (dot left right) = true) :
    Model.toReal (dot left right) =
      Model.roundAt .binary32 (∑ i, ((a i).value : ℝ) * ((b i).value : ℝ)) := by
  unfold dot at hfinite ⊢
  rw [dotExact_finite left right a b ha hb] at hfinite ⊢
  rw [DotProduct.toReal_roundFloat32_finite _ hfinite]
  simp

/-- The one-block dot also incurs only the final half-ULP rounding error. -/
theorem abs_toReal_dot_sub_le {leftProfile rightProfile : Profile}
    (left : Block leftProfile) (right : Block rightProfile)
    (a b : Fin 32 → SignedRat)
    (ha : ∀ i, left.decodeLane i = .finite (a i))
    (hb : ∀ i, right.decodeLane i = .finite (b i))
    (hfinite : Model.isFinite (dot left right) = true) :
    |Model.toReal (dot left right) - ∑ i, ((a i).value : ℝ) * ((b i).value : ℝ)| ≤
      Model.epsilonAt .binary32 (∑ i, ((a i).value : ℝ) * ((b i).value : ℝ)) := by
  rw [toReal_dot_eq_roundAt left right a b ha hb hfinite]
  exact Model.abs_roundAt_sub_le .binary32 _

/-- The exact block reduction equals the specification's factored shared-scale expression. -/
theorem dotExact_eq_scaled_sum {leftProfile rightProfile : Profile}
    (left : Block leftProfile) (right : Block rightProfile)
    (a b : Fin 32 → SignedRat) (leftExponent rightExponent : Int)
    (hleft : left.scale.exponent? = some leftExponent)
    (hright : right.scale.exponent? = some rightExponent)
    (ha : ∀ i, Element.decode left.values[i.val] = .finite (a i))
    (hb : ∀ i, Element.decode right.values[i.val] = .finite (b i)) :
    dotExact left right = .finite
      ((2 : Rat) ^ leftExponent * (2 : Rat) ^ rightExponent *
        ∑ i, (a i).value * (b i).value) := by
  rw [dotExact_finite left right
    (fun i => scaleFinite leftExponent (a i)) (fun i => scaleFinite rightExponent (b i))
    (fun i => Block.decodeLane_finite left i hleft (ha i))
    (fun i => Block.decodeLane_finite right i hright (hb i))]
  congr 1
  simp only [scaleFinite_value, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- General accumulation sums every exact lane product without intermediate rounding. -/
theorem dotGeneralExact_finite {leftProfile rightProfile : Profile} {n : Nat}
    (left : Vector (Block leftProfile) n) (right : Vector (Block rightProfile) n)
    (a b : Fin n → Fin 32 → SignedRat)
    (ha : ∀ (j : Fin n) (i : Fin 32), left[j.val].decodeLane i = .finite (a j i))
    (hb : ∀ (j : Fin n) (i : Fin 32), right[j.val].decodeLane i = .finite (b j i)) :
    dotGeneralExact left right =
      .finite (∑ j, ∑ i, (a j i).value * (b j i).value) := by
  unfold dotGeneralExact
  simp_rw [dotExact_finite _ _ _ _ (ha _) (hb _)]
  exact DotProduct.sum_ofFn_finite _

/-- Real exact dot of decoded lanes, without an intermediate representability restriction. -/
noncomputable def realDot {n : Nat} (a b : Fin n → Fin 32 → SignedRat) : ℝ :=
  ∑ j, ∑ i, ((a j i).value : ℝ) * ((b j i).value : ℝ)

/-- The final finite binary32 result is one nearest-even rounding of the exact real dot. -/
theorem toReal_dotGeneral_eq_roundAt {leftProfile rightProfile : Profile} {n : Nat}
    (left : Vector (Block leftProfile) n) (right : Vector (Block rightProfile) n)
    (a b : Fin n → Fin 32 → SignedRat)
    (ha : ∀ (j : Fin n) (i : Fin 32), left[j.val].decodeLane i = .finite (a j i))
    (hb : ∀ (j : Fin n) (i : Fin 32), right[j.val].decodeLane i = .finite (b j i))
    (hfinite : Model.isFinite (dotGeneral left right) = true) :
    Model.toReal (dotGeneral left right) = Model.roundAt .binary32 (realDot a b) := by
  unfold dotGeneral at hfinite ⊢
  rw [dotGeneralExact_finite left right a b ha hb] at hfinite ⊢
  rw [DotProduct.toReal_roundFloat32_finite _ hfinite]
  simp [realDot]

/--
Finite-result absolute error is at most half an ULP of the exact dot. This includes subnormal
results and cancellation; there is no error from the number or order of finite summands.
-/
theorem abs_toReal_dotGeneral_sub_le {leftProfile rightProfile : Profile} {n : Nat}
    (left : Vector (Block leftProfile) n) (right : Vector (Block rightProfile) n)
    (a b : Fin n → Fin 32 → SignedRat)
    (ha : ∀ (j : Fin n) (i : Fin 32), left[j.val].decodeLane i = .finite (a j i))
    (hb : ∀ (j : Fin n) (i : Fin 32), right[j.val].decodeLane i = .finite (b j i))
    (hfinite : Model.isFinite (dotGeneral left right) = true) :
    |Model.toReal (dotGeneral left right) - realDot a b| ≤
      Model.epsilonAt .binary32 (realDot a b) := by
  rw [toReal_dotGeneral_eq_roundAt left right a b ha hb hfinite]
  exact Model.abs_roundAt_sub_le .binary32 _

end FloatLib.Floats.Formats.OCP.MX.Standard
