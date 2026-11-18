/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.ExtendedRat.Sum
public import FloatLib.Numerics.Quantization.Block.Coded
public import FloatLib.Numerics.Quantization.Block.Dot

/-!
# Exact dot products of stored tensors

`Tensor.dotExact` multiplies decoded positions and sums them in exact extended-rational
arithmetic. The operands may have different element and scale codecs. Finite results factor
through the element values and shared scales; a NaN position makes the exact dot NaN.
This module has no accumulator descriptor and performs no destination rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Numerics

variable {ι γ γ' : Type} {F : CodedFormat ι γ} {G : CodedFormat ι γ'}

namespace Tensor

/-- OCP MX v1.0, §6.1: exact decoded products, in the specified order, for independent codecs. -/
def products (a : Tensor F) (b : Tensor G) (order : List ι) : List (NumericalValue Rat) :=
  order.map fun i =>
    P3109.Arithmetic.Multiply ((a.decode i).map SignedRat.value)
      ((b.decode i).map SignedRat.value)

/-- Exact dot product of two stored tensors over the positions of `order`, in that order. The two
tensors may have different element formats, scale formats and levels. -/
def dotExact (a : Tensor F) (b : Tensor G) (order : List ι) : NumericalValue Rat :=
  Extended.sum (products a b order)

/-- Finite decoded positions give the corresponding list of finite rational products. -/
theorem products_finite (a : Tensor F) (b : Tensor G) (order : List ι)
    (ha : ∀ i ∈ order, (a.decode i).isFinite = true)
    (hb : ∀ i ∈ order, (b.decode i).isFinite = true) :
    products a b order =
      (order.map fun i => a.value i * b.value i).map NumericalValue.finite := by
  rw [products, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  simp [map_decode_of_isFinite a i (ha i hi), map_decode_of_isFinite b i (hb i hi),
    P3109.Arithmetic.Multiply]

/-- Finite decoded positions are multiplied and accumulated without rounding, even when they
cancel. -/
theorem dotExact_finite (a : Tensor F) (b : Tensor G) (order : List ι)
    (ha : ∀ i ∈ order, (a.decode i).isFinite = true)
    (hb : ∀ i ∈ order, (b.decode i).isFinite = true) :
    dotExact a b order = .finite (order.map fun i => a.value i * b.value i).sum := by
  rw [dotExact, products_finite a b order ha hb, Extended.sum_finite]

/-- A NaN position of the left tensor makes the dot NaN. -/
theorem dotExact_eq_nan_of_left (a : Tensor F) (b : Tensor G) (order : List ι) (i : ι)
    (hi : i ∈ order) (e : ExceptionalValue) (h : a.decode i = .exceptional e) :
    dotExact a b order = .exceptional .nan := by
  apply Extended.sum_eq_nan_of_mem
  exact List.mem_map.mpr ⟨i, hi, by simp [h, P3109.Arithmetic.Multiply, P3109.Arithmetic.nan]⟩

/-- A NaN position of the right tensor makes the dot NaN. -/
theorem dotExact_eq_nan_of_right (a : Tensor F) (b : Tensor G) (order : List ι) (i : ι)
    (hi : i ∈ order) (e : ExceptionalValue) (h : b.decode i = .exceptional e) :
    dotExact a b order = .exceptional .nan := by
  apply Extended.sum_eq_nan_of_mem
  refine List.mem_map.mpr ⟨i, hi, ?_⟩
  simp only [h, NumericalValue.map_exceptional]
  cases (a.decode i).map SignedRat.value <;> rfl

/-- A scale with no finite value at a position of either tensor makes the dot NaN, whatever the
element codes. -/
theorem dotExact_eq_nan_of_scale (a : Tensor F) (b : Tensor G) (order : List ι) (i : ι)
    (hi : i ∈ order)
    (h : ScaleCodes.isFinite F.levels a.scales i = false ∨
      ScaleCodes.isFinite G.levels b.scales i = false) :
    dotExact a b order = .exceptional .nan := by
  rcases h with h | h
  · exact dotExact_eq_nan_of_left a b order i hi .nan (decode_of_not_isFinite a i h)
  · exact dotExact_eq_nan_of_right a b order i hi .nan (decode_of_not_isFinite b i h)

/-- A zero position times an infinity is invalid even when every other product is finite. -/
theorem dotExact_eq_nan_of_zero_infinity (a : Tensor F) (b : Tensor G) (order : List ι) (i : ι)
    (hi : i ∈ order) (zero : SignedRat) (sign : Bool) (hzero : zero.value = 0)
    (ha : a.decode i = .finite zero) (hb : b.decode i = .infinity sign) :
    dotExact a b order = .exceptional .nan := by
  apply Extended.sum_eq_nan_of_mem
  exact List.mem_map.mpr ⟨i, hi, by
    simp [ha, hb, hzero, P3109.Arithmetic.Multiply, P3109.Arithmetic.nan]⟩

/--
Block factorization of the rational values. If the total scales of both tensors are constant on
the groups of `group`, the sum of the products of the values is the sum over the groups of the
product of the two scales and the dot product of the stored element values.
-/
theorem sum_value_mul_value [Fintype ι] {κ : Type} [DecidableEq κ] (a : Tensor F)
    (b : Tensor G) (group : ι → κ) (s t : κ → ℚ) (hs : ∀ i, a.scale i = s (group i))
    (ht : ∀ i, b.scale i = t (group i)) :
    ∑ i, a.value i * b.value i =
      ∑ g ∈ Finset.univ.image group, s g * t g *
        ∑ i ∈ members group g, F.element.value (a.elements i) * G.element.value (b.elements i) := by
  rw [← sum_decode_mul_decode group s t]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [value, Format.decode, hs, ht]

end Tensor

end FloatLib.Floats.Formats.Block
