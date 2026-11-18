/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Magnitude.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Dot.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Sum.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core

/-!
# Contracts of the sums of magnitudes and of squares

`sumAbs` and `sumSquare` are `sum` and `dot` with one more special case, so their contracts are
those of `Reduction.Proof` once the special case is settled, for all formats and directions:

* `sumAbs_status_eq_sum`, `dot_status_self_eq_sumSquare`: when no infinity decides, `sumAbs` is
  the correctly rounded `sum` of the magnitudes and `sumSquare` the correctly rounded `dot` of
  the array with itself, flags and ternary value included.
* `sumAbs_status_of_decidingInfinity?`, `sumSquare_status_of_decidingInfinity?`: when an
  infinity decides, the result is the cast of its magnitude into the destination: `+∞` where
  the destination has infinities, with no flag, even beside a quiet NaN.
* `decidingInfinity?_eq_none_of_isFinite`: finite operands have no deciding infinity.
* `toReal_sumAbs`, `toReal_sumSquare`: for finite operands and a finite result in a conventional
  IEEE destination, the nearest-even result is one rounding of the exact sum of the magnitudes
  (`Semantics.finiteSum` of the magnitudes) or of the squares (`Semantics.finiteDot` of the array
  with itself).
* `value_sumAbs`, `value_sumSquare`: asking for the status does not change the value.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Reduction

variable {source : FloatFormat}

/-- Finite operands have no deciding infinity. -/
theorem decidingInfinity?_eq_none_of_isFinite (values : Array (Model source))
    (hfinite : ∀ value ∈ values.toList, isFinite value = true) :
    Internal.decidingInfinity? values = none := by
  unfold Internal.decidingInfinity?
  split
  · rfl
  · rw [Array.find?_eq_none]
    intro value hmem
    rw [isInfinite_eq_false_of_isFinite_eq_true value (hfinite value
      (Array.mem_toList_iff.mpr hmem))]
    exact Bool.false_ne_true

/-- A deciding infinity is an infinity. -/
theorem isInfinite_of_decidingInfinity? {values : Array (Model source)} {infinity : Model source}
    (h : Internal.decidingInfinity? values = some infinity) : isInfinite infinity = true := by
  unfold Internal.decidingInfinity? at h
  split at h
  · cases h
  · exact Array.find?_some h

/-- Without a deciding infinity, `sumAbs` is the correctly rounded sum of the magnitudes. -/
theorem sumAbs_status_eq_sum (destination : FloatFormat) (values : Array (Model source))
    (mode : IEEERoundingMode) (h : Internal.decidingInfinity? values = none) :
    sumAbs destination values mode (status := true) =
      sum destination (values.map abs) mode (status := true) := by
  simp only [sumAbs, h]

/-- A deciding infinity makes `sumAbs` the cast of its magnitude into the destination. -/
theorem sumAbs_status_of_decidingInfinity? (destination : FloatFormat)
    (values : Array (Model source)) (mode : IEEERoundingMode) {infinity : Model source}
    (h : Internal.decidingInfinity? values = some infinity) :
    sumAbs destination values mode (status := true) =
      cast source destination (abs infinity) mode (status := true) := by
  simp only [sumAbs, h]
  exact sum_status_singleton_eq_cast_status_of_isInfinite destination (abs infinity) mode
    (by rw [isInfinite_abs]; exact isInfinite_of_decidingInfinity? h)

/-- A deciding infinity makes `sumSquare` the cast of its magnitude into the destination. -/
theorem sumSquare_status_of_decidingInfinity? (destination : FloatFormat)
    (values : Array (Model source)) (mode : IEEERoundingMode) {infinity : Model source}
    (h : Internal.decidingInfinity? values = some infinity) :
    sumSquare destination values mode (status := true) =
      cast source destination (abs infinity) mode (status := true) := by
  simp only [sumSquare, h]
  exact sum_status_singleton_eq_cast_status_of_isInfinite destination (abs infinity) mode
    (by rw [isInfinite_abs]; exact isInfinite_of_decidingInfinity? h)

/-- Without a deciding infinity, `sumSquare` is the correctly rounded dot product of the array
with itself. -/
theorem dot_status_self_eq_sumSquare (destination : FloatFormat) (values : Array (Model source))
    (mode : IEEERoundingMode) (h : Internal.decidingInfinity? values = none) :
    dot destination values values mode (status := true) =
      .ok (sumSquare destination values mode (status := true)) := by
  simp [dot, Internal.Status.dot, sumSquare, h]

/-- `sumAbs` with `status := true` delivers the value of `sumAbs` in the same direction. -/
@[simp] theorem value_sumAbs (destination : FloatFormat) (values : Array (Model source))
    (mode : IEEERoundingMode) :
    (sumAbs destination values mode (status := true)).value = sumAbs destination values mode := by
  unfold sumAbs
  split <;> rfl

/-- `sumSquare` with `status := true` delivers the value of `sumSquare` in the same direction. -/
@[simp] theorem value_sumSquare (destination : FloatFormat) (values : Array (Model source))
    (mode : IEEERoundingMode) :
    (sumSquare destination values mode (status := true)).value =
      sumSquare destination values mode := by
  unfold sumSquare
  split <;> rfl

/--
For finite operands and a finite result in a conventional IEEE destination, nearest-even `sumAbs`
is one real rounding of the exact sum of the magnitudes.
-/
theorem toReal_sumAbs (destination : FloatFormat) (values : Array (Model source))
    (hfmt : destination.isIEEE = true)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hresult : isFinite (sumAbs destination values .nearest (status := true)).value = true) :
    toReal (sumAbs destination values .nearest (status := true)).value =
      roundAt destination (Semantics.finiteSum (values.toList.map abs) : ℝ) := by
  rw [sumAbs_status_eq_sum destination values .nearest
    (decidingInfinity?_eq_none_of_isFinite values hfinite)] at hresult ⊢
  rw [sum_status_value_toReal_eq_roundAt_of_finite destination (values.map abs) hfmt ?_ hresult,
    Array.toList_map]
  intro value hmem
  rw [Array.toList_map, List.mem_map] at hmem
  obtain ⟨original, horiginal, rfl⟩ := hmem
  rw [isFinite_abs]
  exact hfinite original horiginal

/--
For finite operands and a finite result in a conventional IEEE destination, nearest-even
`sumSquare` is one real rounding of the exact sum of the squares.
-/
theorem toReal_sumSquare (destination : FloatFormat) (values : Array (Model source))
    (exact : Rat) (hfmt : destination.isIEEE = true)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hspec : Semantics.finiteDot values.toList values.toList = .ok exact)
    (hresult : isFinite (sumSquare destination values .nearest (status := true)).value = true) :
    toReal (sumSquare destination values .nearest (status := true)).value =
      roundAt destination (exact : ℝ) := by
  have hposition : ∀ position (hposition : position < values.size),
      isFinite values[position] = true := fun position hposition =>
    hfinite _ (Array.mem_toList_iff.mpr (Array.getElem_mem hposition))
  exact dot_status_value_toReal_eq_roundAt_of_finite destination values values exact _ hfmt
    hposition hposition hspec
    (dot_status_self_eq_sumSquare destination values .nearest
      (decidingInfinity?_eq_none_of_isFinite values hfinite)) hresult

end Reduction
end Model
end FloatLib.Floats.Formats.BinaryInterchange
