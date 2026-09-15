/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Semantics

/-!
# Decimal arithmetic range and numerical error

Every operation returns a valid destination datum. For finite operands and a
result without overflow, the nearest-mode error bounds compare the returned
value with the exact rational sum, difference, product, quotient, or fused
expression. Division additionally requires a nonzero divisor. The fused bound
concerns `x * y + z` directly, without a rounded intermediate product.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

theorem nanResult_valid (f : Format) (s : Bool) (p : Nat) (invalid : Bool) :
    (nanResult f s p invalid).value.Valid f := by
  have hp := f.payloadBound_pos
  simp only [nanResult, Datum.Valid]
  split <;> omega

theorem invalidResult_valid (f : Format) : invalidResult.value.Valid f :=
  f.payloadBound_pos

/-- Addition always returns a valid representation, including exceptional operands. -/
theorem add_valid (f : Format) (mode : RoundingMode) (x y : Datum) :
    (add f mode x y).value.Valid f := by
  cases x <;> cases y <;>
    simp only [add]
  all_goals first
    | exact project_valid ..
    | exact nanResult_valid ..
    | trivial
    | split <;> first | trivial | exact invalidResult_valid f

theorem sub_valid (f : Format) (mode : RoundingMode) (x y : Datum) :
    (sub f mode x y).value.Valid f := by
  cases x <;> cases y <;> simp only [sub]
  all_goals first | exact nanResult_valid .. | exact add_valid ..

theorem mul_valid (f : Format) (mode : RoundingMode) (x y : Datum) :
    (mul f mode x y).value.Valid f := by
  cases x <;> cases y <;> simp only [mul]
  all_goals first
    | exact project_valid ..
    | exact nanResult_valid ..
    | trivial
    | split <;> first | trivial | exact invalidResult_valid f

theorem div_valid (f : Format) (mode : RoundingMode) (x y : Datum) :
    (div f mode x y).value.Valid f := by
  cases x <;> cases y <;> simp only [div]
  all_goals first
    | exact nanResult_valid ..
    | exact invalidResult_valid f
    | trivial
    | (rw [Datum.valid_quantum_iff]
       have hb := f.coefficientBound_pos
       exact ⟨hb, le_rfl, f.minQuantum_le_maxQuantum⟩)
    | (split
       · split <;> first | exact invalidResult_valid f | trivial
       · exact project_valid ..)

theorem addInfinity_valid (f : Format) (s : Bool) (z : Datum) :
    (addInfinity f s z).value.Valid f := by
  cases z <;> simp only [addInfinity]
  all_goals first
    | exact nanResult_valid ..
    | trivial
    | split <;> first | trivial | exact invalidResult_valid f

theorem fma_valid (f : Format) (mode : RoundingMode) (x y z : Datum) :
    (fma f mode x y z).value.Valid f := by
  cases x <;> cases y <;> cases z <;> simp only [fma]
  all_goals first
    | exact nanResult_valid ..
    | exact project_valid ..
    | exact addInfinity_valid ..
    | trivial
    | split <;> first | exact invalidResult_valid f | exact addInfinity_valid ..

/-- Nearest addition is within half a decimal grid unit of the exact sum. -/
theorem add_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (add f mode x y).status.overflow = false) :
    ∃ value, (add f mode x y).value.toRat? = some value ∧
      |value - (a + b)| ≤ (10 : ℚ) ^ roundingQuantum f |a + b| / 2 := by
  cases x <;> cases y <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy
  subst a
  subst b
  exact project_error_le_half f mode hm _ _ _ hfinite

theorem sub_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (sub f mode x y).status.overflow = false) :
    ∃ value, (sub f mode x y).value.toRat? = some value ∧
      |value - (a - b)| ≤ (10 : ℚ) ^ roundingQuantum f |a - b| / 2 := by
  cases x <;> cases y <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy
  subst a
  subst b
  rename_i sx cx qx sy cy qy
  have hn : Datum.finiteValue (!sy) cy qy = -Datum.finiteValue sy cy qy := by
    cases sy <;> simp [Datum.finiteValue]
  simp only [sub, Datum.negate, add, hn, ← sub_eq_add_neg] at hfinite ⊢
  exact project_error_le_half f mode hm _ _ _ hfinite

theorem mul_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (mul f mode x y).status.overflow = false) :
    ∃ value, (mul f mode x y).value.toRat? = some value ∧
      |value - a * b| ≤ (10 : ℚ) ^ roundingQuantum f |a * b| / 2 := by
  cases x <;> cases y <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy
  subst a
  subst b
  exact project_error_le_half f mode hm _ _ _ hfinite

theorem div_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hb : b ≠ 0) (hfinite : (div f mode x y).status.overflow = false) :
    ∃ value, (div f mode x y).value.toRat? = some value ∧
      |value - a / b| ≤ (10 : ℚ) ^ roundingQuantum f |a / b| / 2 := by
  cases x <;> cases y <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy
  subst a
  subst b
  rename_i sx cx qx sy cy qy
  have hc : cy ≠ 0 := by
    intro h
    simp [h] at hb
  simp only [div, ite_eq_right hc] at hfinite ⊢
  exact project_error_le_half f mode hm _ _ _ hfinite

/-- FMA rounds the exact fused expression, including cancellation across the format range. -/
theorem fma_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (x y z : Datum) (a b c : ℚ)
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hz : z.toRat? = some c)
    (hfinite : (fma f mode x y z).status.overflow = false) :
    ∃ value, (fma f mode x y z).value.toRat? = some value ∧
      |value - (a * b + c)| ≤ (10 : ℚ) ^ roundingQuantum f |a * b + c| / 2 := by
  cases x <;> cases y <;> cases z <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy hz
  subst a
  subst b
  subst c
  exact project_error_le_half f mode hm _ _ _ hfinite

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
