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

The file opens with general facts about the exact value of a datum that the other decimal proofs
use: which datums have a given rational value (`Datum.toRat?_eq_some_iff`,
`Datum.toRat?_eq_some_zero_iff`) and how negation changes it (`Datum.negate_toRat?`,
`Datum.negate_toRat?_of_eq_some`). They are proved here, next to the `Datum.finiteValue` of
`Arithmetic.Runtime`, and not in `Sign.Proof`, so that the root and power proofs can use them
without importing the codecs that `Sign.Proof` depends on.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- A datum has an exact rational value exactly when it is finite, and that value is its signed
coefficient times its radix power (zero for either signed zero). -/
theorem Datum.toRat?_eq_some_iff {x : Datum} {v : ℚ} :
    x.toRat? = some v ↔ ∃ s c q, x = .finite s c q ∧ v = Datum.finiteValue s c q := by
  constructor
  · intro hv
    cases x with
    | finite s c q =>
        refine ⟨s, c, q, rfl, ?_⟩
        rw [Datum.toRat?_eq] at hv
        exact (Option.some.inj hv).symm
    | infinity s => contradiction
    | nan s t p => contradiction
  · rintro ⟨s, c, q, rfl, rfl⟩
    rw [Datum.toRat?_eq]
    rfl

/-- A datum has exact value zero exactly when it is a zero of either sign, at any quantum. -/
theorem Datum.toRat?_eq_some_zero_iff {x : Datum} :
    x.toRat? = some 0 ↔ ∃ s q, x = .finite s 0 q := by
  constructor
  · intro hx
    obtain ⟨s, c, q, rfl, h⟩ := Datum.toRat?_eq_some_iff.mp hx
    obtain rfl : c = 0 := by
      by_contra hc
      cases s <;> simp [Datum.finiteValue, hc, (zpow_pos (by norm_num : (0 : ℚ) < 10) q).ne'] at h
    exact ⟨s, q, rfl⟩
  · rintro ⟨s, q, rfl⟩
    rfl

/-- Reversing a finite sign negates the exact rational, including at zero. -/
theorem Datum.negate_toRat? (d : Datum) :
    d.negate.toRat? = d.toRat?.map (- ·) := by
  cases d with
  | finite s c q => cases s <;> simp [Datum.negate, Datum.toRat?_eq]
  | infinity s => rfl
  | nan s t p => rfl

/-- A datum with exact value `a` negates to a datum with exact value `-a`. -/
theorem Datum.negate_toRat?_of_eq_some {d : Datum} {a : ℚ} (h : d.toRat? = some a) :
    d.negate.toRat? = some (-a) := by
  rw [Datum.negate_toRat?, h]
  rfl

namespace Arithmetic

/-- A propagated quiet NaN is always valid: a payload that does not fit the destination is replaced
by zero. -/
theorem nanResult_valid (f : Format) (s : Bool) (p : Nat) (invalid : Bool) :
    (nanResult f s p invalid).value.Valid f := by
  have hp := f.payloadBound_pos
  simp only [nanResult, Datum.Valid]
  split <;> omega

/-- The default invalid-operation NaN, a positive quiet NaN with payload zero, is valid in every
format. -/
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

/-- Subtraction always returns a valid representation, including exceptional operands. -/
theorem sub_valid (f : Format) (mode : RoundingMode) (x y : Datum) :
    (sub f mode x y).value.Valid f := by
  cases x <;> cases y <;> simp only [sub]
  all_goals first | exact nanResult_valid .. | exact add_valid ..

/-- Multiplication always returns a valid representation, including exceptional operands. -/
theorem mul_valid (f : Format) (mode : RoundingMode) (x y : Datum) :
    (mul f mode x y).value.Valid f := by
  cases x <;> cases y <;> simp only [mul]
  all_goals first
    | exact project_valid ..
    | exact nanResult_valid ..
    | trivial
    | split <;> first | trivial | exact invalidResult_valid f

/-- Division always returns a valid representation, including exceptional operands and division by
zero. -/
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

/-- Adding a signed infinity to a third fused operand always returns a valid representation. -/
theorem addInfinity_valid (f : Format) (s : Bool) (z : Datum) :
    (addInfinity f s z).value.Valid f := by
  cases z <;> simp only [addInfinity]
  all_goals first
    | exact nanResult_valid ..
    | trivial
    | split <;> first | trivial | exact invalidResult_valid f

/-- Fused multiply-add always returns a valid representation, including exceptional operands. -/
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
    (hm : mode = .nearest ∨ mode = .nearestAway)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (add f mode x y).status.overflow = false) :
    ∃ value, (add f mode x y).value.toRat? = some value ∧
      |value - (a + b)| ≤ (10 : ℚ) ^ roundingQuantum f |a + b| / 2 := by
  cases x <;> cases y <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy
  subst a
  subst b
  exact project_error_le_half f mode hm _ _ _ hfinite

/-- Nearest subtraction of two finite datums, without overflow, is within half a decimal grid unit
of the exact difference. -/
theorem sub_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearest ∨ mode = .nearestAway)
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

/-- Nearest multiplication of two finite datums, without overflow, is within half a decimal grid
unit of the exact product. -/
theorem mul_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearest ∨ mode = .nearestAway)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (mul f mode x y).status.overflow = false) :
    ∃ value, (mul f mode x y).value.toRat? = some value ∧
      |value - a * b| ≤ (10 : ℚ) ^ roundingQuantum f |a * b| / 2 := by
  cases x <;> cases y <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy
  subst a
  subst b
  exact project_error_le_half f mode hm _ _ _ hfinite

/-- Nearest division of a finite datum by a nonzero finite datum, without overflow, is within half a
decimal grid unit of the exact quotient. -/
theorem div_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearest ∨ mode = .nearestAway)
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
    (hm : mode = .nearest ∨ mode = .nearestAway)
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
