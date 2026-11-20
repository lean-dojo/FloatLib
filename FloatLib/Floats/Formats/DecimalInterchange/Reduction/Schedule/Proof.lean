/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Reduction.Schedule.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Format.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.ScaleProof
public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Rounding
public import FloatLib.Numerics.Reduction.Error

/-!
# Contracts of the decimal reductions in a chosen order and accumulator format

For every decimal accumulator and destination format, rounding direction and association order:

* `reduceInOrder_eq_reduceAlong`: the left-to-right loop is `reduceAlong` along the left chain
  of its inputs.
* `reduceAlong_valid`, `reduceInOrder_valid`: the result is a datum of the destination format.
* `abs_eval_sub_le`: for finite terms and a result without `overflow`, the accumulated value is
  finite, and its distance from the exact sum of the terms is at most
  `ReductionTree.mixedBudget` with the relative allowance `10 ^ (1 - precision)` and the
  absolute allowance `10 ^ minQuantum` of the accumulator at each addition: each addition is
  less than one unit of its rounding grid from the exact sum of its operands
  (`add_error_lt_one`), in every rounding direction.
* `abs_reduceAlong_sub_le`: the delivered result adds less than one unit of the rounding grid
  of the destination at the accumulated value.

The `overflow` premise is on the flags of the result, which accumulate over every step, so it
is observable. No other hypothesis on the intermediate results is needed.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

open FloatLib.Numerics
open Transcendentals (toReal toReal_of_toRat?_eq_some)

/-- One unit of the rounding grid at a nonnegative magnitude is at most the magnitude times
`10 ^ (1 - precision)`, plus the least quantum. -/
theorem zpow_roundingQuantum_le (f : Format) {x : ℚ} (hx : 0 ≤ x) :
    (10 : ℚ) ^ roundingQuantum f x ≤ x / f.payloadBound + (10 : ℚ) ^ f.minQuantum := by
  have hbound : (0 : ℚ) < f.payloadBound := by exact_mod_cast f.payloadBound_pos
  rcases (roundingQuantum_ge_min f x).eq_or_lt with h | h
  · rw [← h]
    exact le_add_of_nonneg_left (div_nonneg hx hbound.le)
  · have hpow : (0 : ℚ) < (10 : ℚ) ^ roundingQuantum f x := zpow_pos (by norm_num) _
    have hlower := payloadBound_le_div_roundingQuantum f h
    rw [le_div_iff₀ hpow] at hlower
    have hgrid : (10 : ℚ) ^ roundingQuantum f x ≤ x / f.payloadBound := by
      rw [le_div_iff₀ hbound]
      linarith
    exact hgrid.trans (le_add_of_nonneg_right (zpow_pos (by norm_num) _).le)

namespace Arithmetic

open Conversion (convertFormat convertFormat_valid)

/-- In every rounding direction, an addition without overflow is less than one unit of the
rounding grid from the exact sum. -/
theorem add_error_lt_one (f : Format) (mode : RoundingMode) (x y : Datum) (a b : ℚ)
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (add f mode x y).status.overflow = false) :
    ∃ value, (add f mode x y).value.toRat? = some value ∧
      |value - (a + b)| < (10 : ℚ) ^ roundingQuantum f |a + b| := by
  cases x <;> cases y <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy
  subst a
  subst b
  exact project_error_lt_one f mode _ _ _ hfinite

namespace Reduction

/--
One addition of a schedule: for finite operands and no `overflow` among the accumulated flags,
the sum is finite and within the relative allowance `10 ^ (1 - precision)` and the absolute
allowance `10 ^ minQuantum` of the exact sum.
-/
theorem lift₂_add_error (acc : Format) (mode : RoundingMode) {left right : Outcome} {a b : ℚ}
    (hleft : left.value.toRat? = some a) (hright : right.value.toRat? = some b)
    (hfinite : (lift₂ (add acc mode) left right).status.overflow = false) :
    ∃ value, (lift₂ (add acc mode) left right).value.toRat? = some value ∧
      |value - (a + b)| ≤ (|a| + |b|) / acc.payloadBound + (10 : ℚ) ^ acc.minQuantum := by
  have hsum : (add acc mode left.value right.value).status.overflow = false := by
    simp only [lift₂, IEEEStatus.union, Bool.or_eq_false_iff] at hfinite
    exact hfinite.2
  obtain ⟨value, hvalue, herror⟩ := add_error_lt_one acc mode _ _ a b hleft hright hsum
  have hbound : (0 : ℚ) < acc.payloadBound := by exact_mod_cast acc.payloadBound_pos
  refine ⟨value, hvalue, herror.le.trans ((zpow_roundingQuantum_le acc (abs_nonneg _)).trans ?_)⟩
  gcongr
  exact abs_add_le a b

/--
Along a schedule with finite terms whose accumulated flags have no `overflow`, the accumulated
value is finite and every addition is within its allowances of the exact sum of its operands.
-/
theorem eval_spec {α : Type} (acc : Format) (mode : RoundingMode) (term : α → Outcome) :
    ∀ schedule : ReductionTree α,
      (∀ x ∈ schedule.leaves, ∃ value, (term x).value.toRat? = some value) →
      (schedule.eval (lift₂ (add acc mode)) term).status.overflow = false →
      (∃ value, (schedule.eval (lift₂ (add acc mode)) term).value.toRat? = some value) ∧
        schedule.AllNodes (lift₂ (add acc mode)) term fun x y =>
          |toReal (lift₂ (add acc mode) x y).value - (toReal x.value + toReal y.value)| ≤
            (1 / (acc.payloadBound : ℝ)) * (|toReal x.value| + |toReal y.value|) +
              (10 : ℝ) ^ acc.minQuantum
  | .leaf x, hterm, _ => ⟨hterm x (by simp [ReductionTree.leaves]), trivial⟩
  | .node left right, hterm, hfinite => by
      have hflags : (left.eval (lift₂ (add acc mode)) term).status.overflow = false ∧
          (right.eval (lift₂ (add acc mode)) term).status.overflow = false := by
        simp only [ReductionTree.eval, lift₂, IEEEStatus.union, Bool.or_eq_false_iff] at hfinite
        exact hfinite.1
      obtain ⟨⟨a, ha⟩, hallLeft⟩ := eval_spec acc mode term left
        (fun x hx => hterm x (by simp [ReductionTree.leaves, hx])) hflags.1
      obtain ⟨⟨b, hb⟩, hallRight⟩ := eval_spec acc mode term right
        (fun x hx => hterm x (by simp [ReductionTree.leaves, hx])) hflags.2
      obtain ⟨value, hvalue, herror⟩ := lift₂_add_error acc mode ha hb hfinite
      refine ⟨⟨value, hvalue⟩, hallLeft, hallRight, ?_⟩
      beta_reduce
      rw [toReal_of_toRat?_eq_some hvalue, toReal_of_toRat?_eq_some ha,
        toReal_of_toRat?_eq_some hb, one_div, inv_mul_eq_div]
      have hcast := (Rat.cast_le (K := ℝ)).mpr herror
      push_cast at hcast
      exact hcast

end Reduction

open Reduction

variable {α : Type}

/--
The left-to-right reduction of a nonempty list is the reduction along the left chain of its
inputs.
-/
theorem reduceInOrder_eq_reduceAlong (acc out : Format) (mode : RoundingMode)
    (term : α → Outcome) (first : α) (rest : List α) :
    reduceInOrder acc out mode term (first :: rest) =
      reduceAlong acc out mode term (ReductionTree.leftChain first rest) := by
  rw [reduceInOrder, reduceAlong, ReductionTree.eval_leftChain]

/-- A reduction along a schedule returns a datum of the destination format. -/
theorem reduceAlong_valid (acc out : Format) (mode : RoundingMode) (term : α → Outcome)
    (schedule : ReductionTree α) : (reduceAlong acc out mode term schedule).value.Valid out :=
  convertFormat_valid out mode _

/-- A reduction from left to right returns a datum of the destination format. -/
theorem reduceInOrder_valid (acc out : Format) (mode : RoundingMode) (term : α → Outcome)
    (values : List α) : (reduceInOrder acc out mode term values).value.Valid out := by
  cases values with
  | nil => exact project_valid ..
  | cons first rest => exact convertFormat_valid out mode _

/--
**Every association order, in every decimal accumulator and rounding direction.** For finite
terms and accumulated flags without `overflow`, the accumulated value is finite, and its
distance from the exact sum of the terms in the order of the schedule is at most the mixed
budget of the schedule with the relative allowance `10 ^ (1 - precision)` and the absolute
allowance `10 ^ minQuantum` of the accumulator at each addition.
-/
theorem abs_eval_sub_le (acc : Format) (mode : RoundingMode) (term : α → Outcome)
    (schedule : ReductionTree α)
    (hterm : ∀ x ∈ schedule.leaves, ∃ value, (term x).value.toRat? = some value)
    (hfinite : (schedule.eval (lift₂ (add acc mode)) term).status.overflow = false) :
    (∃ value, (schedule.eval (lift₂ (add acc mode)) term).value.toRat? = some value) ∧
      |toReal (schedule.eval (lift₂ (add acc mode)) term).value -
          schedule.eval (· + ·) (fun x => toReal (term x).value)| ≤
        schedule.mixedBudget (fun x => toReal (term x).value) (1 / (acc.payloadBound : ℝ))
          ((10 : ℝ) ^ acc.minQuantum) := by
  obtain ⟨hvalue, hall⟩ := eval_spec acc mode term schedule hterm hfinite
  exact ⟨hvalue, schedule.abs_eval_sub_exact_le_mixedBudget _ term (fun outcome =>
    toReal outcome.value) _ _ (by positivity) hall⟩

/--
The delivered result of a reduction along a schedule: for finite terms and a result without
`overflow`, it is finite, and its distance from the exact sum of the terms is at most the
budget of `abs_eval_sub_le` for the additions in the accumulator, plus one unit of the
rounding grid of the destination at the accumulated value `total` for the final conversion.
-/
theorem abs_reduceAlong_sub_le (acc out : Format) (mode : RoundingMode) (term : α → Outcome)
    (schedule : ReductionTree α)
    (hterm : ∀ x ∈ schedule.leaves, ∃ value, (term x).value.toRat? = some value)
    (hfinite : (reduceAlong acc out mode term schedule).status.overflow = false) :
    ∃ total value,
      (schedule.eval (lift₂ (add acc mode)) term).value.toRat? = some total ∧
      (reduceAlong acc out mode term schedule).value.toRat? = some value ∧
      |(value : ℝ) - schedule.eval (· + ·) (fun x => toReal (term x).value)| ≤
        schedule.mixedBudget (fun x => toReal (term x).value) (1 / (acc.payloadBound : ℝ))
            ((10 : ℝ) ^ acc.minQuantum) +
          (10 : ℝ) ^ roundingQuantum out |total| := by
  have hflags : (schedule.eval (lift₂ (add acc mode)) term).status.overflow = false ∧
      (convertFormat out mode (schedule.eval (lift₂ (add acc mode)) term).value).status.overflow =
        false := by
    simpa only [reduceAlong, finish, IEEEStatus.union, Bool.or_eq_false_iff] using hfinite
  obtain ⟨⟨total, htotal⟩, hbound⟩ := abs_eval_sub_le acc mode term schedule hterm hflags.1
  have hconvert := hflags.2
  have hresult : (reduceAlong acc out mode term schedule).value =
      (convertFormat out mode (schedule.eval (lift₂ (add acc mode)) term).value).value := rfl
  rw [hresult]
  clear hresult hfinite hflags
  generalize schedule.eval (lift₂ (add acc mode)) term = accumulated at *
  obtain ⟨datum, status⟩ := accumulated
  cases datum with
  | finite negative coefficient quantum =>
      have hexact : (Datum.finite negative coefficient quantum).toRat? =
          some (Datum.finiteValue negative coefficient quantum) := by
        simp [Datum.toRat?_eq, Datum.finiteValue]
      obtain rfl : total = Datum.finiteValue negative coefficient quantum := by
        rw [hexact] at htotal
        exact (Option.some.inj htotal).symm
      obtain ⟨value, hvalue, herror⟩ := project_error_lt_one out mode _ quantum negative hconvert
      refine ⟨_, value, hexact, hvalue, ?_⟩
      rw [toReal_of_toRat?_eq_some hexact] at hbound
      have hcast := (Rat.cast_lt (K := ℝ)).mpr herror
      push_cast at hcast
      have htriangle := abs_sub_le (value : ℝ)
        ((Datum.finiteValue negative coefficient quantum : ℚ) : ℝ)
        (schedule.eval (· + ·) (fun x => toReal (term x).value))
      linarith
  | infinity negative => simp [Datum.toRat?_eq] at htotal
  | nan negative signaling payload => simp [Datum.toRat?_eq] at htotal

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
