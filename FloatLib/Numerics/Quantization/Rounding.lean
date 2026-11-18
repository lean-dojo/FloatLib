/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar formats as rounding maps

Block scaling sees a scalar format through one map: the exact value the format stores for an exact
input, after its rounding and its saturation or overflow policy. `Rounding K` is that map over any
ordered field `K`, so the same definitions compute over `ℚ` and carry the real-number theorems of
the concrete format families. Nothing here fixes a radix, a width or a rounding direction.

`Rounding.scaled E σ` is the format whose stored values are those of `E` multiplied by `σ`.
Quantizing an element of a block-scaled format is one rounding in the scaled format of its total
scale (`Block.reconstruct_eq`), and storing a scale under outer scales is one rounding in the scaled
format of those outer scales. So every per-element theorem of block scaling is a statement about
`scaled`, proved here once:

* `Budget.scaled`: an error budget `u * |x| + η + max 0 (|x| - M)` becomes
  `u * |x| + σ * η + max 0 (|x| - σ * M)`. The relative part is kept, and the absolute part and
  the saturation threshold scale with `σ`. `Budget.scaled_abs` is the same statement with `|σ|`
  for a scale of any sign, zero included.
* `scaled_round_eq_zero_iff`: the inputs stored as zero are the zero set of `E` multiplied by `σ`,
  with `scaled_round_eq_zero_iff_abs_le` for the closed symmetric zero set of nearest rounding
  with ties to zero. `Block.Binary` has the zero set of each rounding direction.
* `Fixes.scaled`: stored values are kept.
* `Nearest.round_eq_left`, `Nearest.round_eq_right`, `Nearest.round_eq_of_ge`,
  `Nearest.round_eq_of_le`: a nearest rounding is determined between two adjacent stored values
  away from their midpoint, and beyond its largest and least stored values. Two nearest roundings
  with the same stored values and the same value at each midpoint are therefore the same map,
  which is how an executable codec is identified with a real rounding (`OCP.MX.Standard`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

/--
A scalar storage format over the exact domain `K`, as block scaling uses it: `round x` is the exact
value stored for the exact input `x`, after the format's rounding and its saturation or overflow
policy.
-/
structure Rounding (K : Type*) where
  /-- Exact value stored for an exact input. -/
  round : K → K

namespace Rounding

section Field

variable {K : Type*} [Field K]

/-- The identity format, which stores every value exactly. -/
def exact : Rounding K where
  round x := x

/-- The format whose stored values are those of `E` multiplied by `σ`. -/
def scaled (E : Rounding K) (σ : K) : Rounding K where
  round x := E.round (x / σ) * σ

/-- Rounding in a scaled format divides by the scale, rounds, and multiplies back. -/
@[simp] theorem scaled_round (E : Rounding K) (σ x : K) :
    (E.scaled σ).round x = E.round (x / σ) * σ :=
  rfl

/-- Scaling by one changes nothing. -/
theorem scaled_one (E : Rounding K) : E.scaled 1 = E := by
  cases E
  simp [scaled]

/-- `E` stores `v` without error. -/
def Fixes (E : Rounding K) (v : K) : Prop :=
  E.round v = v

/-- The inputs `E` stores as zero. -/
def zeroSet (E : Rounding K) : Set K :=
  {x | E.round x = 0}

/-- Membership in the zero set is the equation `E.round x = 0`. -/
@[simp] theorem mem_zeroSet {E : Rounding K} {x : K} : x ∈ E.zeroSet ↔ E.round x = 0 :=
  Iff.rfl

/-- A scaled format stores the scaled stored values of `E`. -/
theorem Fixes.scaled {E : Rounding K} {v σ : K} (h : E.Fixes v) (hσ : σ ≠ 0) :
    (E.scaled σ).Fixes (v * σ) := by
  simp only [Fixes, scaled_round, mul_div_assoc, div_self hσ, mul_one] at h ⊢
  rw [h]

/-- A scaled format stores `x` as zero exactly when `E` stores `x / σ` as zero. -/
theorem scaled_round_eq_zero_iff (E : Rounding K) {σ : K} (hσ : σ ≠ 0) (x : K) :
    (E.scaled σ).round x = 0 ↔ x / σ ∈ E.zeroSet := by
  simp [hσ]

/--
Flush to zero for a directed rounding: if `E` stores exactly the inputs of a set `Z` as zero, the
scaled format stores exactly the inputs `x` with `x / σ` in `Z` as zero. Rounding up has
`Z = Set.Ioc (-m) 0` and rounding down `Z = Set.Ico 0 m`, with `m` the least positive stored value.
-/
theorem scaled_round_eq_zero_iff_mem {E : Rounding K} {Z : Set K}
    (h : ∀ y, E.round y = 0 ↔ y ∈ Z) {σ : K} (hσ : σ ≠ 0) (x : K) :
    (E.scaled σ).round x = 0 ↔ x / σ ∈ Z := by
  rw [scaled_round_eq_zero_iff E hσ, mem_zeroSet, h]

end Field

section Order

variable {K : Type*} [LinearOrder K]

/-- A monotone rounding is constant between two inputs it stores as the same value. -/
theorem round_eq_of_le_of_le {E : Rounding K} (h : Monotone E.round) {a b y v : K}
    (ha : E.round a = v) (hb : E.round b = v) (hay : a ≤ y) (hyb : y ≤ b) : E.round y = v :=
  le_antisymm (hb ▸ h hyb) (ha ▸ h hay)

end Order

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/--
Error budget of a format: relative error `u`, absolute error `η`, and the loss of saturating at
magnitude `M`. For a binary format with precision `p`, least exponent `emin` and largest finite
value `M`, nearest rounding has `u = 2 ^ (-p)` and `η = 2 ^ (emin - 1)`.
-/
def Budget (E : Rounding K) (u η M : K) : Prop :=
  ∀ x, |E.round x - x| ≤ u * |x| + η + max 0 (|x| - M)

/-- Inside the saturation range the budget is the mixed relative and absolute bound. -/
theorem Budget.abs_sub_le {E : Rounding K} {u η M x : K} (h : E.Budget u η M)
    (hx : |x| ≤ M) : |E.round x - x| ≤ u * |x| + η := by
  simpa [max_eq_left (sub_nonpos.mpr hx)] using h x

/-- A budget stays valid with larger error terms and an earlier saturation threshold. -/
theorem Budget.mono {E : Rounding K} {u η M u' η' M' : K} (h : E.Budget u η M)
    (hu : u ≤ u') (hη : η ≤ η') (hM : M' ≤ M) : E.Budget u' η' M' := by
  intro x
  have hmax : max 0 (|x| - M) ≤ max 0 (|x| - M') :=
    max_le_max le_rfl (sub_le_sub_left hM _)
  have hmul : u * |x| ≤ u' * |x| := mul_le_mul_of_nonneg_right hu (abs_nonneg x)
  exact (h x).trans (add_le_add (add_le_add hmul hη) hmax)

/-- The exact format has the zero budget at every threshold. -/
theorem exact_budget (M : K) : (exact : Rounding K).Budget 0 0 M := by
  intro x
  simp [exact]

/--
The error of a scaled rounding is the error of `E` at the scaled input, multiplied by the scale.
-/
theorem abs_scaled_round_sub (E : Rounding K) {σ : K} (hσ : 0 < σ) (x : K) :
    |(E.scaled σ).round x - x| = |E.round (x / σ) - x / σ| * σ := by
  have hx : x / σ * σ = x := div_mul_cancel₀ x hσ.ne'
  have h : (E.scaled σ).round x - x = (E.round (x / σ) - x / σ) * σ := by
    rw [scaled_round, sub_mul, hx]
  rw [h, abs_mul, abs_of_pos hσ]

/--
Scaling keeps the relative error and multiplies the absolute error and the saturation threshold
by the scale.
-/
theorem Budget.scaled {E : Rounding K} {u η M σ : K} (h : E.Budget u η M) (hσ : 0 < σ) :
    (E.scaled σ).Budget u (σ * η) (σ * M) := by
  intro x
  have habs : |x / σ| * σ = |x| := by
    rw [abs_div, abs_of_pos hσ, div_mul_cancel₀ _ hσ.ne']
  have hmax : max 0 (|x / σ| - M) * σ = max 0 (|x| - σ * M) := by
    rw [max_mul_of_nonneg _ _ hσ.le, zero_mul, sub_mul, habs, mul_comm M σ]
  calc |(E.scaled σ).round x - x| = |E.round (x / σ) - x / σ| * σ :=
        abs_scaled_round_sub E hσ x
    _ ≤ (u * |x / σ| + η + max 0 (|x / σ| - M)) * σ :=
        mul_le_mul_of_nonneg_right (h _) hσ.le
    _ = u * |x| + σ * η + max 0 (|x| - σ * M) := by
        rw [add_mul, add_mul, hmax, mul_assoc, habs, mul_comm η σ]

/--
The budget of a scaled format for a scale of any sign, zero included: the absolute error and the
saturation threshold are multiplied by the magnitude of the scale. A zero scale stores zero, and
the saturation term then covers the whole input.
-/
theorem Budget.scaled_abs {E : Rounding K} {u η M : K} (h : E.Budget u η M) (hu : 0 ≤ u)
    (σ : K) : (E.scaled σ).Budget u (|σ| * η) (|σ| * M) := by
  intro x
  by_cases hσ : σ = 0
  · subst σ
    simp only [scaled_round, mul_zero, zero_sub, abs_neg, abs_zero, zero_mul, sub_zero, add_zero]
    exact (le_max_right 0 |x|).trans (le_add_of_nonneg_left
      (mul_nonneg hu (abs_nonneg x)))
  · have hpos : 0 < |σ| := abs_pos.mpr hσ
    have hx : x / σ * σ = x := div_mul_cancel₀ x hσ
    have hrw : (E.scaled σ).round x - x = (E.round (x / σ) - x / σ) * σ := by
      rw [scaled_round, sub_mul, hx]
    have habs : |x / σ| * |σ| = |x| := by
      rw [abs_div, div_mul_cancel₀ _ hpos.ne']
    have hmax : max 0 (|x / σ| - M) * |σ| = max 0 (|x| - |σ| * M) := by
      rw [max_mul_of_nonneg _ _ hpos.le, zero_mul, sub_mul, habs, mul_comm M |σ|]
    calc |(E.scaled σ).round x - x| = |E.round (x / σ) - x / σ| * |σ| := by
          rw [hrw, abs_mul]
      _ ≤ (u * |x / σ| + η + max 0 (|x / σ| - M)) * |σ| :=
          mul_le_mul_of_nonneg_right (h _) hpos.le
      _ = u * |x| + |σ| * η + max 0 (|x| - |σ| * M) := by
          rw [add_mul, add_mul, hmax, mul_assoc, habs, mul_comm η |σ|]

/--
Best approximation is kept by scaling. If `E` is at least as close to every input as each value
of a set `R`, the scaled format is at least as close to every input as each value of `R`
multiplied by the scale. For a nearest rounding onto the finite values of an element format, the
reconstructed element is at least as close to the input as any other element value at the same
scale.
-/
theorem abs_scaled_round_sub_le_of_nearest {E : Rounding K} {R : Set K}
    (h : ∀ y, ∀ v ∈ R, |E.round y - y| ≤ |v - y|) {σ : K} (hσ : 0 < σ) (x : K) {v : K}
    (hv : v ∈ R) : |(E.scaled σ).round x - x| ≤ |v * σ - x| := by
  rw [abs_scaled_round_sub E hσ x]
  have hx : x / σ * σ = x := div_mul_cancel₀ x hσ.ne'
  have h2 : |v * σ - x| = |v - x / σ| * σ := by
    have h3 : v * σ - x = (v - x / σ) * σ := by rw [sub_mul, hx]
    rw [h3, abs_mul, abs_of_pos hσ]
  rw [h2]
  exact mul_le_mul_of_nonneg_right (h _ v hv) hσ.le

/-- `E` stores, for every input, a value at least as close to it as every other stored value.
Rounding to nearest onto a set of values has this property under any tie rule. -/
def Nearest (E : Rounding K) : Prop :=
  ∀ x y, |E.round x - x| ≤ |E.round y - x|

/--
A nearest rounding between two stored values with no stored value strictly between them: an
input from `a` up to their midpoint, the midpoint excluded, is stored as `a`. The premise `hm`
states the absence of a stored value in between as a fact about one input: the midpoint is stored
as `a` or as `b`.
-/
theorem Nearest.round_eq_left {E : Rounding K} (h : E.Nearest) {a b q : K} (ha : E.Fixes a)
    (hm : E.round ((a + b) / 2) = a ∨ E.round ((a + b) / 2) = b) (haq : a ≤ q)
    (hq : q < (a + b) / 2) : E.round q = a := by
  have h1 := h q a
  rw [show E.round a = a from ha, abs_of_nonpos (sub_nonpos.mpr haq)] at h1
  have h1' := abs_le.mp h1
  by_contra hne
  have hlt : a < E.round q := lt_of_le_of_ne (by linarith [h1'.1]) (Ne.symm hne)
  have h2 := h ((a + b) / 2) q
  have h3 : |E.round q - (a + b) / 2| < (b - a) / 2 :=
    abs_lt.mpr ⟨by linarith, by linarith [h1'.2]⟩
  rcases hm with hm | hm
  · rw [hm, abs_of_nonpos (by linarith)] at h2
    linarith
  · rw [hm, abs_of_nonneg (by linarith)] at h2
    linarith

/-- The other half of `Nearest.round_eq_left`: an input above the midpoint, up to `b`, is stored
as `b`. -/
theorem Nearest.round_eq_right {E : Rounding K} (h : E.Nearest) {a b q : K} (hb : E.Fixes b)
    (hm : E.round ((a + b) / 2) = a ∨ E.round ((a + b) / 2) = b) (hq : (a + b) / 2 < q)
    (hqb : q ≤ b) : E.round q = b := by
  have h1 := h q b
  rw [show E.round b = b from hb, abs_of_nonneg (sub_nonneg.mpr hqb)] at h1
  have h1' := abs_le.mp h1
  by_contra hne
  have hlt : E.round q < b := lt_of_le_of_ne (by linarith [h1'.2]) hne
  have h2 := h ((a + b) / 2) q
  have h3 : |E.round q - (a + b) / 2| < (b - a) / 2 :=
    abs_lt.mpr ⟨by linarith [h1'.1], by linarith⟩
  rcases hm with hm | hm
  · rw [hm, abs_of_nonpos (by linarith)] at h2
    linarith
  · rw [hm, abs_of_nonneg (by linarith)] at h2
    linarith

/-- A nearest rounding stores every input at or above its largest stored value as that value. -/
theorem Nearest.round_eq_of_ge {E : Rounding K} (h : E.Nearest) {b q : K} (hb : E.Fixes b)
    (hle : ∀ x, E.round x ≤ b) (hq : b ≤ q) : E.round q = b := by
  have h1 := h q b
  rw [show E.round b = b from hb,
    abs_of_nonpos (sub_nonpos.mpr ((hle q).trans hq)),
    abs_of_nonpos (sub_nonpos.mpr hq), neg_sub, neg_sub] at h1
  exact le_antisymm (hle q) ((sub_le_sub_iff_left q).mp h1)

/-- A nearest rounding stores every input at or below its least stored value as that value. -/
theorem Nearest.round_eq_of_le {E : Rounding K} (h : E.Nearest) {a q : K} (ha : E.Fixes a)
    (hge : ∀ x, a ≤ E.round x) (hq : q ≤ a) : E.round q = a := by
  have h1 := h q a
  rw [show E.round a = a from ha,
    abs_of_nonneg (sub_nonneg.mpr (hq.trans (hge q))),
    abs_of_nonneg (sub_nonneg.mpr hq)] at h1
  exact le_antisymm ((sub_le_sub_iff_right q).mp h1) (hge q)

/--
Flush to zero with ties to zero: if `E` stores exactly the inputs of magnitude at most `τ` as
zero, the scaled format stores exactly the inputs of magnitude at most `τ * σ` as zero. Nearest
rounding with ties to even has this form, with `τ` half the least positive stored value.
-/
theorem scaled_round_eq_zero_iff_abs_le {E : Rounding K} {τ σ : K}
    (h : ∀ y, E.round y = 0 ↔ |y| ≤ τ) (hσ : 0 < σ) (x : K) :
    (E.scaled σ).round x = 0 ↔ |x| ≤ τ * σ := by
  rw [scaled_round_eq_zero_iff E hσ.ne', mem_zeroSet, h, abs_div, abs_of_pos hσ,
    div_le_iff₀ hσ]

end Rounding

end FloatLib.Floats.Formats.Block
