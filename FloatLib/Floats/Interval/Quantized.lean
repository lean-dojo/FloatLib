/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Data.EReal.Basic
public import FloatLib.Floats.Interval.RealBounds
public import FloatLib.Floats.Interval.Rounders

/-!
# Quantized real intervals and unbounded division enclosures

Intervals are propagated over `ℝ` or `EReal`, then their endpoints are snapped outward to a chosen
representable grid, a Flocq-style $(\beta,\mathtt{fexp})$ format.

The usual workflow is:

- start from a real interval $x\in[\mathtt{lo},\mathtt{hi}]$;
- propagate it through arithmetic or a monotone nonlinear function; and
- round each new endpoint outward with a `Rounder`.

The layer is meant for real-valued enclosure proofs, not bit-level IEEE execution. It therefore
has no NaN payloads, signed-zero rules, or status flags.

Division returns an `EReal` interval so that a denominator interval containing zero can be enclosed
by $[-\infty,+\infty]$.

References:
- IEEE 1788-2015 (interval arithmetic).
- Moore, Kearfott, Cloud, *Introduction to Interval Analysis* (2009).
- Rump (INTLAB) for outward rounding.
-/

@[expose] public section


namespace FloatLib.Floats.Interval

/-- A closed real interval $[\mathtt{lo},\mathtt{hi}]$, empty when `hi < lo`. -/
structure RInterval where
  /-- Lower endpoint. -/
  lo : ℝ
  /-- Upper endpoint. -/
  hi : ℝ

namespace RInterval

/-- Membership predicate: $x\in I$ means
$I.\mathtt{lo}\le x\le I.\mathtt{hi}$. -/
def mem (I : RInterval) (x : ℝ) : Prop :=
  I.lo ≤ x ∧ x ≤ I.hi

/-- Enable $x\in I$ notation for real intervals. -/
instance : Membership ℝ RInterval where
  mem I x := I.mem x

/-- Unfold membership:
$x\in I\iff I.\mathtt{lo}\le x\land x\le I.\mathtt{hi}$. -/
@[simp, grind =] theorem mem_iff (I : RInterval) (x : ℝ) : x ∈ I ↔ I.lo ≤ x ∧ x ≤ I.hi :=
  Iff.rfl

/-- Degenerate interval $[x,x]$. -/
@[inline] def point (x : ℝ) : RInterval := ⟨x, x⟩

/-- Membership in a point interval is equality. -/
theorem mem_point (x y : ℝ) : x ∈ point y ↔ x = y :=
  ⟨fun h => le_antisymm h.2 h.1, fun h => h ▸ ⟨le_rfl, le_rfl⟩⟩

/-- Interval negation:
$-[\mathtt{lo},\mathtt{hi}]=[-\mathtt{hi},-\mathtt{lo}]$. -/
@[inline] def neg (I : RInterval) : RInterval := ⟨-I.hi, -I.lo⟩

/-- Outward-rounded interval addition, using the provided endpoint `Rounder`. -/
@[inline] def add (R : Rounder) (A B : RInterval) : RInterval :=
  ⟨R.down (A.lo + B.lo), R.up (A.hi + B.hi)⟩

/-- Outward-rounded interval subtraction, implemented as $A+(-B)$. -/
@[inline] def sub (R : Rounder) (A B : RInterval) : RInterval :=
  add R A (neg B)

/--
Maximum absolute endpoint magnitude:
$\max(|\mathtt{lo}|,|\mathtt{hi}|)$.

For a member of the interval, this bounds its absolute value. It is useful for even functions such
as `Real.cosh`, whose maximum over an interval occurs at an endpoint of largest magnitude.
-/
noncomputable def absMax (I : RInterval) : ℝ :=
  max |I.lo| |I.hi|

/-- If $x\in I$, then $|x|\le\operatorname{absMax}(I)$. -/
theorem abs_le_absMax {I : RInterval} {x : ℝ} (hx : x ∈ I) :
    |x| ≤ absMax I := by
  -- `abs` is convex on ℝ; max on an interval occurs at endpoints.
  exact abs_le_max_abs_abs hx.1 hx.2

/-- Outward-rounded multiplication using the four products of the endpoint pairs. -/
noncomputable def mul (R : Rounder) (A B : RInterval) : RInterval :=
  let lower := minOfFour
    (A.lo * B.lo) (A.lo * B.hi) (A.hi * B.lo) (A.hi * B.hi)
  let upper := maxOfFour
    (A.lo * B.lo) (A.lo * B.hi) (A.hi * B.lo) (A.hi * B.hi)
  ⟨R.down lower, R.up upper⟩

/-- Soundness of `add`: membership is preserved by real addition. -/
theorem mem_add {R : Rounder} {A B : RInterval} {x y : ℝ}
    (hx : x ∈ A) (hy : y ∈ B) :
    x + y ∈ add R A B :=
  ⟨(R.down_le _).trans (add_le_add hx.1 hy.1), (add_le_add hx.2 hy.2).trans (R.le_up _)⟩

/-- Soundness of `sub`: membership is preserved by real subtraction. -/
theorem mem_sub {R : Rounder} {A B : RInterval} {x y : ℝ}
    (hx : x ∈ A) (hy : y ∈ B) :
    x - y ∈ sub R A B := by
  have hy' : -y ∈ neg B := ⟨neg_le_neg hy.2, neg_le_neg hy.1⟩
  simpa [sub, sub_eq_add_neg] using mem_add (R := R) hx hy'

/-- Soundness of `mul`: every product of members lies between the rounded corner bounds. -/
theorem mem_mul {R : Rounder} {A B : RInterval} {x y : ℝ}
    (hx : x ∈ A) (hy : y ∈ B) :
    x * y ∈ mul R A B := by
  have hbounds := mul_bounds_Icc A.lo A.hi B.lo B.hi x y
    (show x ∈ Set.Icc A.lo A.hi from hx)
    (show y ∈ Set.Icc B.lo B.hi from hy)
  constructor
  · exact le_trans (R.down_le _) hbounds.1
  · exact le_trans hbounds.2 (R.le_up _)

/-- Outward-rounded interval enclosure for `Real.exp`, using monotonicity. -/
noncomputable def exp (R : Rounder) (A : RInterval) : RInterval :=
  ⟨R.down (Real.exp A.lo), R.up (Real.exp A.hi)⟩

/-- Soundness of `exp`: membership is preserved by `Real.exp`. -/
theorem mem_exp {R : Rounder} {A : RInterval} {x : ℝ} (hx : x ∈ A) :
    Real.exp x ∈ exp R A :=
  ⟨(R.down_le _).trans (Real.exp_monotone hx.1), (Real.exp_monotone hx.2).trans (R.le_up _)⟩

private theorem tanh_monotone {x y : ℝ} (hxy : x ≤ y) :
    Real.tanh x ≤ Real.tanh y := by
  have hx : Real.tanh x ∈ Set.Ioo (-1) 1 :=
    ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
  have hy : Real.tanh y ∈ Set.Ioo (-1) 1 :=
    ⟨Real.neg_one_lt_tanh y, Real.tanh_lt_one y⟩
  apply (Real.artanh_le_artanh_iff hx hy).mp
  simpa only [Real.artanh_tanh] using hxy

/-- Outward-rounded interval enclosure for the monotone function `Real.tanh`. -/
noncomputable def tanh (R : Rounder) (A : RInterval) : RInterval :=
  ⟨R.down (Real.tanh A.lo), R.up (Real.tanh A.hi)⟩

/-- Soundness of `tanh`: membership is preserved by `Real.tanh`. -/
theorem mem_tanh {R : Rounder} {A : RInterval} {x : ℝ} (hx : x ∈ A) :
    Real.tanh x ∈ tanh R A :=
  ⟨(R.down_le _).trans (tanh_monotone hx.1), (tanh_monotone hx.2).trans (R.le_up _)⟩

/-- Outward-rounded interval enclosure for `Real.sqrt`; informative when $0\le\mathtt{lo}$. -/
noncomputable def sqrt (R : Rounder) (A : RInterval) : RInterval :=
  ⟨R.down (Real.sqrt A.lo), R.up (Real.sqrt A.hi)⟩

/--
Soundness of `sqrt`: membership is preserved by `Real.sqrt`.

`Real.sqrt` is monotone on all of `ℝ` (it sends every nonpositive input to `0`), so no sign
hypothesis on `A` is needed; the nonnegativity remark on `sqrt` only describes when the enclosure
is informative.
-/
theorem mem_sqrt {R : Rounder} {A : RInterval} {x : ℝ} (hx : x ∈ A) :
    Real.sqrt x ∈ sqrt R A :=
  ⟨(R.down_le _).trans (Real.sqrt_le_sqrt hx.1), (Real.sqrt_le_sqrt hx.2).trans (R.le_up _)⟩

/-- Outward-rounded interval enclosure for `Real.log` (requires
$0<\mathtt{lo}$). -/
noncomputable def log (R : Rounder) (A : RInterval) : RInterval :=
  ⟨R.down (Real.log A.lo), R.up (Real.log A.hi)⟩

/-- Soundness of `log`: membership is preserved by `Real.log` on positive intervals. -/
theorem mem_log {R : Rounder} {A : RInterval} {x : ℝ} (hA : 0 < A.lo) (hx : x ∈ A) :
    Real.log x ∈ log R A :=
  ⟨(R.down_le _).trans (Real.log_le_log hA hx.1),
    (Real.log_le_log (hA.trans_le hx.1) hx.2).trans (R.le_up _)⟩

end RInterval

/-!
## Extended-real intervals (for division by an interval containing 0)
-/

/--
An `EReal` interval `[lo,hi]`.

We use this for operations like division where a single interval may need to represent unbounded
results (`-∞`/`+∞`) in a sound-but-coarse way.
-/
structure EInterval where
  /-- Lower endpoint. -/
  lo : EReal
  /-- Upper endpoint. -/
  hi : EReal

noncomputable section

namespace EInterval

/-- Membership predicate: `x ∈ I` means `I.lo ≤ x ≤ I.hi` in `EReal`. -/
def mem (I : EInterval) (x : EReal) : Prop :=
  I.lo ≤ x ∧ x ≤ I.hi

/-- Enable `x ∈ I` notation for `EReal` intervals. -/
instance : Membership EReal EInterval where
  mem I x := I.mem x

/-- Unfold membership: `x ∈ I ↔ I.lo ≤ x ∧ x ≤ I.hi`. -/
@[simp, grind =] theorem mem_iff (I : EInterval) (x : EReal) : x ∈ I ↔ I.lo ≤ x ∧ x ≤ I.hi :=
  Iff.rfl

/-- Top interval `[-∞,+∞]` (the most conservative enclosure). -/
noncomputable def top : EInterval := ⟨⊥, ⊤⟩

/-- Every value lies in `top = [-∞,+∞]`. -/
theorem mem_top (x : EReal) : x ∈ top := by
  simp [top]

/-- Embed a real interval into an extended-real interval. -/
@[inline] def ofRInterval (I : RInterval) : EInterval := ⟨(I.lo : EReal), (I.hi : EReal)⟩

/--
Embedding an interval into `EReal` preserves membership of real values.
-/
theorem mem_ofRInterval (I : RInterval) (x : ℝ) :
    ((x : ℝ) : EReal) ∈ ofRInterval I ↔ x ∈ I := by
  simp [ofRInterval]

end EInterval

namespace RInterval

open EInterval

/-!
Division with possibly unbounded results.

If the denominator interval contains `0`, the enclosure is `[-∞,+∞]`.
Otherwise the quotient is enclosed by the four endpoint quotients.
-/
/--
Outward-rounded interval division as an `EReal` enclosure.

If the denominator interval contains `0`, we return `EInterval.top = [-∞,+∞]`. Otherwise we
outward-round the minimum and maximum of the four endpoint quotients.
-/
noncomputable def div (R : Rounder) (A B : RInterval) : EInterval :=
  if _h0 : (B.lo ≤ 0 ∧ 0 ≤ B.hi) then
    EInterval.top
  else
    let lower := minOfFour
      (A.lo / B.lo) (A.lo / B.hi) (A.hi / B.lo) (A.hi / B.hi)
    let upper := maxOfFour
      (A.lo / B.lo) (A.lo / B.hi) (A.hi / B.lo) (A.hi / B.hi)
    EInterval.ofRInterval ⟨R.down lower, R.up upper⟩

/--
Soundness of `div` in the nonzero-denominator case (`0 ∉ B`).

Under the hypothesis `¬ (B.lo ≤ 0 ∧ 0 ≤ B.hi)`, the constructed `EInterval` contains the true real
quotient `x/y` (as an `EReal`).
-/
theorem mem_div_of_nozero {R : Rounder} {A B : RInterval} {x y : ℝ}
    (hx : x ∈ A) (hy : y ∈ B) (h0 : ¬ (B.lo ≤ 0 ∧ 0 ≤ B.hi)) :
    ((x / y : ℝ) : EReal) ∈ (div R A B) := by
  have hside : B.hi < 0 ∨ 0 < B.lo := by
    by_contra h
    exact h0 ⟨not_lt.mp (not_or.mp h).2, not_lt.mp (not_or.mp h).1⟩
  have hbounds := div_bounds_Icc A.lo A.hi B.lo B.hi x y
    (show x ∈ Set.Icc A.lo A.hi from hx)
    (show y ∈ Set.Icc B.lo B.hi from hy)
    hside
  rw [div, dif_neg h0]
  apply (EInterval.mem_ofRInterval _ _).2
  exact And.intro
    (le_trans (R.down_le _) hbounds.1)
    (le_trans hbounds.2 (R.le_up _))

/--
Soundness of `div` without any hypothesis on the denominator interval.

When `B` contains zero the result is `EInterval.top`, which contains everything; otherwise this is
`mem_div_of_nozero`. Division by zero itself is Lean's totalized `x / 0 = 0`, which the top
interval also contains.
-/
theorem mem_div {R : Rounder} {A B : RInterval} {x y : ℝ}
    (hx : x ∈ A) (hy : y ∈ B) :
    ((x / y : ℝ) : EReal) ∈ (div R A B) := by
  by_cases h0 : B.lo ≤ 0 ∧ 0 ≤ B.hi
  · rw [div, dif_pos h0]
    exact EInterval.mem_top _
  · exact mem_div_of_nozero hx hy h0

end RInterval

end

end Interval
