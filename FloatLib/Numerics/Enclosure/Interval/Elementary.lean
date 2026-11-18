/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Runtime
public import FloatLib.Numerics.Enclosure.Interval.Basic
public import FloatLib.Numerics.Enclosure.Trigonometric.Reduction.Runtime
public import FloatLib.Numerics.Kernel.RootProof

/-!
# Elementary functions on rational intervals

A monotone function needs only enclosures of its lower and upper endpoints. Sine and cosine aren't
monotone, so they enclose the midpoint and add the half-width, using their global Lipschitz constant
one. Intersecting with `[-1, 1]` keeps the bounds useful even when the requested Taylor degree is
small.

The analytic point enclosures come from `Numerics.Enclosure`, and square root uses an integer square
root after exact dyadic scaling. `ElementaryProof` proves containment of every real member of the
input interval, irrational members included.

The comparisons, the maxima and minima and the square root are written with the kernel functions
of `FloatLib.Numerics.Kernel` (`Q.le`, `Q.max`, `isqrt`), because the `interval` tactic evaluates
these bounds in Lean's kernel. `expBounds_def`, `lipschitzUnitBounds_def`, `sinBounds_def`,
`cosBounds_def` and `sqrtPointBounds_def` state them in ordinary notation.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/--
Combine the lower enclosure at the left endpoint with the upper enclosure at the right.

Soundness requires a monotone real function and sound point enclosures. A point interval
evaluates the enclosure only once.
-/
def monotoneBounds (enclose : ℚ → Interval ℚ) (I : Interval ℚ) : Interval ℚ :=
  let lo := enclose I.lo
  if I.lo = I.hi then lo else ⟨lo.lo, (enclose I.hi).hi⟩

/-- Enclose the exponential on the whole interval, with the supplied Taylor degree. -/
def expBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  monotoneBounds (fun x =>
    let J := Enclosure.exp x terms
    ⟨Kernel.Q.max 0 J.lo, J.hi⟩) I

/-- The exponential bounds, in ordinary notation. -/
theorem expBounds_def (I : Interval ℚ) (terms : Nat) :
    expBounds I terms =
      monotoneBounds (fun x =>
        let J := Enclosure.exp x terms
        ⟨max 0 J.lo, J.hi⟩) I := by
  unfold expBounds
  simp only [Kernel.Q.max_eq]

/-- Enclose the logarithm when the entire input interval is strictly positive. -/
def logBounds? (I : Interval ℚ) (terms : Nat) : Option (Interval ℚ) :=
  if 0 < I.lo then
    some (monotoneBounds (fun x =>
      let J := Enclosure.log x terms
      ⟨J.lo, J.hi⟩) I)
  else none

/-- Enclose arctangent on the whole interval, using the reduced rational point kernel. -/
def atanBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  monotoneBounds (fun x =>
    let J := Enclosure.atan x terms
    ⟨J.lo, J.hi⟩) I

/--
Enclose a function with Lipschitz constant one and range in `[-1, 1]`.

The midpoint enclosure is widened by the half-width. Widths at least four already give the
whole unit range after this widening, so they skip the point kernel.
-/
def lipschitzUnitBounds (enclose : ℚ → Interval ℚ) (I : Interval ℚ) : Interval ℚ :=
  Bool.casesOn (motive := fun _ => Interval ℚ) (Kernel.Q.le 4 (Kernel.Q.sub I.hi I.lo))
    (let midpoint := Kernel.Q.divPow2 (Kernel.Q.add I.lo I.hi) 1
     let radius := Kernel.Q.divPow2 (Kernel.Q.sub I.hi I.lo) 1
     let J := enclose midpoint
     ⟨Kernel.Q.max (-1) (Kernel.Q.sub J.lo radius), Kernel.Q.min 1 (Kernel.Q.add J.hi radius)⟩)
    ⟨-1, 1⟩

/-- The Lipschitz bounds, in ordinary notation. -/
theorem lipschitzUnitBounds_def (enclose : ℚ → Interval ℚ) (I : Interval ℚ) :
    lipschitzUnitBounds enclose I =
      if 4 ≤ I.hi - I.lo then ⟨-1, 1⟩
      else
        let midpoint := (I.lo + I.hi) / 2
        let radius := (I.hi - I.lo) / 2
        let J := enclose midpoint
        ⟨max (-1) (J.lo - radius), min 1 (J.hi + radius)⟩ := by
  unfold lipschitzUnitBounds
  simp only [Kernel.Q.casesOn_le, Kernel.Q.divPow2_eq, Kernel.Q.max_eq, Kernel.Q.min_eq,
    Kernel.Q.sub_eq, Kernel.Q.add_eq, pow_one]

/--
Share the period certificate and turn count between the value and error bounds
(`Internal.reducedTrigBounds_def`).
-/
def Internal.reducedTrigBounds (taylor : ℚ → Nat → ℚ) (x : ℚ)
    (terms : Nat) : RationalInterval :=
  let pi := Enclosure.piQuarter terms
  let quarter := Kernel.Q.max (Kernel.Q.divPow2 1 1) (Kernel.Q.min 1 pi.lo)
  let turns : Int :=
    Kernel.Q.floor (Kernel.Q.add (Kernel.Q.div x (Kernel.Q.mul 8 quarter)) (Kernel.Q.divPow2 1 1))
  let arg := Kernel.Q.sub x (Kernel.Q.mul (Kernel.Q.mul 8 (turns : ℚ)) quarter)
  let radius := Kernel.Q.add (Enclosure.trigRadius arg terms)
    (Kernel.Q.mul (Kernel.Q.mul 8 (Kernel.Q.abs (turns : ℚ))) (Kernel.Q.sub pi.hi quarter))
  Enclosure.restrictUnit (RationalInterval.around (taylor arg terms) radius)

/-- The reduced trigonometric bounds, in ordinary notation. -/
theorem Internal.reducedTrigBounds_def (taylor : ℚ → Nat → ℚ) (x : ℚ) (terms : Nat) :
    Internal.reducedTrigBounds taylor x terms =
      (let pi := Enclosure.piQuarter terms
       let quarter := max (1 / 2) (min 1 pi.lo)
       let turns : Int := ⌊x / (8 * quarter) + 1 / 2⌋
       let arg := x - 8 * (turns : ℚ) * quarter
       let radius :=
         Enclosure.trigRadius arg terms + 8 * |(turns : ℚ)| * (pi.hi - quarter)
       Enclosure.restrictUnit (RationalInterval.around (taylor arg terms) radius)) := by
  unfold Internal.reducedTrigBounds
  simp only [Kernel.Q.max_eq, Kernel.Q.min_eq, Kernel.Q.floor_eq, Kernel.Q.add_eq,
    Kernel.Q.div_eq, Kernel.Q.divPow2_eq, Kernel.Q.sub_eq, Kernel.Q.mul_eq, Kernel.Q.abs_eq,
    pow_one]

/--
Enclose sine for every real in the interval, including intervals crossing an extremum.

Small midpoints use the Taylor kernel as it is. Larger ones use proved rational period reduction,
and the resulting period error is included in the point enclosure.
-/
def sinBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  lipschitzUnitBounds (fun x =>
    let J := Bool.casesOn (motive := fun _ => RationalInterval) (Kernel.Q.le (Kernel.Q.abs x) 4)
      (Internal.reducedTrigBounds Enclosure.sinTaylor x terms) (Enclosure.sin x terms)
    ⟨J.lo, J.hi⟩) I

/-- The sine bounds, in ordinary notation. -/
theorem sinBounds_def (I : Interval ℚ) (terms : Nat) :
    sinBounds I terms =
      lipschitzUnitBounds (fun x =>
        let J := if |x| ≤ 4 then Enclosure.sin x terms
          else Internal.reducedTrigBounds Enclosure.sinTaylor x terms
        ⟨J.lo, J.hi⟩) I := by
  unfold sinBounds
  simp only [Kernel.Q.casesOn_le, Kernel.Q.abs_eq]

/-- Enclose cosine by the midpoint Lipschitz bound, without assuming endpoint monotonicity. -/
def cosBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  lipschitzUnitBounds (fun x =>
    let J := Bool.casesOn (motive := fun _ => RationalInterval) (Kernel.Q.le (Kernel.Q.abs x) 4)
      (Internal.reducedTrigBounds Enclosure.cosTaylor x terms) (Enclosure.cos x terms)
    ⟨J.lo, J.hi⟩) I

/-- The cosine bounds, in ordinary notation. -/
theorem cosBounds_def (I : Interval ℚ) (terms : Nat) :
    cosBounds I terms =
      lipschitzUnitBounds (fun x =>
        let J := if |x| ≤ 4 then Enclosure.cos x terms
          else Internal.reducedTrigBounds Enclosure.cosTaylor x terms
        ⟨J.lo, J.hi⟩) I := by
  unfold cosBounds
  simp only [Kernel.Q.casesOn_le, Kernel.Q.abs_eq]

/--
Dyadic bounds for the square root of a nonnegative rational.

The lower endpoint is `floor (sqrt x * 2^precision) / 2^precision`, computed by an integer
square root. The upper endpoint is one grid step higher, unless the lower endpoint squares
to `x` exactly. The width is therefore at most `2^(-precision)`.
-/
def sqrtPointBounds (x : ℚ) (precision : Nat) : Interval ℚ :=
  (fun root : Nat =>
    (fun lo : ℚ =>
      (⟨lo, Bool.casesOn (motive := fun _ => ℚ) (Kernel.Q.beq (Kernel.Q.mul lo lo) x)
        (Kernel.Q.mk (Int.ofNat (Nat.succ root)) (Nat.shiftLeft 1 precision)) lo⟩ : Interval ℚ))
      (Kernel.Q.mk (Int.ofNat root) (Nat.shiftLeft 1 precision)))
    (Kernel.isqrt (Kernel.Z.toNat (Kernel.Q.floor (Kernel.Q.mulPow2 x (Nat.mul 2 precision)))))

/-- The square-root bounds, in ordinary notation. -/
theorem sqrtPointBounds_def (x : ℚ) (precision : Nat) :
    sqrtPointBounds x precision =
      (let scale := (2 : ℚ) ^ precision
       let root := Nat.sqrt ⌊x * scale ^ 2⌋₊
       let lo := (root : ℚ) / scale
       ⟨lo, if lo ^ 2 = x then lo else (root + 1 : ℚ) / scale⟩) := by
  have hroot : Kernel.isqrt (Kernel.Z.toNat
      (Kernel.Q.floor (Kernel.Q.mulPow2 x (Nat.mul 2 precision)))) =
        Nat.sqrt ⌊x * ((2 : ℚ) ^ precision) ^ 2⌋₊ := by
    rw [Kernel.isqrt_eq, Kernel.Z.toNat_eq, Kernel.Q.floor_eq, Kernel.Q.mulPow2_eq,
      Int.floor_toNat, ← pow_mul, Nat.mul_comm precision 2]
    rfl
  have hmk : ∀ n : Nat, Kernel.Q.mk (Int.ofNat n) (Nat.shiftLeft 1 precision) =
      (n : ℚ) / (2 : ℚ) ^ precision := by
    intro n
    rw [Kernel.Q.mk_eq, Rat.mkRat_eq_div]
    change ((n : Int) : ℚ) / ((1 <<< precision : Nat) : ℚ) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    push_cast
    rfl
  unfold sqrtPointBounds
  simp only [hroot, hmk, Kernel.Z.casesOn_eq_ite (Kernel.Q.beq_iff _ _), Kernel.Q.mul_eq,
    ← pow_two, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]

/--
Enclose square root on a nonnegative interval with a dyadic grid of step `2^(-precision)`.

A negative lower endpoint returns `none`, including intervals that cross zero from below.
Zero and exact dyadic squares are accepted without an artificial positive lower bound.
-/
def sqrtBounds? (I : Interval ℚ) (precision : Nat) : Option (Interval ℚ) :=
  if 0 ≤ I.lo then some (monotoneBounds (fun x => sqrtPointBounds x precision) I)
  else none

end FloatLib.Numerics.Interval
