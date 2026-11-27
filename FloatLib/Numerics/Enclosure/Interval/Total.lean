/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.InverseTrig
public import FloatLib.Numerics.Enclosure.Interval.Rounding

/-!
# Enclosures of Mathlib's total square root, arcsine, arccosine and logarithm

Mathlib defines `Real.sqrt`, `Real.arcsin`, `Real.arccos` and `Real.log` at every real number.
The square root is zero below zero, arcsine and arccosine are constant outside `[-1, 1]`, and
`Real.log x = Real.log |x|` with `Real.log 0 = 0`. The enclosures `sqrtBounds?`, `asinBounds?`,
`acosBounds?` and `logBounds?` return `none` on those arguments. The ones here follow the total
functions there: on `[-1, 1]`, say, `Total.sqrt` gives `[0, 1]`, where `sqrtBounds?` gives
`none`. Only the logarithm still refuses an interval, one that contains zero and another point,
where it's unbounded below.

## Main definitions

* `Total.sqrtPoint q steps`: `[0, 0]` below zero, and otherwise the integer square-root bounds of
  `q * q.den ^ 2 = q.num * q.den` divided by `q.den`. So a rational square gives its exact root,
  and every result is at most `1 / (q.den * 2 ^ steps)` wide. At 12 bits, `√2` gets
  `[181/128, 5793/4096]`.
* `Total.asinPoint` and `Total.acosPoint`: the argument clamped to `[-1, 1]`, enclosed by
  `asinBounds?` or `acosBounds?` with a square-root precision that grows with the denominator.
  The result is rounded outward with `dyadicHull` to a binary grid 32 bits finer than that
  precision, and of at least 128 bits, which keeps the endpoints short.
* `Total.sqrt`, `Total.asin` and `Total.acos`: the point enclosures at the two ends of an
  interval (`monotoneBounds`, and `antitoneBounds` for the arccosine).
* `Total.log? I terms`: `logBounds? I terms` on a positive interval, `logBounds?` of the negation
  on a negative one, and `[0, 0]` on `[0, 0]`.

## Implementation notes

The comparisons and the rational arithmetic are written with the kernel functions of
`FloatLib.Numerics.Kernel`, because Lean's kernel evaluates these bounds. `sqrtPoint_def`,
`clampUnit_def`, `inverseTrigPrecision_def` and `log?_def` state them in ordinary notation, and
`TotalProof` proves that each enclosure contains the function at every real member of its input.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval.Total

/-! ### Square root -/

/--
Enclose Mathlib's total `Real.sqrt q`: `[0, 0]` for negative `q`, and otherwise the bounds
`sqrtPointBounds` of `q * q.den ^ 2` at `steps` fractional bits, divided by `q.den`
(`sqrtPoint_def`).

The scaled argument is the integer `q.num * q.den`, and a square `(a / b) ^ 2` in lowest terms
scales to `(a * b) ^ 2`, so a rational square gives its exact root (`sqrtPoint_sq`). The width is
at most `1 / (q.den * 2 ^ steps)` (`sqrtPoint_width_le`).
-/
def sqrtPoint (q : ℚ) (steps : Nat) : Interval ℚ :=
  Bool.casesOn (motive := fun _ => Interval ℚ) (Kernel.Q.le 0 q) (point 0)
    ((fun bounds : Interval ℚ =>
      (⟨Kernel.Q.div bounds.lo q.den, Kernel.Q.div bounds.hi q.den⟩ : Interval ℚ))
        (sqrtPointBounds (Kernel.Q.mul q (Kernel.Q.pow q.den 2)) steps))

/-- The total square-root bounds, in ordinary notation. -/
theorem sqrtPoint_def (q : ℚ) (steps : Nat) :
    sqrtPoint q steps =
      if 0 ≤ q then
        let bounds := sqrtPointBounds (q * (q.den : ℚ) ^ 2) steps
        ⟨bounds.lo / q.den, bounds.hi / q.den⟩
      else point 0 := by
  unfold sqrtPoint
  simp only [Kernel.Q.casesOn_le, Kernel.Q.div_eq, Kernel.Q.mul_eq, Kernel.Q.pow_eq]

/--
Enclose `Real.sqrt` on `I` by the lower bound at `I.lo` and the upper bound at `I.hi`
(`monotoneBounds`), which is valid because the square root is monotone.
-/
def sqrt (I : Interval ℚ) (steps : Nat) : Interval ℚ :=
  monotoneBounds (fun q => sqrtPoint q steps) I

/-! ### Arcsine and arccosine -/

/-- `q` clamped to `[-1, 1]` (`clampUnit_def`). Arcsine and arccosine take the same values at
`clampUnit q` and at `q` (`arcsin_clampUnit`, `arccos_clampUnit`). -/
def clampUnit (q : ℚ) : ℚ :=
  Kernel.Q.max (-1) (Kernel.Q.min 1 q)

/-- The clamp, in ordinary notation. -/
theorem clampUnit_def (q : ℚ) : clampUnit q = max (-1) (min 1 q) := by
  rw [clampUnit, Kernel.Q.max_eq, Kernel.Q.min_eq]

/--
The square-root precision of `asinPoint q` and `acosPoint q`: `32 + 2 * log2 q.den` fractional
bits (`inverseTrigPrecision_def`). A larger denominator lets `q` lie closer to `±1`, where
`√(1 - q ^ 2)` is small.
-/
def inverseTrigPrecision (q : ℚ) : Nat :=
  32 + 2 * Kernel.log2 q.den

/-- The precision schedule, with core's `Nat.log2`. -/
theorem inverseTrigPrecision_def (q : ℚ) : inverseTrigPrecision q = 32 + 2 * q.den.log2 := by
  rw [inverseTrigPrecision, Kernel.log2_eq]

/--
The grid of `asinPoint q` and `acosPoint q`, in fractional bits: `inverseTrigPrecision q + 32`,
and at least `128`.
-/
def inverseTrigRoundingPrecision (q : ℚ) : Nat :=
  max 128 (inverseTrigPrecision q + 32)

/--
Enclose `f q` from interval bounds `bounds` for `f`, evaluated at the point `clampUnit q` with
the degree `terms` and the precision `inverseTrigPrecision q`.

A result is rounded outward by `dyadicHull` to the grid of `inverseTrigRoundingPrecision q`
fractional bits. `fallback` is returned when `bounds` fails. `containsReal_inverseTrigPoint`
gives the conditions on `f`, `bounds` and `fallback`.
-/
def inverseTrigPoint (bounds : Interval ℚ → Nat → Nat → Option (Interval ℚ))
    (fallback : Interval ℚ) (q : ℚ) (terms : Nat) : Interval ℚ :=
  match bounds (point (clampUnit q)) terms (inverseTrigPrecision q) with
  | some J => dyadicHull (inverseTrigRoundingPrecision q) J
  | none => fallback

/--
Enclose Mathlib's total `Real.arcsin q` by `asinBounds?` at `clampUnit q`, with `terms` series
terms (`inverseTrigPoint`). If `asinBounds?` fails, the result is `[-π / 2, π / 2]`, with the
upper bound `3.14159265358979323847` of `π`.
-/
def asinPoint (q : ℚ) (terms : Nat) : Interval ℚ :=
  inverseTrigPoint asinBounds?
    ⟨-3.14159265358979323847 / 2, 3.14159265358979323847 / 2⟩ q terms

/--
Enclose Mathlib's total `Real.arccos q` by `acosBounds?` at `clampUnit q`, with `terms` series
terms (`inverseTrigPoint`). If `acosBounds?` fails, the result is `[0, π]`, with the upper bound
`3.14159265358979323847` of `π`.
-/
def acosPoint (q : ℚ) (terms : Nat) : Interval ℚ :=
  inverseTrigPoint acosBounds? ⟨0, 3.14159265358979323847⟩ q terms

/--
Enclose `Real.arcsin` on `I` by the lower bound at `I.lo` and the upper bound at `I.hi`
(`monotoneBounds`), which is valid because the arcsine is monotone.
-/
def asin (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  monotoneBounds (fun q => asinPoint q terms) I

/--
Enclose `Real.arccos` on `I` by the lower bound at `I.hi` and the upper bound at `I.lo`
(`antitoneBounds`), which is valid because the arccosine is antitone.
-/
def acos (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  antitoneBounds (fun q => acosPoint q terms) I

/-! ### Logarithm -/

/--
Enclose Mathlib's total `Real.log` on `I` (`log?_def`). A positive interval gets
`logBounds? I terms`. A negative one gets `logBounds?` of its negation, since
`Real.log (-x) = Real.log x`, and `[0, 0]` gets `[0, 0]`, since `Real.log 0 = 0`. Every other
ordered interval contains zero and points as close to it as we like, so it gives `none`.
-/
def log? (I : Interval ℚ) (terms : Nat) : Option (Interval ℚ) :=
  Bool.casesOn (motive := fun _ => Option (Interval ℚ)) (Kernel.Q.lt 0 I.lo)
    (Bool.casesOn (motive := fun _ => Option (Interval ℚ)) (Kernel.Q.lt I.hi 0)
      (Bool.casesOn (motive := fun _ => Option (Interval ℚ))
        (Bool.and (Kernel.Q.beq I.lo 0) (Kernel.Q.beq I.hi 0)) none (some (point 0)))
      (logBounds? ⟨Kernel.Q.neg I.hi, Kernel.Q.neg I.lo⟩ terms))
    (logBounds? I terms)

/-- The total logarithm bounds, in ordinary notation. -/
theorem log?_def (I : Interval ℚ) (terms : Nat) :
    log? I terms =
      if 0 < I.lo then logBounds? I terms
      else if I.hi < 0 then logBounds? ⟨-I.hi, -I.lo⟩ terms
      else if I.lo = 0 ∧ I.hi = 0 then some (point 0)
      else none := by
  have hzero : Bool.and (Kernel.Q.beq I.lo 0) (Kernel.Q.beq I.hi 0) = true ↔
      I.lo = 0 ∧ I.hi = 0 := by
    rw [Bool.and_eq_true, Kernel.Q.beq_iff, Kernel.Q.beq_iff]
  unfold log?
  rw [Kernel.Q.casesOn_lt, Kernel.Q.casesOn_lt, Kernel.Z.casesOn_eq_ite hzero, Kernel.Q.neg_eq,
    Kernel.Q.neg_eq]

end FloatLib.Numerics.Interval.Total
