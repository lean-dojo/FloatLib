/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Runtime
public import FloatLib.Numerics.Enclosure.Interval.BinaryGrid

/-!
# Elementary enclosures evaluated on a binary grid

Taylor polynomials and remainder bounds use integer interval arithmetic at `precision` fractional
bits. Each multiplication and scalar division rounds outward on that grid. Exact rational
arithmetic is used for argument reduction and scalar factors; only the final endpoints are decoded.

The degree selects the same Taylor polynomial as the rational kernels in `Elementary.Runtime`.
Containment holds at every precision, including zero. Coarse grids can give wide bounds.

Long logarithm polynomials share a table of powers through rectangular splitting; see Section 4
of Fredrik Johansson, [*Efficient implementation of elementary functions in the medium-precision
range*](https://arxiv.org/abs/1410.7176).
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.BinaryGrid

open Interval.BinaryGrid

/-- Add guard bits and a degree-dependent rounding allowance to a target grid width. -/
def workingPrecision (targetBits degree : Nat) : Nat :=
  targetBits + degree.log2 + 16

/--
Choose a grid width relative to a nonzero result scale.

The integer logarithms estimate the extra fractional bits needed for a small result. Consumers
handle exact zero separately; increasing the degree also increases the rounding allowance.
-/
def relativePrecision (targetBits : Nat) (scale : ℚ) (degree : Nat) : Nat :=
  workingPrecision (targetBits + (scale.den.log2 - scale.num.natAbs.log2)) degree

/--
Allow for repeated squaring and small exponential results when choosing a grid width.

Subtracting one also needs enough fractional bits to retain a small input's contribution.
These estimates guide refinement; endpoint containment holds independently of them.
-/
def expPrecision (targetBits : Nat) (x : ℚ) (degree : Nat) (subtractOne : Bool := false) :
    Nat :=
  let cancellation := if subtractOne then x.den.log2 - x.num.natAbs.log2 else 0
  workingPrecision
    (targetBits + Enclosure.expScale x + 2 * (-x).ceil.toNat + cancellation) degree

/-- Allow for cancellation near one and scaling by a large binary logarithm. -/
def logPrecision (targetBits : Nat) (x : ℚ) (degree : Nat) : Nat :=
  relativePrecision (targetBits + (Enclosure.logScale (max x x⁻¹)).log2) (x - 1) degree

/-- Decode the two final coefficients as rational endpoints. -/
def toRationalInterval (precision : Nat) (I : Interval Int) : RationalInterval :=
  ⟨toRat precision I.lo, toRat precision I.hi⟩

/--
Scale an interval by an exact rational, rounding the integer coefficients outward.

The rational denominator is positive, so scalar division remains defined on every grid.
-/
def scaleRat (I : Interval Int) (factor : ℚ) : Interval Int :=
  let a := divBounds (I.lo * factor.num) factor.den
  let b := divBounds (I.hi * factor.num) factor.den
  if 0 ≤ factor then ⟨a.lo, b.hi⟩ else ⟨b.lo, a.hi⟩

/-- Divide the coefficients by a natural scalar with outward rounding. -/
def divideNat (I : Interval Int) (n : Nat) : Interval Int :=
  scaleRat I (1 / (n : ℚ))

namespace Internal

/-- Integer floor and ceiling division; a zero divisor gives the zero interval. -/
@[inline] def divideNat (I : Interval Int) (n : Nat) : Interval Int :=
  ⟨I.lo / (n : Int), -((-I.hi) / (n : Int))⟩

private theorem divBounds_hi_neg_fdiv (a b : Int) (hb : b ≠ 0) :
    (divBounds a b).hi = -((-a).fdiv b) := by
  by_cases h : b ∣ a
  · simp [divBounds, Int.neg_fdiv, hb, h, Int.fdiv_mul_cancel h]
  · have hne : a.fdiv b * b ≠ a := by
      intro heq
      exact h ⟨a.fdiv b, by simpa [Int.mul_comm] using heq.symm⟩
    simp [divBounds, Int.neg_fdiv, hb, h, hne, add_comm]

/-- A point factor needs only two corner products, including for reversed input endpoints. -/
@[inline] def mul (precision : Nat) (I J : Interval Int) : Interval Int :=
  if I.lo = I.hi then
    let a := I.lo * J.lo
    let b := I.lo * J.hi
    ⟨roundDown precision (min a b), roundUp precision (max a b)⟩
  else if J.lo = J.hi then
    let a := I.lo * J.lo
    let b := I.hi * J.lo
    ⟨roundDown precision (min a b), roundUp precision (max a b)⟩
  else
    let a := I.lo * J.lo
    let b := I.lo * J.hi
    let c := I.hi * J.lo
    let d := I.hi * J.hi
    ⟨roundDown precision (Interval.minOfFour a b c d),
      roundUp precision (Interval.maxOfFour a b c d)⟩

end Internal

/-- Compile natural scalar division directly on integers, preserving both endpoints. -/
@[csimp] theorem divideNat_eq_direct : divideNat = Internal.divideNat := by
  funext I n
  by_cases hn : n = 0
  · simp [divideNat, scaleRat, Internal.divideNat, hn, divBounds]
  have hnz : (n : Int) ≠ 0 := Int.natCast_ne_zero.mpr hn
  have hnonneg : (0 : ℚ) ≤ (n : ℚ)⁻¹ := by positivity
  simp only [divideNat, scaleRat, one_div, ite_eq_left hnonneg, Rat.num_inv, Rat.den_inv,
    Rat.num_natCast, Rat.den_natCast, Int.sign_natCast_of_ne_zero hn, Nat.cast_one,
    mul_one, hnz, ite_false, Int.natAbs_natCast]
  change (⟨I.lo.fdiv n, (divBounds I.hi n).hi⟩ : Interval Int) = _
  rw [Internal.divBounds_hi_neg_fdiv I.hi n hnz]
  simp [Internal.divideNat, Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg n)]

/-- Compile point-factor multiplication with two products, preserving both interval endpoints. -/
@[csimp] theorem mul_eq_point : Interval.BinaryGrid.mul = Internal.mul := by
  funext precision I J
  dsimp only [Internal.mul]
  split_ifs <;> simp_all [Interval.BinaryGrid.mul, Interval.minOfFour, Interval.maxOfFour]

/-- Expand a midpoint interval using the upper endpoint of a radius enclosure. -/
def around (midpoint radius : Interval Int) : Interval Int :=
  ⟨midpoint.lo - radius.hi, midpoint.hi + radius.hi⟩

/-- Exponential Horner steps, with every product and division rounded on the chosen grid. -/
def expHorner (precision : Nat) (X : Interval Int) (start : Nat) : Nat → Interval Int
  | 0 => Interval.point 0
  | n + 1 =>
    add (Interval.point (scale precision))
      (divideNat (mul precision X (expHorner precision X (start + 1) n)) (start + 1))

/-- Odd logarithm terms evaluated by Horner steps in the square of the argument. -/
def logOddHorner (precision : Nat) (X Q : Interval Int) (start : Nat) : Nat → Interval Int
  | 0 => Interval.point 0
  | n + 1 =>
    add (divideNat X (2 * start + 1))
      (mul precision Q (logOddHorner precision X Q (start + 1) n))

namespace Internal

/-- Apply Horner steps from the highest index down, keeping the partial result in an accumulator. -/
@[specialize] def reverseHorner
    (step : Nat → Interval Int → Interval Int) (start : Nat) :
    Nat → Interval Int → Interval Int
  | 0, tail => tail
  | n + 1, tail => reverseHorner step start n (step (start + n) tail)

/-- Peeling off the outer step recovers the recursive Horner evaluation order. -/
private theorem reverseHorner_succ (step : Nat → Interval Int → Interval Int) (start n : Nat)
    (tail : Interval Int) :
    reverseHorner step start (n + 1) tail =
      step start (reverseHorner step (start + 1) n tail) := by
  induction n generalizing start tail with
  | zero => simp [reverseHorner]
  | succ n ih =>
    simpa only [reverseHorner, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih start (step (start + (n + 1)) tail)

end Internal

/-- Exponential Horner evaluation with an accumulator and one shared grid coefficient for one. -/
def expHornerIter (precision : Nat) (X : Interval Int) (start n : Nat) : Interval Int :=
  let one := Interval.point (scale precision)
  Internal.reverseHorner (fun k tail => add one (divideNat (mul precision X tail) (k + 1)))
    start n (Interval.point 0)

/-- Odd logarithm Horner evaluation with an accumulator. -/
def logOddHornerIter (precision : Nat) (X Q : Interval Int) (start n : Nat) : Interval Int :=
  Internal.reverseHorner (fun k tail => add (divideNat X (2 * k + 1)) (mul precision Q tail))
    start n (Interval.point 0)

/-- Compile exponential Horner evaluation as a loop, preserving both interval endpoints. -/
@[csimp] theorem expHorner_eq_iter : expHorner = expHornerIter := by
  funext precision X start n
  dsimp only [expHornerIter]
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [expHorner, Internal.reverseHorner_succ, ih]

/-- Compile odd logarithm Horner evaluation as a loop, preserving both interval endpoints. -/
@[csimp] theorem logOddHorner_eq_iter : logOddHorner = logOddHornerIter := by
  funext precision X Q start n
  dsimp only [logOddHornerIter]
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [logOddHorner, Internal.reverseHorner_succ, ih]

/-- Evaluate the exponential remainder bound without forming an exact rational power. -/
def expRadius (precision : Nat) (X : Interval Int) (n : Nat) : Interval Int :=
  scaleRat (pow precision (abs X) n)
    (((n + 1 : Nat) : ℚ) / ((n.factorial : ℚ) * n))

/-- Enclose the small exponential with the original Taylor polynomial and remainder bound. -/
def expSmall (x : ℚ) (degree precision : Nat) : Interval Int :=
  let X := enclose precision x
  around (expHorner precision X 0 (degree + 1)) (expRadius precision X (degree + 1))

/-- Restore exponential range reduction, rounding outward after each square. -/
def squareRepeat (precision : Nat) (I : Interval Int) : Nat → Interval Int
  | 0 => I
  | n + 1 => square precision (squareRepeat precision I n)

/--
Balance Taylor work against extra squarings using the degree and requested grid width.

The square-root estimate limits squaring work while the degree is small; the quotient reduces it
as refinement raises the degree. A small input already supplies some reduction without squaring.
These estimates guide refinement; containment does not depend on their accuracy.
-/
def expExtraScale (x : ℚ) (degree precision : Nat) : Nat :=
  min (Nat.sqrt (4 * precision)) (precision / (degree + 1)) -
    (x.den.log2 - x.num.natAbs.log2)

/-- Enclose the exponential, adding grid bits to compensate for the extra range-restoring squares. -/
def exp (x : ℚ) (degree precision : Nat) : RationalInterval :=
  let extra := expExtraScale x degree precision
  let reduction := Enclosure.expScale x + extra
  let working := precision + extra
  toRationalInterval working
    (squareRepeat working (expSmall (x / 2 ^ reduction) degree working) reduction)

namespace LogPolynomial

/-- Extend a table with successive rounded powers, including its final power. -/
def powerTableAux (precision : Nat) (Q : Interval Int) :
    Nat → Interval Int → Array (Interval Int) → Array (Interval Int)
  | 0, current, powers => powers.push current
  | n + 1, current, powers =>
    powerTableAux precision Q n (mul precision current Q) (powers.push current)

/-- Store the powers from zero through `n`, using one rounded multiplication per new power. -/
def powerTable (precision : Nat) (Q : Interval Int) (n : Nat) : Array (Interval Int) :=
  powerTableAux precision Q n (Interval.point (scale precision)) #[]

/-- Add one block of scalar-divided powers, from the highest index down. -/
def blockSumAux (powers : Array (Interval Int)) (start : Nat) :
    Nat → Interval Int → Interval Int
  | 0, total => total
  | n + 1, total =>
    blockSumAux powers start n
      (add (divideNat (powers[n]?.getD (Interval.point 0)) (2 * (start + n) + 1)) total)

/-- The sum of a block uses only scalar division and grid addition. -/
def blockSum (powers : Array (Interval Int)) (start n : Nat) : Interval Int :=
  blockSumAux powers start n (Interval.point 0)

/-- Apply the block Horner steps from the highest block down. -/
def blockHorner (precision : Nat) (powers : Array (Interval Int)) (stride : Interval Int)
    (start blockSize blocks : Nat) (tail : Interval Int) : Interval Int :=
  Internal.reverseHorner
    (fun k total => add (blockSum powers (start + blockSize * k) blockSize)
      (mul precision stride total))
    0 blocks tail

/-- Rectangular evaluation with a positive block size and an unpadded final partial block. -/
def logOddRectangular (precision : Nat) (X Q : Interval Int) (start n blockSize : Nat) :
    Interval Int :=
  let powers := powerTable precision Q blockSize
  let stride := powers[blockSize]?.getD (Interval.point 0)
  let blocks := n / blockSize
  let tail := blockSum powers (start + blockSize * blocks) (n % blockSize)
  mul precision X (blockHorner precision powers stride start blockSize blocks tail)

end LogPolynomial

/-- Share a power table across longer odd logarithm polynomials. -/
def logOddPolynomial (precision : Nat) (X Q : Interval Int) (start n : Nat) : Interval Int :=
  if n ≤ 4 then logOddHorner precision X Q start n
  else LogPolynomial.logOddRectangular precision X Q start n (max 1 n.sqrt)

/--
Evaluate the odd logarithm remainder with a grid power and an exact scalar denominator.

Using `1 - x²` before rounding avoids a zero-crossing grid divisor at low precision.
-/
def logOddRadius (precision : Nat) (X Q : Interval Int) (x : ℚ) (n : Nat) :
    Interval Int :=
  scaleRat (mul precision (pow precision Q n) (abs X)) (1 / (1 - x ^ 2))

/-- Enclose `log x` with the odd terms of its transformed series. -/
def logSeries (x : ℚ) (degree precision : Nat) : Interval Int :=
  let t := (x - 1) / (x + 1)
  let X := enclose precision t
  let Q := square precision X
  let n := (degree + 1) / 2
  let half := around (logOddPolynomial precision X Q 0 n) (logOddRadius precision X Q t n)
  add half half

/-- Remove a power of two and restore its multiple of `log 2`, omitting a zero multiple. -/
def logLarge (x : ℚ) (degree precision : Nat) : Interval Int :=
  let reduction := Enclosure.logScale x
  if reduction = 0 then logSeries x degree precision
  else
    add (logSeries (x / 2 ^ reduction) degree precision)
      (scaleRat (logSeries 2 degree precision) reduction)

/-- Enclose the logarithm of a positive rational, inverting arguments below one before reduction. -/
def log (x : ℚ) (degree precision : Nat) : RationalInterval :=
  toRationalInterval precision
    (if x < 1 then neg (logLarge x⁻¹ degree precision) else logLarge x degree precision)

end FloatLib.Numerics.Enclosure.BinaryGrid
