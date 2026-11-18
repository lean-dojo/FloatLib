/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Runtime
public import FloatLib.Numerics.Enclosure.Interval.BinaryGrid
public import FloatLib.Numerics.Kernel.RootProof

/-!
# Elementary enclosures evaluated on a binary grid

Here the Taylor polynomials and remainder bounds use integer interval arithmetic at `precision`
fractional bits. Each multiplication and scalar division rounds outward on that grid. Argument
reduction and scalar factors use exact rational arithmetic, and only the final endpoints are
decoded.

The degree selects the same Taylor polynomial as the rational kernels in `Elementary.Runtime`.
Containment holds at every degree and precision, zero included, so the precision and degree
estimates below only guide refinement and never affect soundness. A coarse grid can give wide
bounds, never wrong ones.

Long logarithm polynomials share a table of powers through rectangular splitting, as in Section 4 of
Fredrik Johansson, [*Efficient implementation of elementary functions in the medium-precision
range*](https://arxiv.org/abs/1410.7176).

The loops and the scalar factors are written for Lean's kernel: the Horner loops recurse with
`Nat.rec`, and the reduced argument, the remainder factors and the extra scale use
`FloatLib.Numerics.Kernel.Q`, `isqrt` and `size`. The theorems named `…_def`, and `…_zero` and
`…_succ` for the loops, state them in ordinary notation, and compiled code runs the earlier loops
and core's operations.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.BinaryGrid

open Interval.BinaryGrid
open FloatLib.Numerics.Kernel

/-- Add guard bits and a degree-dependent rounding allowance to a target grid width. -/
def workingPrecision (targetBits degree : Nat) : Nat :=
  targetBits + degree.log2 + 16

/--
Choose a grid width relative to a nonzero result scale.

The integer logarithms estimate the extra fractional bits needed for a small result. Consumers
handle exact zero themselves. A higher degree also raises the rounding allowance.
-/
def relativePrecision (targetBits : Nat) (scale : ℚ) (degree : Nat) : Nat :=
  workingPrecision (targetBits + (scale.den.log2 - scale.num.natAbs.log2)) degree

/--
Allow for repeated squaring and small exponential results when choosing a grid width.

Subtracting one also needs enough fractional bits to retain a small input's contribution.
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
  (fun a b =>
    Bool.casesOn (motive := fun _ => Interval Int) (Int.ble' (Int.ofNat 0) factor.num)
      ⟨b.lo, a.hi⟩ ⟨a.lo, b.hi⟩)
    (divBounds (Z.mul I.lo factor.num) (Int.ofNat factor.den))
    (divBounds (Z.mul I.hi factor.num) (Int.ofNat factor.den))

/-- Scaling divides the two scaled endpoints by the denominator, in the order the sign of the
factor gives. -/
theorem scaleRat_def (I : Interval Int) (factor : ℚ) :
    scaleRat I factor =
      (let a := divBounds (I.lo * factor.num) factor.den
       let b := divBounds (I.hi * factor.num) factor.den
       if 0 ≤ factor then ⟨a.lo, b.hi⟩ else ⟨b.lo, a.hi⟩) := by
  have hcond : Int.ble' (Int.ofNat 0) factor.num = true ↔ 0 ≤ factor := by
    rw [Z.ble'_iff]
    exact Rat.num_nonneg
  unfold scaleRat
  beta_reduce
  rw [Z.casesOn_eq_ite hcond, Z.mul_eq, Z.mul_eq]
  rfl

/-- Divide the coefficients by a natural scalar with outward rounding. -/
def divideNat (I : Interval Int) (n : Nat) : Interval Int :=
  ⟨Z.floorDiv I.lo n, Z.ceilDiv I.hi n⟩

namespace Internal

/-- Integer floor and ceiling division. A zero divisor gives the zero interval. -/
@[inline] def divideNat (I : Interval Int) (n : Nat) : Interval Int :=
  ⟨I.lo / (n : Int), -((-I.hi) / (n : Int))⟩

private theorem divBounds_hi_neg_fdiv (a b : Int) (hb : b ≠ 0) :
    (divBounds a b).hi = -((-a).fdiv b) := by
  by_cases h : b ∣ a
  · simp [divBounds_def, Int.neg_fdiv, hb, h, Int.fdiv_mul_cancel h]
  · have hne : a.fdiv b * b ≠ a := by
      intro heq
      exact h ⟨a.fdiv b, by simpa [Int.mul_comm] using heq.symm⟩
    simp [divBounds_def, Int.neg_fdiv, hb, h, hne, add_comm]

/-- Scaling by the inverse of a natural number is the integer floor and ceiling division. -/
theorem scaleRat_one_div (I : Interval Int) (n : Nat) :
    scaleRat I (1 / (n : ℚ)) = divideNat I n := by
  rw [scaleRat_def]
  by_cases hn : n = 0
  · simp [divideNat, hn, divBounds_def]
  have hnz : (n : Int) ≠ 0 := Int.natCast_ne_zero.mpr hn
  have hnonneg : (0 : ℚ) ≤ (n : ℚ)⁻¹ := by positivity
  simp only [one_div, ite_eq_left hnonneg, Rat.num_inv, Rat.den_inv,
    Rat.num_natCast, Rat.den_natCast, Int.sign_natCast_of_ne_zero hn, Nat.cast_one,
    mul_one, hnz, ite_false, Int.natAbs_natCast]
  rw [divBounds_hi_neg_fdiv I.hi n hnz, divBounds_def]
  simp [divideNat, Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg n)]

/-- Grid multiplication with two corner products when either factor is a point, in any order. -/
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

/-- `divideNat` equals the integer floor and ceiling division that compiled code runs. -/
@[csimp] theorem divideNat_eq_direct : divideNat = Internal.divideNat := by
  funext I n
  rw [divideNat, Z.floorDiv_eq, Z.ceilDiv_eq]
  rfl

/-- Dividing by a natural scalar is scaling by its rational inverse. -/
theorem divideNat_def (I : Interval Int) (n : Nat) :
    divideNat I n = scaleRat I (1 / (n : ℚ)) := by
  rw [Internal.scaleRat_one_div, divideNat_eq_direct]

/-- Grid multiplication equals `Internal.mul`, which needs two products for a point factor. -/
@[csimp] theorem mul_eq_point : Interval.BinaryGrid.mul = Internal.mul := by
  funext precision I J
  rw [Interval.BinaryGrid.mul_def]
  dsimp only [Internal.mul]
  split_ifs <;> simp_all [Interval.minOfFour, Interval.maxOfFour]

/-- Expand a midpoint interval using the upper endpoint of a radius enclosure. -/
def around (midpoint radius : Interval Int) : Interval Int :=
  ⟨Z.sub midpoint.lo radius.hi, Z.add midpoint.hi radius.hi⟩

/-- The expanded interval subtracts and adds the upper endpoint of the radius. -/
theorem around_def (midpoint radius : Interval Int) :
    around midpoint radius = ⟨midpoint.lo - radius.hi, midpoint.hi + radius.hi⟩ := by
  rw [around, Z.sub_eq, Z.add_eq]

/--
Exponential Horner steps, with every product and division rounded on the chosen grid:
`expHorner_zero` and `expHorner_succ` are its two equations. The recursion is written with
`Nat.rec`, which Lean's kernel steps through at a quarter of the cost of a compiled match.
-/
def expHorner (precision : Nat) (X : Interval Int) (start n : Nat) : Interval Int :=
  Nat.rec (motive := fun _ => Nat → Interval Int) (fun _ => Interval.point (Int.ofNat 0))
    (fun _ tail start =>
      add (Interval.point (scale precision))
        (divideNat (mul precision X (tail (Nat.succ start))) (Nat.succ start)))
    n start

/-- No Horner step gives the zero interval. -/
theorem expHorner_zero (precision : Nat) (X : Interval Int) (start : Nat) :
    expHorner precision X start 0 = Interval.point 0 := rfl

/-- One more Horner step multiplies by the argument, divides by the index and adds one. -/
theorem expHorner_succ (precision : Nat) (X : Interval Int) (start n : Nat) :
    expHorner precision X start (n + 1) =
      add (Interval.point (scale precision))
        (divideNat (mul precision X (expHorner precision X (start + 1) n)) (start + 1)) := rfl

/--
Odd logarithm terms evaluated by Horner steps in the square of the argument:
`logOddHorner_zero` and `logOddHorner_succ` are its two equations.
-/
def logOddHorner (precision : Nat) (X Q : Interval Int) (start n : Nat) : Interval Int :=
  Nat.rec (motive := fun _ => Nat → Interval Int) (fun _ => Interval.point (Int.ofNat 0))
    (fun _ tail start =>
      add (divideNat X (Nat.succ (Nat.mul 2 start)))
        (mul precision Q (tail (Nat.succ start))))
    n start

/-- No Horner step gives the zero interval. -/
theorem logOddHorner_zero (precision : Nat) (X Q : Interval Int) (start : Nat) :
    logOddHorner precision X Q start 0 = Interval.point 0 := rfl

/-- One more Horner step adds the term of the next odd index. -/
theorem logOddHorner_succ (precision : Nat) (X Q : Interval Int) (start n : Nat) :
    logOddHorner precision X Q start (n + 1) =
      add (divideNat X (2 * start + 1))
        (mul precision Q (logOddHorner precision X Q (start + 1) n)) := rfl

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

/-- Exponential Horner evaluation equals the accumulator loop that compiled code runs. -/
@[csimp] theorem expHorner_eq_iter : expHorner = expHornerIter := by
  funext precision X start n
  dsimp only [expHornerIter]
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [expHorner_succ, Internal.reverseHorner_succ, ih]

/-- Odd logarithm Horner evaluation equals the accumulator loop that compiled code runs. -/
@[csimp] theorem logOddHorner_eq_iter : logOddHorner = logOddHornerIter := by
  funext precision X Q start n
  dsimp only [logOddHornerIter]
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [logOddHorner_succ, Internal.reverseHorner_succ, ih]

/-- Evaluate the exponential remainder bound without forming an exact rational power. -/
def expRadius (precision : Nat) (X : Interval Int) (n : Nat) : Interval Int :=
  scaleRat (pow precision (abs X) n) (Q.mk (Int.ofNat (Nat.succ n)) (Nat.mul (factorial n) n))

/-- The exponential remainder bound on the grid, with its factor in ordinary notation. -/
theorem expRadius_def (precision : Nat) (X : Interval Int) (n : Nat) :
    expRadius precision X n =
      scaleRat (pow precision (abs X) n) (((n + 1 : Nat) : ℚ) / ((n.factorial : ℚ) * n)) := by
  unfold expRadius
  rw [Q.mk_eq, Rat.mkRat_eq_div, factorial_eq]
  congr 1
  change (((n + 1 : Nat) : Int) : ℚ) / ((n.factorial * n : Nat) : ℚ) = _
  push_cast
  rfl

/-- Enclose the exponential of a small argument with its Taylor polynomial and remainder bound. -/
def expSmall (x : ℚ) (degree precision : Nat) : Interval Int :=
  let X := enclose precision x
  around (expHorner precision X 0 (degree + 1)) (expRadius precision X (degree + 1))

/--
Square `n` times, rounding outward after each square, to undo exponential range reduction:
`squareRepeat_zero` and `squareRepeat_succ` are its two equations.
-/
def squareRepeat (precision : Nat) (I : Interval Int) (n : Nat) : Interval Int :=
  Nat.rec (motive := fun _ => Interval Int) I (fun _ squared => square precision squared) n

/-- No squaring returns the interval. -/
theorem squareRepeat_zero (precision : Nat) (I : Interval Int) :
    squareRepeat precision I 0 = I := rfl

/-- One more squaring squares the result so far. -/
theorem squareRepeat_succ (precision : Nat) (I : Interval Int) (n : Nat) :
    squareRepeat precision I (n + 1) = square precision (squareRepeat precision I n) := rfl

/--
Balance Taylor work against extra squarings using the degree and requested grid width.

The square-root estimate limits squaring work while the degree is small, and the quotient reduces
it as refinement raises the degree. A small input already supplies some reduction without
squaring.
-/
def expExtraScale (x : ℚ) (degree precision : Nat) : Nat :=
  Nat.sub (minNat (isqrt (Nat.mul 4 precision)) (Nat.div precision (Nat.succ degree)))
    (Nat.sub (Nat.sub (size x.den) 1) (Nat.sub (size (Z.natAbs x.num)) 1))

/-- The extra scale, with the square root and the binary logarithms in ordinary notation. -/
theorem expExtraScale_def (x : ℚ) (degree precision : Nat) :
    expExtraScale x degree precision =
      min (Nat.sqrt (4 * precision)) (precision / (degree + 1)) -
        (x.den.log2 - x.num.natAbs.log2) := by
  unfold expExtraScale
  rw [minNat_eq, isqrt_eq, Z.natAbs_eq, log2_eq_size_sub_one x.den,
    log2_eq_size_sub_one x.num.natAbs]
  rfl

/-- Enclose the exponential, with extra grid bits to cover the extra range-restoring squares. -/
def exp (x : ℚ) (degree precision : Nat) : RationalInterval :=
  let extra := expExtraScale x degree precision
  let reduction := Enclosure.expScale x + extra
  let working := precision + extra
  toRationalInterval working
    (squareRepeat working (expSmall (Q.divPow2 x reduction) degree working) reduction)

/-- The grid exponential, with the reduced argument in ordinary notation. -/
theorem exp_def (x : ℚ) (degree precision : Nat) :
    exp x degree precision =
      toRationalInterval (precision + expExtraScale x degree precision)
        (squareRepeat (precision + expExtraScale x degree precision)
          (expSmall (x / 2 ^ (Enclosure.expScale x + expExtraScale x degree precision)) degree
            (precision + expExtraScale x degree precision))
          (Enclosure.expScale x + expExtraScale x degree precision)) := by
  unfold exp
  simp only [Q.divPow2_eq]

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

/-- Sum of one block, by scalar division and grid addition alone. -/
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

/-- Odd logarithm polynomial: Horner steps up to four terms, rectangular splitting above. -/
def logOddPolynomial (precision : Nat) (X Q : Interval Int) (start n : Nat) : Interval Int :=
  if n ≤ 4 then logOddHorner precision X Q start n
  else LogPolynomial.logOddRectangular precision X Q start n (max 1 n.sqrt)

/--
Evaluate the odd logarithm remainder with a grid power and an exact scalar denominator.

Using `1 - x²` before rounding avoids a zero-crossing grid divisor at low precision.
-/
def logOddRadius (precision : Nat) (X Q : Interval Int) (x : ℚ) (n : Nat) :
    Interval Int :=
  scaleRat (mul precision (pow precision Q n) (abs X))
    (Kernel.Q.inv (Kernel.Q.sub 1 (Kernel.Q.mul x x)))

/-- The logarithm remainder bound on the grid, with its factor in ordinary notation. -/
theorem logOddRadius_def (precision : Nat) (X Q : Interval Int) (x : ℚ) (n : Nat) :
    logOddRadius precision X Q x n =
      scaleRat (mul precision (pow precision Q n) (abs X)) (1 / (1 - x ^ 2)) := by
  unfold logOddRadius
  rw [Kernel.Q.inv_eq, Kernel.Q.sub_eq, Kernel.Q.mul_eq, ← pow_two, one_div]

/-- Enclose `log x` with the odd terms of its transformed series. -/
def logSeries (x : ℚ) (degree precision : Nat) : Interval Int :=
  let t := Kernel.Q.div (Kernel.Q.sub x 1) (Kernel.Q.add x 1)
  let X := enclose precision t
  let Q := square precision X
  let n := (degree + 1) / 2
  let half := around (logOddPolynomial precision X Q 0 n) (logOddRadius precision X Q t n)
  add half half

/-- The logarithm series on the grid, with its argument in ordinary notation. -/
theorem logSeries_def (x : ℚ) (degree precision : Nat) :
    logSeries x degree precision =
      (let t := (x - 1) / (x + 1)
       let X := enclose precision t
       let Q := square precision X
       let n := (degree + 1) / 2
       let half := around (logOddPolynomial precision X Q 0 n) (logOddRadius precision X Q t n)
       add half half) := by
  unfold logSeries
  simp only [Kernel.Q.div_eq, Kernel.Q.sub_eq, Kernel.Q.add_eq]

/--
A logarithm series degree for a positive `value`, aiming at a truncation error of about `2 ^ -bits`.

With `value = n / d` in lowest terms the series runs in `t = (n - d) / (n + d)`, and each pair of
degrees gains `log₂ (1 / t²)` bits. The estimate counts `log₂` of the integer part of `1 / t²`,
rounded down and at least one bit, and it never overcounts while `t² ≤ 1/2`, that is for `value`
between `3 - 2√2 ≈ 0.17` and `3 + 2√2 ≈ 5.83`. Farther from one a pair of degrees gains less than
one bit, so the degree falls short of the target and the enclosure is wider. It stays sound at every
degree (`containsReal_logUnreduced`).
-/
def logSeriesDegree (value : ℚ) (bits : Nat) : Nat :=
  let numerator := value.num.natAbs
  let gap := if numerator ≤ value.den then value.den - numerator else numerator - value.den
  if gap = 0 then 1
  else 2 * (bits / max 1 ((numerator + value.den) ^ 2 / gap ^ 2).log2 + 1) - 1

/--
Enclose `log value` for a positive rational on the grid of `precision` fractional bits with the
transformed series in `(value - 1) / (value + 1)`, without the argument reduction of `log`. It
suits values near one: its degree (`logSeriesDegree`) aims at an error of about `2 ^ -precision`
only for values between about `0.17` and `5.83`, and gives a sound but wider enclosure outside.
-/
def logUnreduced (value : ℚ) (precision : Nat) : Interval Int :=
  logSeries value (logSeriesDegree value precision) precision

/-- Remove a power of two and restore its multiple of `log 2`, omitting a zero multiple. -/
def logLarge (x : ℚ) (degree precision : Nat) : Interval Int :=
  let reduction := Enclosure.logScale x
  if reduction = 0 then logSeries x degree precision
  else
    add (logSeries (Kernel.Q.divPow2 x reduction) degree precision)
      (scaleRat (logSeries 2 degree precision) reduction)

/-- The reduced logarithm on the grid, with the reduced argument in ordinary notation. -/
theorem logLarge_def (x : ℚ) (degree precision : Nat) :
    logLarge x degree precision =
      if Enclosure.logScale x = 0 then logSeries x degree precision
      else
        add (logSeries (x / 2 ^ Enclosure.logScale x) degree precision)
          (scaleRat (logSeries 2 degree precision) (Enclosure.logScale x)) := by
  unfold logLarge
  simp only [Kernel.Q.divPow2_eq]

/-- Enclose the logarithm of a positive rational, inverting arguments below one before reduction. -/
def log (x : ℚ) (degree precision : Nat) : RationalInterval :=
  toRationalInterval precision
    (Bool.casesOn (motive := fun _ => Interval Int) (Kernel.Q.lt x 1)
      (logLarge x degree precision) (neg (logLarge (Kernel.Q.inv x) degree precision)))

/-- The grid logarithm, in ordinary notation. -/
theorem log_def (x : ℚ) (degree precision : Nat) :
    log x degree precision =
      toRationalInterval precision
        (if x < 1 then neg (logLarge x⁻¹ degree precision) else logLarge x degree precision) := by
  unfold log
  rw [Kernel.Q.casesOn_lt, Kernel.Q.inv_eq]

end FloatLib.Numerics.Enclosure.BinaryGrid
