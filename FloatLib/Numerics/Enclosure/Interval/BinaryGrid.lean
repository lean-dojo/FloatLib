/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Basic
public import FloatLib.Numerics.Enclosure.Interval.Bounds
public import FloatLib.Numerics.Kernel.QProof

/-!
# Integer arithmetic on a binary interval grid

At `precision` fractional bits, an integer coefficient `z` represents `z / 2^precision`. Intervals
are plain `Interval Int`, and each operation takes the scale as an argument instead of storing it in
the interval. Coefficients have unbounded magnitude, so the arithmetic can't overflow.

Addition, subtraction, and negation are exact. Multiplication rounds the smallest and largest
integer products with signed shifts, and division uses four integer quotients and rejects a divisor
interval that contains zero. Values become rationals only at the interface, never between arithmetic
steps.

The endpoint construction follows S. M. Rump, [Verification methods: Rigorous results using
floating-point arithmetic](https://doi.org/10.1017/S096249291000005X), *Acta Numerica* 19 (2010),
§§5.1-5.3. `BinaryGridProof` proves containment for arbitrary real members of the input intervals.

## Evaluation in Lean's kernel

These operations are checked by `decide +kernel` in proofs about concrete numbers, so their bodies
are written with the kernel functions of `FloatLib.Numerics.Kernel.Z` (one `Int.rec` per integer
read and the bare `Nat` functions inside). Core's `Int.mul`, `min` and `>>>` cost the kernel 40 to
150 µs each through instances and matches, which made one interval product cost 630 µs in a fresh
kernel state, against 150 µs now. Each
operation has a theorem `…_def` that states it with the usual integer operations, for all inputs:
`mul_def` is the four-corner rule, `roundUp_def` is `-((-z) >>> precision)`, and so on. Proofs
about an operation rewrite with that theorem. Compiled code is unchanged, because the kernel
functions compile to core's operations (`Z.add_eq_compiled` and its siblings).
-/

@[expose] public section

namespace FloatLib.Numerics.Interval.BinaryGrid

open FloatLib.Numerics.Kernel

/-- Positive integer scale `2 ^ precision` of a grid with `precision` fractional bits. -/
def scale (precision : Nat) : Int :=
  Int.ofNat (Nat.shiftLeft 1 precision)

/-- The scale is one shifted left by the precision. -/
theorem scale_def (precision : Nat) : scale precision = (1 : Int) <<< precision := rfl

/-- Exact rational interpretation of an integer coefficient on the binary grid. -/
def toRat (precision : Nat) (z : Int) : ℚ :=
  Kernel.Q.mk z (Nat.shiftLeft 1 precision)

/-- The rational of a coefficient is the coefficient over the scale. -/
theorem toRat_def (precision : Nat) (z : Int) :
    toRat precision z = Rat.divInt z (scale precision) := by
  rw [toRat, Kernel.Q.mk_eq]
  rfl

/-- Decode a coefficient as its rational value. Every coefficient is finite. -/
def decode (precision : Nat) (z : Int) : Option ℚ :=
  some (toRat precision z)

/-- Floor of `z / 2^precision`. The signed shift rounds negative values downward too. -/
def roundDown (precision : Nat) (z : Int) : Int :=
  Z.shiftRight z precision

/-- Rounding down is the signed shift to the right. -/
theorem roundDown_def (precision : Nat) (z : Int) : roundDown precision z = z >>> precision :=
  Z.shiftRight_eq z precision

/-- Ceiling of `z / 2^precision`, obtained by negating a downward-rounded negative. -/
def roundUp (precision : Nat) (z : Int) : Int :=
  Z.ceilShift z precision

/-- Rounding up is the negated signed shift of the negation. -/
theorem roundUp_def (precision : Nat) (z : Int) :
    roundUp precision z = -((-z) >>> precision) :=
  Z.ceilShift_eq z precision

/-- Coarsen a grid interval by `shift` fractional bits, rounding both endpoints outward. -/
def coarsen (shift : Nat) (I : Interval Int) : Interval Int :=
  ⟨roundDown shift I.lo, roundUp shift I.hi⟩

/--
Integer floor and ceiling of `a / b`, for a nonzero denominator of either sign.

One signed floor division supplies both endpoints. Testing the integer product detects exact
division without computing another quotient or a rational greatest common divisor.
-/
def divBounds (a b : Int) : Interval Int :=
  (fun q => ⟨q, Bool.casesOn (motive := fun _ => Int) (Int.beq' (Z.mul q b) a) (Z.add q 1) q⟩)
    (Z.fdiv a b)

/-- The quotient bounds are the floor quotient, and one more unless the division is exact. -/
theorem divBounds_def (a b : Int) :
    divBounds a b =
      (let q := a.fdiv b
       ⟨q, if q * b = a then q else q + 1⟩) := by
  change Interval.mk (Z.fdiv a b)
    (Bool.casesOn (motive := fun _ => Int) (Int.beq' (Z.mul (Z.fdiv a b) b) a) (Z.add (Z.fdiv a
      b) 1)
      (Z.fdiv a b)) = _
  rw [Z.casesOn_eq_ite (Z.beq'_iff _ _), Z.mul_eq, Z.add_eq, Z.fdiv_eq]

/-- Enclose an exact rational by neighboring grid coefficients. -/
def enclose (precision : Nat) (q : ℚ) : Interval Int :=
  divBounds (Z.shiftLeft q.num precision) (Int.ofNat q.den)

/-- The enclosure of a rational divides its shifted numerator by its denominator. -/
theorem enclose_def (precision : Nat) (q : ℚ) :
    enclose precision q = divBounds (q.num <<< precision) q.den := by
  rw [enclose, Z.shiftLeft_eq]
  rfl

/-- Exact negation on the grid, with the endpoints exchanged. -/
def neg (I : Interval Int) : Interval Int :=
  ⟨Z.neg I.hi, Z.neg I.lo⟩

/-- Negation exchanges and negates the endpoints. -/
theorem neg_def (I : Interval Int) : neg I = ⟨-I.hi, -I.lo⟩ := by
  rw [neg, Z.neg_eq, Z.neg_eq]

/-- Exact addition of intervals on the same grid. -/
def add (I J : Interval Int) : Interval Int :=
  ⟨Z.add I.lo J.lo, Z.add I.hi J.hi⟩

/-- Addition adds the lower endpoints and the upper endpoints. -/
theorem add_def (I J : Interval Int) : add I J = ⟨I.lo + J.lo, I.hi + J.hi⟩ := by
  rw [add, Z.add_eq, Z.add_eq]

/-- Exact subtraction of intervals on the same grid. -/
def sub (I J : Interval Int) : Interval Int :=
  ⟨Z.sub I.lo J.hi, Z.sub I.hi J.lo⟩

/-- Subtraction subtracts the opposite endpoints. -/
theorem sub_def (I J : Interval Int) : sub I J = ⟨I.lo - J.hi, I.hi - J.lo⟩ := by
  rw [sub, Z.sub_eq, Z.sub_eq]

/-- Multiply using four integer products and two outward-rounded shifts. -/
def mul (precision : Nat) (I J : Interval Int) : Interval Int :=
  (fun a b c d =>
    ⟨roundDown precision (Z.min (Z.min a b) (Z.min c d)),
      roundUp precision (Z.max (Z.max a b) (Z.max c d))⟩)
    (Z.mul I.lo J.lo) (Z.mul I.lo J.hi) (Z.mul I.hi J.lo) (Z.mul I.hi J.hi)

/-- Multiplication rounds the smallest and the largest of the four corner products outward. -/
theorem mul_def (precision : Nat) (I J : Interval Int) :
    mul precision I J =
      (let a := I.lo * J.lo
       let b := I.lo * J.hi
       let c := I.hi * J.lo
       let d := I.hi * J.hi
       ⟨roundDown precision (minOfFour a b c d), roundUp precision (maxOfFour a b c d)⟩) := by
  change Interval.mk
    (roundDown precision (Z.min (Z.min (Z.mul I.lo J.lo) (Z.mul I.lo J.hi))
      (Z.min (Z.mul I.hi J.lo) (Z.mul I.hi J.hi))))
    (roundUp precision (Z.max (Z.max (Z.mul I.lo J.lo) (Z.mul I.lo J.hi))
      (Z.max (Z.mul I.hi J.lo) (Z.mul I.hi J.hi)))) = _
  simp only [Z.min_eq, Z.max_eq, Z.mul_eq]

/--
Divide using scaled integer numerators, returning `none` for a denominator containing zero.

The four corner divisions round outward on the same grid as the input endpoints. No rational
normalization occurs in this operation.
-/
def div? (precision : Nat) (I J : Interval Int) : Option (Interval Int) :=
  Bool.casesOn (motive := fun _ => Option (Interval Int))
    (Bool.or (Int.blt' J.hi (Int.ofNat 0)) (Int.blt' (Int.ofNat 0) J.lo))
    none
    ((fun lo hi =>
      (fun a b c d =>
        some ⟨Z.min (Z.min a.lo b.lo) (Z.min c.lo d.lo), Z.max (Z.max a.hi b.hi) (Z.max c.hi d.hi)⟩)
        (divBounds lo J.lo) (divBounds lo J.hi) (divBounds hi J.lo) (divBounds hi J.hi))
      (Z.shiftLeft I.lo precision) (Z.shiftLeft I.hi precision))

/-- Division takes the four corner quotients when the divisor interval excludes zero. -/
theorem div?_def (precision : Nat) (I J : Interval Int) :
    div? precision I J =
      if J.hi < 0 ∨ 0 < J.lo then
        let lo := I.lo <<< precision
        let hi := I.hi <<< precision
        let a := divBounds lo J.lo
        let b := divBounds lo J.hi
        let c := divBounds hi J.lo
        let d := divBounds hi J.hi
        some ⟨minOfFour a.lo b.lo c.lo d.lo, maxOfFour a.hi b.hi c.hi d.hi⟩
      else none := by
  have hcond : Bool.or (Int.blt' J.hi (Int.ofNat 0)) (Int.blt' (Int.ofNat 0) J.lo) = true ↔
      J.hi < 0 ∨ 0 < J.lo := by
    rw [Bool.or_eq_true, Z.blt'_iff, Z.blt'_iff]
    rfl
  unfold div?
  rw [Z.casesOn_eq_ite hcond]
  simp only [Z.min_eq, Z.max_eq, Z.shiftLeft_eq]

/-- Exact absolute-value enclosure, taking a zero lower bound when the interval crosses zero. -/
def abs (I : Interval Int) : Interval Int :=
  Bool.casesOn (motive := fun _ => Interval Int) (Int.ble' (Int.ofNat 0) I.lo)
    (Bool.casesOn (motive := fun _ => Interval Int) (Int.ble' I.hi (Int.ofNat 0))
      ⟨Int.ofNat 0, Z.max (Z.neg I.lo) I.hi⟩
      (neg I))
    I

/-- The absolute value keeps a nonnegative interval, negates a nonpositive one, and starts at
zero otherwise. -/
theorem abs_def (I : Interval Int) :
    abs I =
      if 0 ≤ I.lo then I
      else if I.hi ≤ 0 then neg I
      else ⟨0, max (-I.lo) I.hi⟩ := by
  unfold abs
  rw [Z.casesOn_eq_ite (Z.ble'_iff _ _), Z.casesOn_eq_ite (Z.ble'_iff _ _), Z.max_eq, Z.neg_eq]
  rfl

/--
Square with a nonnegative lower bound, including for intervals that cross zero.

Using the range of the square avoids the negative lower endpoint produced by treating the two
occurrences of the input as independent factors.
-/
def square (precision : Nat) (I : Interval Int) : Interval Int :=
  (fun a b =>
    ⟨roundDown precision
        (Bool.casesOn (motive := fun _ => Int) (Int.ble' (Int.ofNat 0) I.lo)
          (Bool.casesOn (motive := fun _ => Int) (Int.ble' I.hi (Int.ofNat 0)) (Int.ofNat 0) b)
          a),
      roundUp precision (Z.max a b)⟩)
    (Z.mul I.lo I.lo) (Z.mul I.hi I.hi)

/-- The square rounds the smallest and the largest square of a member outward. -/
theorem square_def (precision : Nat) (I : Interval Int) :
    square precision I =
      (let a := I.lo * I.lo
       let b := I.hi * I.hi
       let lo := if 0 ≤ I.lo then a else if I.hi ≤ 0 then b else 0
       ⟨roundDown precision lo, roundUp precision (max a b)⟩) := by
  change Interval.mk
    (roundDown precision
      (Bool.casesOn (motive := fun _ => Int) (Int.ble' (Int.ofNat 0) I.lo)
        (Bool.casesOn (motive := fun _ => Int) (Int.ble' I.hi (Int.ofNat 0)) (Int.ofNat 0)
          (Z.mul I.hi I.hi))
        (Z.mul I.lo I.lo)))
    (roundUp precision (Z.max (Z.mul I.lo I.lo) (Z.mul I.hi I.hi))) = _
  rw [Z.casesOn_eq_ite (Z.ble'_iff _ _), Z.casesOn_eq_ite (Z.ble'_iff _ _), Z.max_eq, Z.mul_eq,
    Z.mul_eq]
  rfl

namespace Internal

namespace Compiled

/-- Repeated squaring by recursion on the halved exponent, which is what compiled code runs. -/
def pow (precision : Nat) (I : Interval Int) (n : Nat) : Interval Int :=
  if h : n = 0 then
    point (scale precision)
  else if n = 1 then
    I
  else
    let a := square precision (pow precision I (n / 2))
    if n % 2 = 0 then a else mul precision a I
termination_by n

end Compiled

/--
Repeated squaring for the endpoint evaluations in `BinaryGrid.pow`.

With the squaring in its own helper, the public operation can use monotonicity before interval
evaluation. The exponent-one branch avoids multiplying by a scaled representation of one. The
recursion runs on a count that starts at the exponent, so that Lean's kernel evaluates it, and
each step halves the exponent, so the count never runs out (`pow_def`).
-/
def pow (precision : Nat) (I : Interval Int) (n : Nat) : Interval Int :=
  Nat.rec (motive := fun _ => Nat → Interval Int) (fun _ => point (scale precision))
    (fun _ step n =>
      Bool.casesOn (motive := fun _ => Interval Int) (Nat.beq n 0)
        (Bool.casesOn (motive := fun _ => Interval Int) (Nat.beq n 1)
          ((fun a =>
            Bool.casesOn (motive := fun _ => Interval Int) (Nat.beq (Nat.mod n 2) 0)
              (mul precision a I) a)
            (square precision (step (Nat.div n 2))))
          I)
        (point (scale precision)))
    n n

/-- With a count of at least the exponent, the counted recursion is the recursion on the halved
exponent. -/
private theorem pow_loop (precision : Nat) (I : Interval Int) :
    ∀ count n : Nat, n ≤ count →
      Nat.rec (motive := fun _ => Nat → Interval Int) (fun _ => point (scale precision))
        (fun _ step n =>
          Bool.casesOn (motive := fun _ => Interval Int) (Nat.beq n 0)
            (Bool.casesOn (motive := fun _ => Interval Int) (Nat.beq n 1)
              ((fun a =>
                Bool.casesOn (motive := fun _ => Interval Int) (Nat.beq (Nat.mod n 2) 0)
                  (mul precision a I) a)
                (square precision (step (Nat.div n 2))))
              I)
            (point (scale precision)))
        count n = Compiled.pow precision I n := by
  intro count
  induction count with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := Nat.le_zero.1 hn
    rw [Compiled.pow]
    rfl
  | succ count ih =>
    intro n hn
    rw [Compiled.pow]
    by_cases h0 : n = 0
    · subst h0
      rfl
    · by_cases h1 : n = 1
      · subst h1
        rfl
      · have hbeq0 : Nat.beq n 0 = false := by
          cases h : Nat.beq n 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) h0
        have hbeq1 : Nat.beq n 1 = false := by
          cases h : Nat.beq n 1
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) h1
        have hhalf : n / 2 ≤ count := by omega
        change Bool.casesOn (motive := fun _ => Interval Int) (Nat.beq n 0)
          (Bool.casesOn (motive := fun _ => Interval Int) (Nat.beq n 1)
            (Bool.casesOn (motive := fun _ => Interval Int) (Nat.beq (n % 2) 0)
              (mul precision (square precision (Nat.rec (motive := fun _ => Nat → Interval Int)
                _ _ count (n / 2))) I)
              (square precision (Nat.rec (motive := fun _ => Nat → Interval Int)
                _ _ count (n / 2))))
            I)
          (point (scale precision)) = _
        rw [hbeq0, hbeq1, ih (n / 2) hhalf, dite_eq_right h0, ite_eq_right h1]
        by_cases hpar : n % 2 = 0
        · rw [hpar, ite_eq_left rfl]
          rfl
        · have hodd : Nat.beq (n % 2) 0 = false := by
            cases h : Nat.beq (n % 2) 0
            · rfl
            · exact absurd (Nat.eq_of_beq_eq_true h) hpar
          rw [hodd, ite_eq_right hpar]

/-- The counted recursion is the recursion on the halved exponent, which compiled code runs. -/
@[csimp] theorem pow_eq_compiled : @pow = @Compiled.pow := by
  funext precision I n
  exact pow_loop precision I n n le_rfl

/-- Repeated squaring: the power is the square of the power of half the exponent, times the
base when the exponent is odd. -/
theorem pow_def (precision : Nat) (I : Interval Int) (n : Nat) :
    pow precision I n =
      if n = 0 then point (scale precision)
      else if n = 1 then I
      else
        let a := square precision (pow precision I (n / 2))
        if n % 2 = 0 then a else mul precision a I := by
  rw [pow_eq_compiled, Compiled.pow]
  split <;> rfl

end Internal

/--
Natural powers with logarithmically many interval operations.

Odd powers are increasing, so their lower and upper bounds come from evaluating at each endpoint.
Even powers use the absolute-value interval. These choices avoid treating repeated occurrences of
the input as independent values. Each evaluation still rounds outward at intermediate steps.
Exponents zero and one are exact, and a point interval needs one repeated-squaring evaluation.
-/
def pow (precision : Nat) (I : Interval Int) (n : Nat) : Interval Int :=
  Bool.casesOn (motive := fun _ => Interval Int) (Nat.beq n 0)
    (Bool.casesOn (motive := fun _ => Interval Int) (Nat.beq n 1)
      (Bool.casesOn (motive := fun _ => Interval Int) (Nat.beq (Nat.mod n 2) 0)
        (Bool.casesOn (motive := fun _ => Interval Int) (Int.beq' I.lo I.hi)
          ⟨(Internal.pow precision (point I.lo) n).lo, (Internal.pow precision (point I.hi) n).hi⟩
          (Internal.pow precision I n))
        (Internal.pow precision (abs I) n))
      I)
    (point (scale precision))

/-- The power by cases on the exponent: zero, one, even, and odd on a point or on an interval. -/
theorem pow_def (precision : Nat) (I : Interval Int) (n : Nat) :
    pow precision I n =
      if n = 0 then point (scale precision)
      else if n = 1 then I
      else if n % 2 = 0 then Internal.pow precision (abs I) n
      else if I.lo = I.hi then Internal.pow precision I n
      else
        ⟨(Internal.pow precision (point I.lo) n).lo,
          (Internal.pow precision (point I.hi) n).hi⟩ := by
  have hbeq (a b : Nat) : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]
  unfold pow
  rw [Z.casesOn_eq_ite (hbeq n 0), Z.casesOn_eq_ite (hbeq n 1),
    Z.casesOn_eq_ite (hbeq (Nat.mod n 2) 0), Z.casesOn_eq_ite (Z.beq'_iff _ _)]
  rfl

end FloatLib.Numerics.Interval.BinaryGrid
