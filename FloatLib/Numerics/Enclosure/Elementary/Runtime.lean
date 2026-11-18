/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Taylor
public import FloatLib.Numerics.Enclosure.Rational.Runtime

/-!
# Rational enclosures for exponential and logarithm

Everything here is exact rational arithmetic, Taylor polynomials and remainder bounds alike. `exp`
reduces the argument by a power of two and restores the scale by repeated squaring. `log` first
reduces a positive argument to `[1, 2)` and then restores the removed multiple of `log 2`, and its
reduced series uses the identity `log x = log (1 + t) - log (1 - t)`, where `t = (x - 1) / (x + 1)`.
Every series argument satisfies `|t| ≤ 1/3`.

A natural argument sets the polynomial degree. It isn't a floating-point precision or a search
timeout, and the endpoint error tends to zero as it grows. What you get back are bounds, which a
caller can use to separate the exact value from rounding boundaries or to show that both endpoints
round to the same result.

Lean's kernel evaluates these definitions when a proof checks an enclosure by `decide`, so the
ones on its path are written with the functions of `FloatLib.Numerics.Kernel.Q` and `Z`, which
compute the same rationals and integers in fewer kernel steps. Each has a theorem named `…_def`
that states it in ordinary notation, and compiled code runs core's operations as before.

Soundness theorems in `Elementary.Proof` use Mathlib's real Taylor remainder bounds, and the
underlying series are the exponential and logarithm expansions in the NIST [Digital Library of
Mathematical Functions, §4.2.E19](https://dlmf.nist.gov/4.2.E19) and
[§4.6.E1](https://dlmf.nist.gov/4.6.E1). That logarithm change of variable also appears in
[§4.6.E4](https://dlmf.nist.gov/4.6.E4).
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure

open RationalInterval

/--
The first `n` terms of the exponential series, evaluated exactly by binary splitting
(`expTaylor_def` states the sum).
-/
def expTaylor (x : ℚ) (n : Nat) : ℚ := Taylor.exp x n

/-- The exponential Taylor sum is its evaluation by binary splitting. -/
theorem expTaylor_eq_binarySplit : expTaylor = Taylor.exp := rfl

/-- `expTaylor x n` is the sum of the first `n` terms of the exponential series. -/
theorem expTaylor_def (x : ℚ) (n : Nat) :
    expTaylor x n = ∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℚ) := by
  rw [expTaylor_eq_binarySplit, Taylor.exp_eq_sum]

/--
Absolute exponential remainder bound for `|x| ≤ 1` and `n > 0`: `expRadius_def` states it as
`|x| ^ n * (n + 1) / (n ! * n)`. The body builds the numerator and the denominator from naturals
and reduces once.
-/
def expRadius (x : ℚ) (n : Nat) : ℚ :=
  Kernel.Q.mk (Int.ofNat (Nat.mul (Nat.pow (Kernel.Z.natAbs x.num) n) (Nat.succ n)))
    (Nat.mul (Nat.pow x.den n) (Nat.mul (Kernel.factorial n) n))

/-- The exponential remainder bound, in ordinary notation. -/
theorem expRadius_def (x : ℚ) (n : Nat) :
    expRadius x n = |x| ^ n * ((n + 1 : Nat) : ℚ) / ((n.factorial : ℚ) * n) := by
  unfold expRadius
  rw [Kernel.Q.mk_eq, Rat.mkRat_eq_div, Kernel.Z.natAbs_eq, Kernel.factorial_eq,
    Kernel.Q.abs_eq_natAbs_div, div_pow, div_mul_eq_mul_div, div_div]
  change ((((x.num.natAbs ^ n * (n + 1) : Nat) : Int) : ℚ)) / ((x.den ^ n * (n.factorial * n) :
    Nat) : ℚ) = _
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- Enclose `exp x` on `|x| ≤ 1`, using at least the constant Taylor term. -/
def expSmall (x : ℚ) (degree : Nat) : RationalInterval :=
  around (expTaylor x (degree + 1)) (expRadius x (degree + 1))

/--
A binary reduction scale determined by the integer part of the absolute argument.

Dividing by this power of two puts the absolute argument below one. Using the quotient rather
than the numerator keeps the scale small for high-precision rational inputs close to one.
-/
def expScale (x : ℚ) : Nat :=
  (x.num.natAbs / x.den).log2 + 1

/-- Enclose the exponential of any rational argument by reduction and repeated squaring. -/
def exp (x : ℚ) (degree : Nat) : RationalInterval :=
  let scale := expScale x
  (expSmall (Kernel.Q.divPow2 x scale) degree).squareRepeat scale

/-- The exponential enclosure: the argument divided by `2 ^ expScale x`, then squared back. -/
theorem exp_def (x : ℚ) (degree : Nat) :
    exp x degree = (expSmall (x / (2 : ℚ) ^ expScale x) degree).squareRepeat (expScale x) := by
  change (expSmall (Kernel.Q.divPow2 x (expScale x)) degree).squareRepeat (expScale x) = _
  rw [Kernel.Q.divPow2_eq]

/-- The first `n` terms of `-log (1 - x)`, before restoring the sign. -/
def logOneSubTaylor (x : ℚ) (n : Nat) : ℚ := Taylor.logOneSub x n

/-- `logOneSubTaylor x n` is the sum of the first `n` terms of the series of `-log (1 - x)`. -/
theorem logOneSubTaylor_def (x : ℚ) (n : Nat) :
    logOneSubTaylor x n = ∑ i ∈ Finset.range n, x ^ (i + 1) / ((i + 1 : Nat) : ℚ) :=
  Taylor.logOneSub_eq_sum x n

/-- The Taylor sum for `-log (1 - x)` is its evaluation by binary splitting. -/
theorem logOneSubTaylor_eq_binarySplit : logOneSubTaylor = Taylor.logOneSub := rfl

/--
Absolute logarithm remainder bound on `|x| < 1`: `logOneSubRadius_def` states it as
`|x| ^ (n + 1) / (1 - |x|)`.
-/
def logOneSubRadius (x : ℚ) (n : Nat) : ℚ :=
  Kernel.Q.div (Kernel.Q.pow (Kernel.Q.abs x) (Nat.succ n)) (Kernel.Q.sub 1 (Kernel.Q.abs x))

/-- The logarithm remainder bound, in ordinary notation. -/
theorem logOneSubRadius_def (x : ℚ) (n : Nat) :
    logOneSubRadius x n = |x| ^ (n + 1) / (1 - |x|) := by
  unfold logOneSubRadius
  rw [Kernel.Q.div_eq, Kernel.Q.pow_eq, Kernel.Q.sub_eq, Kernel.Q.abs_eq]

/-- Enclose `log (1 - x)` for `|x| < 1`. -/
def logOneSub (x : ℚ) (degree : Nat) : RationalInterval :=
  around (-logOneSubTaylor x degree) (logOneSubRadius x degree)

/--
Enclose the natural logarithm of a positive rational with its transformed series.

The change of variable maps every positive argument into `(-1, 1)`. Argument reduction before
this kernel is useful when a value is far from one, since the series then converges slowly.
-/
def logSeries (x : ℚ) (degree : Nat) : RationalInterval :=
  let t := Kernel.Q.div (Kernel.Q.sub x 1) (Kernel.Q.add x 1)
  (logOneSub (-t) degree).sub (logOneSub t degree)

/-- The logarithm series in `t = (x - 1) / (x + 1)`, in ordinary notation. -/
theorem logSeries_def (x : ℚ) (degree : Nat) :
    logSeries x degree =
      (logOneSub (-((x - 1) / (x + 1))) degree).sub (logOneSub ((x - 1) / (x + 1)) degree) := by
  change (logOneSub (-(Kernel.Q.div (Kernel.Q.sub x 1) (Kernel.Q.add x 1))) degree).sub
    (logOneSub (Kernel.Q.div (Kernel.Q.sub x 1) (Kernel.Q.add x 1)) degree) = _
  rw [Kernel.Q.div_eq, Kernel.Q.sub_eq, Kernel.Q.add_eq]

/--
Binary logarithm of the integer part, used to reduce arguments at least one (`logScale_def`):
the bit length of the floor, minus one.
-/
def logScale (x : ℚ) : Nat :=
  Nat.sub (Kernel.size (Kernel.Z.toNat (Kernel.Q.floor x))) 1

/-- The log scale is the binary logarithm of the integer part. -/
theorem logScale_def (x : ℚ) : logScale x = (Nat.floor x).log2 := by
  unfold logScale
  rw [Kernel.Q.floor_eq, Kernel.Z.toNat_eq, Int.floor_toNat]
  exact (Kernel.log2_eq_size_sub_one _).symm

/--
Enclose the logarithm after removing an exact power of two from the argument: the enclosure of
`x / 2 ^ scale` plus `scale` times the enclosure of `log 2` (`logLarge_def`). For `scale = 0` the
body returns the series of `x` and computes no `log 2`.
-/
def logLarge (x : ℚ) (degree : Nat) : RationalInterval :=
  let scale := logScale x
  Bool.casesOn (motive := fun _ => RationalInterval) (Nat.beq scale 0)
    ((logSeries (Kernel.Q.divPow2 x scale) degree).add
      ((logSeries 2 degree).scaleNonnegative scale))
    (logSeries x degree)

/-- The reduced logarithm, in ordinary notation and for every scale. -/
theorem logLarge_def (x : ℚ) (degree : Nat) :
    logLarge x degree =
      (logSeries (x / 2 ^ logScale x) degree).add
        ((logSeries 2 degree).scaleNonnegative (logScale x)) := by
  change Bool.casesOn (motive := fun _ => RationalInterval) (Nat.beq (logScale x) 0)
    ((logSeries (Kernel.Q.divPow2 x (logScale x)) degree).add
      ((logSeries 2 degree).scaleNonnegative (logScale x)))
    (logSeries x degree) = _
  rw [Kernel.Q.divPow2_eq]
  cases h : Nat.beq (logScale x) 0 with
  | false => rfl
  | true =>
    have hzero : logScale x = 0 := Nat.eq_of_beq_eq_true h
    change logSeries x degree = _
    simp [hzero, RationalInterval.add, RationalInterval.scaleNonnegative]

/-- Omit the `log 2` enclosure when its coefficient is zero. -/
def logLargeReduced (x : ℚ) (degree : Nat) : RationalInterval :=
  let scale := logScale x
  if scale = 0 then logSeries x degree
  else
    (logSeries (x / 2 ^ scale) degree).add
      ((logSeries 2 degree).scaleNonnegative scale)

/-- Omitting the `log 2` term when its coefficient is zero preserves both endpoints. -/
@[csimp]
theorem logLarge_eq_reduced : logLarge = logLargeReduced := by
  funext x degree
  rw [logLarge_def]
  dsimp only [logLargeReduced]
  split_ifs with h
  · simp [h, RationalInterval.add, RationalInterval.scaleNonnegative]
  · rfl

/--
Enclose the logarithm of a positive rational with binary argument reduction.

Inputs below one are inverted first and the resulting interval is negated. Every series is
therefore evaluated in `[1, 2]`, independently of the original input's exponent.
-/
def log (x : ℚ) (degree : Nat) : RationalInterval :=
  Bool.casesOn (motive := fun _ => RationalInterval) (Kernel.Q.lt x 1)
    (logLarge x degree) ((logLarge (Kernel.Q.inv x) degree).neg)

/-- The logarithm enclosure, in ordinary notation. -/
theorem log_def (x : ℚ) (degree : Nat) :
    log x degree = if x < 1 then (logLarge x⁻¹ degree).neg else logLarge x degree := by
  unfold log
  rw [Kernel.Z.casesOn_eq_ite (Kernel.Q.lt_iff x 1), Kernel.Q.inv_eq]

end FloatLib.Numerics.Enclosure
