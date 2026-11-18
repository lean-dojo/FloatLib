/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.MultiplicativeProof
public import FloatLib.Tactic.Cover
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Checks of the complex kernel layer

Every example is closed by Lean's kernel (`decide +kernel`) or by one of the enclosure theorems
applied to a kernel-checked comparison, which is how the layer is used. The examples cover the
algebra of `CBall` on values worked out by hand, `exp (i t)` against digits of `cos` and `sin`
from an independent source (mpmath, forty digits) for a small, a large and a negative argument,
the two fallbacks of `expISmall`, the table form `expIStep`, a bound on `cos 1` as a real number,
the products, the conjugate and the flag of `CFix`, a sum times a complex number, the pairs and
the cover check of a split, the total over a split, and covers written out by `cover%` with their
theorem. The last section checks that a false statement is refused.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.KernelComplex

open FloatLib.Numerics.Kernel

/-! ### Strict application -/

example : strict 5 (fun n => Nat.add n 1) = 6 ∧ strict 0 (fun n => Nat.mul n 7) = 0 := by
  decide +kernel

/-! ### `CBall`: the algebra on values worked out by hand -/

/-- The ball of radius zero around `a + i b`, for natural numbers. -/
def gauss (a b : Nat) : CBall := ⟨Ball.ofNat a, Ball.ofNat b⟩

-- `(1 + 2 i) (3 + 4 i) = -5 + 10 i`
example : (gauss 1 2).mul (gauss 3 4) = ⟨⟨0, 5, 0, 0⟩, ⟨10, 0, 0, 0⟩⟩ := by decide +kernel
example : (gauss 1 2).add (gauss 3 4) = gauss 4 6 ∧
    (gauss 3 4).sub (gauss 1 2) = gauss 2 2 ∧
    (gauss 1 2).conj = ⟨⟨1, 0, 0, 0⟩, ⟨0, 2, 0, 0⟩⟩ ∧
    (gauss 1 2).neg = ⟨⟨0, 1, 0, 0⟩, ⟨0, 2, 0, 0⟩⟩ := by decide +kernel
-- `i (1 + 2 i) = -2 + i`, and the four powers of `i`
example : (gauss 1 2).mulI = ⟨⟨0, 2, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩ ∧
    CBall.mulIPow 0 (gauss 1 2) = gauss 1 2 ∧
    CBall.mulIPow 1 (gauss 1 2) = (gauss 1 2).mulI ∧
    CBall.mulIPow 2 (gauss 1 2) = (gauss 1 2).neg ∧
    CBall.mulIPow 3 (gauss 1 2) = (gauss 1 2).mulI.mulI.mulI ∧
    CBall.mulIPow 7 (gauss 1 2) = CBall.mulIPow 3 (gauss 1 2) ∧
    CBall.mulIPow 8 (gauss 1 2) = gauss 1 2 := by decide +kernel
-- scaling by a real ball and rounding: `(5/8 ± 1/8) (1 + 2 i)`, then to two binary digits
example : CBall.smul ⟨5, 0, 1, 3⟩ (gauss 1 2) = ⟨⟨5, 0, 1, 3⟩, ⟨10, 0, 2, 3⟩⟩ ∧
    (CBall.smul ⟨5, 0, 1, 3⟩ (gauss 1 2)).round 2 = ⟨⟨2, 0, 1, 2⟩, ⟨5, 0, 2, 2⟩⟩ := by
  decide +kernel
-- a ball around zero, a wider ball, and the bound on all members
example : Ball.widen ⟨5, 0, 1, 3⟩ 1 2 = ⟨5, 0, 3, 3⟩ ∧ Ball.within ⟨5, 0, 1, 3⟩ 0 = true ∧
    Ball.within ⟨5, 0, 1, 3⟩ 1 = false ∧ Ball.within ⟨0, 3, 1, 3⟩ 1 = true := by decide +kernel

/-! ### `exp (i t)` against forty digits of mpmath -/

/-- Whether the dyadic number `(plus - minus) / 2 ^ 66` is a member of the ball. -/
def has (b : Ball) (plus minus : Nat) : Bool :=
  Bool.and (b.lower.le ⟨plus, minus, 66⟩) (Dyad.le ⟨plus, minus, 66⟩ b.upper)

-- `cos 1` and `sin 1`, rounded down to 66 binary digits, are within one unit of members,
-- and the radii are a few units of `2 ^ (-66)`
example : has (CBall.expI (Ball.ofNat 1) CBall.halfPi 0 22 66).re 39867273435138847304 0 = true ∧
    has (CBall.expI (Ball.ofNat 1) CBall.halfPi 0 22 66).im 62089599608814420099 0 = true ∧
    Nat.ble (CBall.expI (Ball.ofNat 1) CBall.halfPi 0 22 66).re.rad 8 = true ∧
    (CBall.expI (Ball.ofNat 1) CBall.halfPi 0 22 66).re.scale = 66 := by decide +kernel
-- `t = 1234.5`: 786 quarter turns are removed
example : has (CBall.expI ⟨2469, 0, 0, 1⟩ CBall.halfPi 0 22 66).re 0 73002885789413946903 = true ∧
    has (CBall.expI ⟨2469, 0, 0, 1⟩ CBall.halfPi 0 22 66).im 10728305418508489960 0 = true := by
  decide +kernel
-- `t = -7.25`: a negative argument
example : has (CBall.expI ⟨0, 29, 0, 2⟩ CBall.halfPi 0 22 66).re 41905407511718513692 0 = true ∧
    has (CBall.expI ⟨0, 29, 0, 2⟩ CBall.halfPi 0 22 66).im 0 60732649308356547127 = true := by
  decide +kernel
-- a ball that is not within `2 ^ (-j)` of zero, and no terms: the square `[-1, 1]²`
example : CBall.expISmall (Ball.ofNat 3) 0 22 66 = CBall.box ∧
    CBall.expISmall ⟨1, 0, 0, 3⟩ 2 0 66 = CBall.box ∧
    CBall.expISmall ⟨1, 0, 0, 1⟩ 2 22 66 = CBall.box := by decide +kernel
-- the series alone, for `t = 1/8` within `2 ^ (-3)`: seven terms give 33 bits
example : has (CBall.expISmall ⟨1, 0, 0, 3⟩ 3 7 66).re 73211265751644270004 0 = true ∧
    has (CBall.expISmall ⟨1, 0, 0, 3⟩ 3 7 66).im 9199371596861069096 0 = true ∧
    Nat.ble (CBall.expISmall ⟨1, 0, 0, 3⟩ 3 7 66).re.rad (2 ^ 33) = true := by
  decide +kernel

/-- A table of `exp (i k / 128)`, computed by `expI`. -/
noncomputable def table (k : Nat) : CBall := CBall.expI ⟨k, 0, 0, 7⟩ CBall.halfPi 0 22 70

-- The computed table satisfies the analytic premise for every index.
example : (CBall.expIStep (Ball.ofNat 1) ⟨1, 0, 0, 7⟩ table 8 7 66).Mem
    (Complex.exp Complex.I) := by
  have hs : (Ball.mk 1 0 0 7).Contains (1 / 128 : ℝ) := by
    rw [Ball.contains_mk]
    norm_num
  have htbl (k : Nat) : (table k).Mem
      (Complex.exp ((((k : ℝ) * (1 / 128) : ℝ) : ℂ) * Complex.I)) := by
    apply CBall.mem_expI CBall.contains_halfPi
    rw [Ball.contains_mk]
    norm_num [div_eq_mul_inv]
  simpa using CBall.mem_expIStep hs htbl (Ball.contains_ofNat (K := ℝ) 1) 8 7 66

-- the table form at `t = 1`: entry 128 times the series at zero
example : has (CBall.expIStep (Ball.ofNat 1) ⟨1, 0, 0, 7⟩ table 8 7 66).re
      39867273435138847304 0 = true ∧
    has (CBall.expIStep (Ball.ofNat 1) ⟨1, 0, 0, 7⟩ table 8 7 66).im
      62089599608814420099 0 = true := by decide +kernel
-- and at `t = -3/8`: the conjugate of entry 48
example : has (CBall.expIStep ⟨0, 3, 0, 3⟩ ⟨1, 0, 0, 7⟩ table 8 7 66).re
      68659343840210207051 0 = true ∧
    has (CBall.expIStep ⟨0, 3, 0, 3⟩ ⟨1, 0, 0, 7⟩ table 8 7 66).im
      0 27026142421122628899 = true := by decide +kernel

/-- A bound on a real number from the theorem and one kernel comparison:
`cos 1 ≤ 39867273435138847312 / 2 ^ 66`. -/
example : Real.cos 1 ≤ 39867273435138847312 / 2 ^ 66 := by
  have hmem := CBall.mem_expI (j := 0) (n := 22) (p := 66) CBall.contains_halfPi
    (Ball.contains_ofNat (K := ℝ) 1)
  have hre : (CBall.expI (Ball.ofNat 1) CBall.halfPi 0 22 66).re.Contains (Real.cos 1) := by
    have := hmem.1
    rwa [show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num, Complex.exp_ofReal_mul_I_re] at this
  have hupper := ((Ball.contains_iff _ _).1 hre).2
  have hle : (CBall.expI (Ball.ofNat 1) CBall.halfPi 0 22 66).re.upper.le
      ⟨39867273435138847312, 0, 66⟩ = true := by decide +kernel
  have hcast := Dyad.le_cast (K := ℝ) hle
  have hvalue : ((Dyad.mk 39867273435138847312 0 66).toRat : ℝ) =
      39867273435138847312 / 2 ^ 66 := by
    rw [Dyad.toRat_mk]
    push_cast
    ring
  rw [hvalue] at hcast
  exact hupper.trans hcast

/-! ### `CFix`: products without signs -/

-- at the scale 4 a part `n` stands for `(n - 32) / 16`: `1 * 1 = 1`, `i * i = -1`
example : CFix.mul 4 (CFix.one 4) (CFix.one 4) = ⟨48, 32, 2, true⟩ ∧
    CFix.mul 4 ⟨32, 48, 0, true⟩ ⟨32, 48, 0, true⟩ = ⟨16, 32, 2, true⟩ := by decide +kernel
-- `(1/2 + i/4) (-3/4 + i) = -5/8 + 5 i/16`, with radii 1/16 and 2/16
example : CFix.mul 4 ⟨40, 36, 1, true⟩ ⟨20, 48, 2, true⟩ = ⟨22, 37, 5, true⟩ := by decide +kernel
-- `(-2) * 2` has no place below `-2`: the flag is false, and stays false
example : (CFix.mul 4 ⟨0, 32, 0, true⟩ ⟨64, 32, 0, true⟩).ok = false ∧
    (CFix.mul 4 (CFix.mul 4 ⟨0, 32, 0, true⟩ ⟨64, 32, 0, true⟩) (CFix.one 4)).ok = false ∧
    (CFix.mul 4 CFix.bad (CFix.one 4)).ok = false := by decide +kernel
-- zero has both parts at the offset, and a product with it has the midpoint zero
example : CFix.zero 4 = ⟨32, 32, 0, true⟩ ∧
    CFix.mul 4 ⟨40, 36, 1, true⟩ (CFix.zero 4) = ⟨32, 32, 2, true⟩ := by decide +kernel
example : (CFix.zero 8).Mem 8 0 := CFix.mem_zero 8
example (s k : Nat) : (CFix.pow2 s k (CFix.one s)).Mem s 1 := by
  simpa using CFix.mem_pow2 k (CFix.mem_one s)
example : CFix.conj 4 ⟨40, 36, 1, true⟩ = ⟨40, 28, 1, true⟩ ∧
    CFix.pow2 4 6 ⟨32, 48, 0, true⟩ = ⟨48, 32, 107178, true⟩ := by decide +kernel
-- a complex ball on the grid: `5/8 ± 1/8` and `-3/4 ± 1/4` at the scale 4
example : CFix.ofCBall 4 ⟨⟨5, 0, 1, 3⟩, ⟨0, 3, 1, 2⟩⟩ = ⟨42, 20, 4, true⟩ ∧
    (CFix.ofCBall 4 ⟨⟨0, 5, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩).ok = false := by decide +kernel
-- Rotation, negation and conversion preserve membership, with a successful output flag.
example :
    (CFix.ofCBall 8 (CBall.ofReal (Ball.ofNat 1)).mulI.neg).ok = true ∧
    (CFix.ofCBall 8 (CBall.ofReal (Ball.ofNat 1)).mulI.neg).Mem 8 (-Complex.I) := by
  refine ⟨by decide +kernel, ?_⟩
  simpa using CFix.mem_ofCBall (s := 8)
    (CBall.mem_neg (CBall.mem_mulI (CBall.mem_ofReal (Ball.contains_ofNat (K := ℝ) 1))))
example : CSum.push ⟨40, 36, 1, true⟩ (CSum.push (CFix.one 4) CSum.zero) = ⟨88, 68, 1, 2, true⟩ ∧
    CSum.add ⟨88, 68, 1, 2, true⟩ ⟨48, 32, 0, 1, false⟩ = ⟨136, 100, 1, 3, false⟩ := by
  decide +kernel

-- a sum times a complex number: `(3/2 + i/4) (1/2 + i/4) = 11/16 + i/2`, and the flags
example : CSum.scale 4 ⟨40, 36, 1, true⟩ ⟨88, 68, 1, 2, true⟩ = ⟨75, 72, 4, 2, true⟩ ∧
    (CSum.scale 4 ⟨40, 36, 1, true⟩ ⟨88, 68, 1, 2, false⟩).ok = false ∧
    (CSum.scale 4 CFix.bad ⟨88, 68, 1, 2, true⟩).ok = false := by decide +kernel

/-! ### Splits and covers -/

/-- The integers up to `6` with the small prime `2`: the products `2` and `4`, and the integers
`1`, `3`, `5` by their factors. The node `2` pairs with `1` and `3`, the node `4` with `1`. -/
def plan6 : Split := .node 2 2 (.node 2 1 .nil .nil) .nil

/-- The factor lists of `1`, `3` and `5`. -/
def rough6 : List (List Nat) := [[], [3], [5]]

example : Split.allPairs rough6 3 plan6 = [1, 3, 5, 2, 6, 4] ∧
    Split.splitOk plan6 rough6 3 6 = true := by decide +kernel
-- another bound, a pair missing and a pair twice fail
example : Split.splitOk plan6 rough6 3 7 = false ∧ Split.splitOk plan6 rough6 3 5 = false ∧
    Split.splitOk plan6 rough6 2 6 = false ∧
    Split.splitOk (.node 2 3 (.node 2 1 .nil .nil) .nil) rough6 3 6 = false := by decide +kernel

/-- The constant one is completely multiplicative: the total counts the six integers. -/
example : Split.total 8 (fun _ => CFix.one 8) rough6 3 plan6 =
    ⟨6 * (3 * 2 ^ 8), 6 * (2 * 2 ^ 8), 12, 6, true⟩ := by decide +kernel

-- the cover of `1, …, 30` with the small primes `2` and `3`
/-- A concrete generated cover, kept in the tests. -/
def thirty : Cover := cover% 30 3

example : thirty.ν = 30 ∧ thirty.count = 10 ∧
    thirty.rough = [[], [5], [7], [11], [13], [17], [19], [23], [5, 5], [29]] ∧
    (Cover.total 8 (fun _ => CFix.one 8) thirty).count = 30 ∧
    (Cover.total 8 (fun _ => CFix.one 8) thirty).ok = true := by decide +kernel
example : (Cover.find 30 [thirty]).isSome = true ∧
    (Cover.find 31 [thirty]).isSome = false := by decide +kernel

/-- A cover for another bound and other small primes, written out and checked where it is used. -/
example : (cover% 100 5).ν = 100 ∧ (cover% 100 5).count = 26 := by decide +kernel

/-- The premises of `Cover.total_contains` are satisfiable: with the constant one, the total of
`thirty` contains `∑ n ∈ [1, 30], 1` and `∑ n ∈ [1, 30], 0`. -/
example : (Cover.total 8 (fun _ => CFix.one 8) thirty).Contains 8
    (∑ _n ∈ Finset.Icc 1 thirty.ν, (1 : ℝ)) (∑ _n ∈ Finset.Icc 1 thirty.ν, (0 : ℝ)) :=
  Cover.total_contains (fr := fun _ => (1 : ℝ)) (fi := fun _ => (0 : ℝ))
    (fun _ _ => by norm_num) ⟨rfl, rfl⟩ (fun _ => CFix.contains_one 8) thirty

/-! ### A false statement is refused -/

/-- The kernel evaluates a wrong value to `false`: the negation is what is proved. -/
example : ¬ ((gauss 1 2).mul (gauss 3 4) = gauss 5 10) := by decide +kernel

/-- A value outside the ball is reported as outside. -/
example : has (CBall.expI (Ball.ofNat 1) CBall.halfPi 0 22 66).re 39867273435138847404 0 =
    false := by decide +kernel

end FloatLibTests.Conformance.Numerics.KernelComplex
