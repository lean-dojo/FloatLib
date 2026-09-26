/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats
public import FloatLib.Numerics.Automation.Interval

/-!
# Regression checks for representation-independent numerical automation

The examples use the same `numerics` and `numerics_refine` commands across unrelated runtime
carriers. They also ensure operation contracts can drive proof-indexed execution directly without
family-specific wrapper theorems.

This is a regression module rather than a second automation API. Its deliberately small examples
exercise the public syntax, exact contract discovery, and failure boundaries that users see, so a
change to metaprogramming support cannot silently become tied to one float family.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.Automation

open FloatLib.Numerics
open FloatLib.Floats.Formats

example {radix : Radix} {fractionalDigits : Nat} {a b : ℚ}
    (x : FixedPoint.AtFinite radix fractionalDigits a)
    (y : FixedPoint.AtFinite radix fractionalDigits b) :
    FixedPoint.AtFinite radix fractionalDigits (a + b) :=
  numerics_refine (FixedPoint.Code.add x.1 y.1)

example {radix : Radix} {p q : Nat} {a b : ℚ}
    (x : FixedPoint.AtFinite radix p a)
    (y : FixedPoint.AtFinite radix q b) :
    FixedPoint.AtFinite radix (p + q) (a * b) :=
  numerics_refine (FixedPoint.Code.mul x.1 y.1)

example {radix : Radix} {a b : ℝ}
    (x : Logarithmic.AtFinite radix a)
    (y : Logarithmic.AtFinite radix b) :
    Logarithmic.AtFinite radix (a * b) :=
  numerics_refine (Logarithmic.Code.mul x.1 y.1)

example {a b : ℤ}
    (x : Codebook.AtFinite Codebook.Catalog.bipolar1 a)
    (y : Codebook.AtFinite Codebook.Catalog.bipolar1 b) :
    Codebook.AtFinite Codebook.Catalog.bipolar1 (a * b) :=
  numerics_refine (Codebook.Catalog.bipolar1.mul x.1 y.1)

example {a b : ℤ}
    (x : Codebook.AtFinite Codebook.Catalog.ternary2 a)
    (y : Codebook.AtFinite Codebook.Catalog.ternary2 b) :
    Codebook.At Codebook.Catalog.ternary2 (.finite (a * b)) :=
  Operation.Checked2.applyAt Codebook.Catalog.ternary2.mul_refines x y

example :
    FixedPoint.Code.toRat
      ({ coefficient := 125 } : FixedPoint.Code decimalRadix 2) = 5 / 4 := by
  numerics

example :
    Logarithmic.Code.mul
      (.value false 3 : Logarithmic.Code binaryRadix)
      (.value true 2) = .value true 5 := by
  numerics

example :
    Codebook.AtFinite Codebook.Catalog.bipolar1 1 :=
  numerics_refine (Codebook.Catalog.bipolar1.ofNatBits 1)

example :
    Codebook.At Codebook.Catalog.ternary2
      (.exceptional (.reserved (some 3))) :=
  numerics_refine (Codebook.Catalog.ternary2.ofNatBits 3)

example {radix : Radix} {value : ℝ} (x : Flocq.FloatRep.AtFinite radix value) :
    Flocq.FloatRep.AtFinite radix (-value) :=
  numerics_refine (Flocq.FloatRep.negExact x.1)

example {radix : Radix} {left right : ℝ}
    (x : Flocq.FloatRep.AtFinite radix left)
    (y : Flocq.FloatRep.AtFinite radix right) :
    Flocq.FloatRep.AtFinite radix (left * right) :=
  numerics_refine (Flocq.FloatRep.mulExact x.1 y.1)

example :
    Flocq.FloatRep.negExact
        ({ mantissa := 7, exponent := -3 } : Flocq.FloatRep decimalRadix) =
      { mantissa := -7, exponent := -3 } := by
  numerics

example :
    Flocq.FloatRep.mulExact
        ({ mantissa := -3, exponent := 4 } : Flocq.FloatRep binaryRadix)
        { mantissa := 5, exponent := -2 } =
      { mantissa := -15, exponent := 2 } := by
  numerics

/-! ## Stable `grind` contracts -/

abbrev Binary32 :=
  FloatLib.Floats.ExecFloat.Binary
    (exponentBits := 8) (fractionBits := 23)

abbrev Posit32 := FloatLib.Floats.ExecFloat.Posit (bits := 32)

abbrev Posit32Quire :=
  FloatLib.Floats.ExecFloat.Posit.Quire (bits := 32)

/--
The public binary carrier/model equivalence is available to generic proof automation without
exposing the selected `UInt32` storage representation.
-/
example (value : Binary32) :
    FloatLib.Floats.ExecFloat.Binary.ofModel
        (FloatLib.Floats.ExecFloat.Binary.toModel value) =
      value := by
  grind

/--
The configured posit carrier/model equivalence has the same automation contract as configured
binary values.
-/
example (value : Posit32) :
    FloatLib.Floats.ExecFloat.Posit.ofModel
        (FloatLib.Floats.ExecFloat.Posit.toModel value) =
      value := by
  grind

/-- Posit successor and predecessor laws can close without unfolding packed storage. -/
example (value : Posit32) :
    FloatLib.Floats.ExecFloat.Posit.prior
        (FloatLib.Floats.ExecFloat.Posit.next value) =
      value := by
  grind

/-- Automation retains the Posit Standard's distinguished NaR behavior. -/
example :
    FloatLib.Floats.ExecFloat.Posit.floor
        (FloatLib.Floats.ExecFloat.Posit.nar : Posit32) =
      (FloatLib.Floats.ExecFloat.Posit.nar : Posit32) := by
  grind

/-- Converting posit zero to its associated quire preserves the distinguished zero value. -/
example :
    FloatLib.Floats.ExecFloat.Posit.Quire.pToQ
        (FloatLib.Floats.ExecFloat.Posit.zero : Posit32) =
      (FloatLib.Floats.ExecFloat.Posit.Quire.zero : Posit32Quire) := by
  grind

/-- The exact rational view is preserved when a configured posit enters its quire. -/
example (value : Posit32) :
    FloatLib.Floats.ExecFloat.Posit.Quire.toRat?
        (FloatLib.Floats.ExecFloat.Posit.Quire.pToQ value) =
      FloatLib.Floats.ExecFloat.Posit.toRat? value := by
  grind

/--
Backend refinement rules are available to automation without making optimized kernels global
`simp` rewrites.
-/
example
    {format : BinaryInterchange.FloatFormat}
    {plan : BinaryInterchange.Configured.StoragePlan format}
    {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan
      (BinaryInterchange.Model format) code]
    (left right : FloatLib.Floats.ExecFloat
      (BinaryInterchange.Configured.Family format code plan)) :
    BinaryInterchange.Configured.Backend.genericAdd left right =
      BinaryInterchange.Configured.Spec.add left right := by
  grind

/-! ## Real inequalities by certified interval evaluation -/

-- The initial enclosure is too wide; subdivision must preserve the original variable bounds.
example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : x * (1 - x) ≤ 1 / 3 := by
  fail_if_success interval (depth := 0)
  interval (precision := 32) (depth := 4)

-- Powers and two variables pass through the same reifier.
example (x y : ℝ) (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc 2 3) :
    |x| ^ 3 / y ≤ 1 / 2 := by
  interval

example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : Real.exp x * Real.cos x < 3 := by
  interval (degree := 12)

example (x : ℝ) (hx : x ∈ Set.Icc 1 2) : Real.log x + Real.sqrt x < 5 / 2 := by
  interval (degree := 12)

-- Zero degree and precision still support exact algebraic bounds.
example (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) : x ^ 2 ≤ 1 := by
  interval (precision := 0) (degree := 0) (depth := 0)

-- A successful left child is insufficient, and the shared midpoint cannot be dropped.
example (x : ℝ) (_hx : x ∈ Set.Icc 0 1) : True := by
  fail_if_success have : x ≤ 1 / 2 := by interval (depth := 1)
  fail_if_success have : 0 < (x - 1 / 2) ^ 2 := by interval (depth := 2)
  trivial

-- Local definitions of rational bounds are constants, not additional interval variables.
example (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 2) : x ≤ 2 := by
  let two : ℝ := 2
  change 0 ≤ x ∧ x ≤ two at hx
  interval (depth := 0)

-- Failures leave the goal unchanged. `1 / x ≤ 2` and `x < 0` are false on `[-1, 1]`. The `log`
-- and `sqrt` bounds are true in Lean, where `Real.log x = Real.log |x|` and `Real.sqrt` of a
-- negative number is `0`, but the enclosure rejects them because `x` may leave the domain.
example (x : ℝ) (_hx : x ∈ Set.Icc (-1) 1) : True := by
  fail_if_success have : 1 / x ≤ 2 := by interval (depth := 2)
  fail_if_success have : Real.log x < 1 := by interval (depth := 2)
  fail_if_success have : Real.sqrt x < 2 := by interval (depth := 2)
  fail_if_success have : x < 0 := by interval (depth := 2)
  trivial

example (x : ℝ) : x = x := by
  fail_if_success have : x ≤ 2 := by interval
  rfl

/-! ## Finite sums and matrix bounds -/

open scoped BigOperators Matrix.Norms.Elementwise

local macro "test_interval_options" : tactic =>
  `(tactic| interval (precision := 32) (depth := 0))

example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : x ^ 2 ≤ 1 := by
  test_interval_options

example (x : Fin 4 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (-1) 1) :
    ∑ i, (x i) ^ 2 ≤ 4 := by
  interval (depth := 0)

example (x : ℕ → ℝ) (hx : ∀ i ∈ ({2, 5, 9} : Finset ℕ), x i ∈ Set.Icc 0 1) :
    ∑ i ∈ ({2, 5, 9} : Finset ℕ), x i ≤ 3 := by
  interval (depth := 0)

example (x : ℕ → ℝ) (hx : ∀ i ∈ Finset.range 3, x i ∈ Set.Icc 0 1) :
    ∑ i ∈ Finset.range 3, x i ≤ 3 := by
  interval (depth := 0)

-- A pointwise hypothesis cannot supply bounds beyond its index set.
example (x : ℕ → ℝ) (_hx : ∀ i ∈ Finset.range 2, x i ∈ Set.Icc 0 1) : True := by
  fail_if_success have : ∑ i ∈ Finset.range 3, x i ≤ 3 := by interval (depth := 0)
  trivial

example (x : Fin 3 → ℝ) (y : ℝ)
    (h : y ∈ Set.Icc 0 1 ∧ ∀ i, x i ∈ Set.Icc 0 1) :
    y + dotProduct x x ≤ 4 := by
  interval (depth := 0)

-- Congruence follows local definitions as well as literal arithmetic applications.
example (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) : |x| ^ 2 + 1 ≤ 2 := by
  let square := |x| ^ 2
  change square + 1 ≤ 2
  interval (depth := 0)

example (A : Matrix (Fin 2) (Fin 3) ℝ) (x : Fin 3 → ℝ)
    (hA : ∀ i j, A i j ∈ Set.Icc (-1) 1) (hx : ∀ i, x i ∈ Set.Icc (-1) 1) :
    ‖WithLp.toLp 1 (A.mulVec x)‖₊ ≤ (6 : NNReal) := by
  interval (depth := 0)

example (A : Matrix (Fin 2) (Fin 3) ℝ) (B : Matrix (Fin 3) (Fin 2) ℝ)
    (hA : ∀ i j, A i j ∈ Set.Icc (-1) 1) (hB : ∀ i j, B i j ∈ Set.Icc (-1) 1) :
    ‖A * B‖ ≤ 3 := by
  interval (depth := 0)

section
open scoped Matrix.Norms.Operator

-- The operator norm sums a row; it is not the elementwise maximum.
example (A : Matrix (Fin 2) (Fin 3) ℝ) (hA : ∀ i j, A i j ∈ Set.Icc (-1) 1) :
    ‖A‖ ≤ 3 := by
  fail_if_success have : ‖A‖ ≤ 1 := by interval (depth := 0)
  interval (depth := 0)

end

end FloatLibTests.Conformance.Numerics.Automation
