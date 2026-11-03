/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats
public import FloatLib.Numerics.Automation.Interval
meta import FloatLib.Numerics.Automation.Interval

/-!
# Regression checks for representation-independent numerical automation

The examples use the same `numerics` and `numerics_refine` commands across unrelated runtime
carriers. They also check that operation contracts can drive proof-indexed execution without
family-specific wrapper theorems.

This module holds regression tests and adds no automation API of its own. Its deliberately small
examples exercise the public syntax, exact contract discovery, and failure boundaries that users
see, so a change to metaprogramming support cannot silently become tied to one float family.
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

-- Exact rational endpoints must survive a successful weak endpoint check.
example (x : ℝ) (hx : x ∈ Set.Icc 0 (1 / 3 : ℝ)) : x ≤ 1 / 3 := by interval

example (x : ℝ) (hx : x ∈ Set.Icc 0 (1 / 3 : ℝ)) : x + 1 ≤ 4 / 3 := by interval

example (x : ℝ) (hx : x ∈ Set.Icc (1 / 3 : ℝ) 1) : 1 / 3 ≤ x := by interval

-- A touching endpoint supplies no strict margin.
example (x : ℝ) (_hx : x ∈ Set.Icc 0 (1 / 3 : ℝ)) : True := by
  fail_if_success have : x < 1 / 3 := by interval (maxHeartbeats := 100)
  trivial

/-! ## Stable `grind` contracts -/

/--
The public binary carrier/model equivalence is available to generic proof automation without
exposing the selected `UInt32` storage representation.
-/
example (value : FloatLib.Floats.Binary32) :
    FloatLib.Floats.ExecFloat.Binary.ofModel
        (FloatLib.Floats.ExecFloat.Binary.toModel value) =
      value := by
  grind

/--
The configured posit carrier/model equivalence has the same automation contract as configured
binary values.
-/
example (value : FloatLib.Floats.Posit32) :
    FloatLib.Floats.ExecFloat.Posit.ofModel
        (FloatLib.Floats.ExecFloat.Posit.toModel value) =
      value := by
  grind

/-- Posit successor and predecessor laws can close without unfolding packed storage. -/
example (value : FloatLib.Floats.Posit32) :
    FloatLib.Floats.ExecFloat.Posit.prior
        (FloatLib.Floats.ExecFloat.Posit.next value) =
      value := by
  grind

/-- Automation retains the Posit Standard's distinguished NaR behavior. -/
example :
    FloatLib.Floats.ExecFloat.Posit.floor
        (FloatLib.Floats.ExecFloat.Posit.nar : FloatLib.Floats.Posit32) =
      (FloatLib.Floats.ExecFloat.Posit.nar : FloatLib.Floats.Posit32) := by
  grind

/-- Converting posit zero to its associated quire preserves the distinguished zero value. -/
example :
    FloatLib.Floats.ExecFloat.Posit.Quire.pToQ
        (FloatLib.Floats.ExecFloat.Posit.zero : FloatLib.Floats.Posit32) =
      (FloatLib.Floats.ExecFloat.Posit.Quire.zero : FloatLib.Floats.Quire32) := by
  grind

/-- The exact rational view is preserved when a configured posit enters its quire. -/
example (value : FloatLib.Floats.Posit32) :
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

open Lean Elab Tactic Meta in
/--
`check_interval_failure (goal) "expected" "forbidden" (options)` runs `interval` with the given
options on `goal` in the current context. It must fail with a message that contains `expected` and
does not contain `forbidden`; the proof state is left as it was.
-/
syntax (name := checkIntervalFailure)
  "check_interval_failure " term:max str str (ppSpace "(" ident " := " num ")")* : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| check_interval_failure $goal:term $expected:str $forbidden:str
      $[($option:ident := $value:num)]*) => withMainContext do
    let saved ← saveState
    let mvar ← mkFreshExprMVar (← elabTerm goal (some (mkSort .zero)))
    let message ← try
      discard <| Tactic.run mvar.mvarId!
        (evalTactic (← `(tactic| interval $[($option:ident := $value:num)]*)))
      pure "unexpected interval success"
    catch error =>
      pure (← error.toMessageData.toString)
    saved.restore
    unless message.contains expected.getString do
      throwError "the interval failure does not say {expected.getString}: {message}"
    if message.contains forbidden.getString then
      throwError "the interval failure says {forbidden.getString}: {message}"

#allow_unused_tactic checkIntervalFailure

-- The tactic keeps its own finite kernel budget when the surrounding declaration disables limits.
-- The goal is true, so a budget of 1 heartbeat fails only because kernel verification runs out,
-- and the message says so. Failure restores the goal so its ordinary proof can still close it.
set_option maxHeartbeats 0 in
example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : x * (1 - x) ≤ 1 / 3 := by
  check_interval_failure (x * (1 - x) ≤ 1 / 3)
    "Kernel verification of the binary-grid attempt ran out of the interval budget of 1 heartbeats"
    "does not establish" (precision := 32) (depth := 4) (maxHeartbeats := 1)
  interval (precision := 32) (depth := 4)

-- With 1 heartbeat the kernel also runs out on the exact-rational attempt, which alone can prove
-- this bound. The binary-grid attempt fails on its merits, since its endpoints cannot equal 1/3,
-- so the advice names only the exact-rational attempt.
example (x : ℝ) (_hx : x ∈ Set.Icc 0 (1 / 3 : ℝ)) : True := by
  check_interval_failure (x ≤ 1 / 3)
    "Kernel verification of the exact-rational attempt ran out of the interval budget of 1 \
      heartbeats" "binary-grid attempt" (maxHeartbeats := 1)
  trivial

-- A false goal, or an enclosure outside a registered function's accepted domain, is not a
-- resource problem, so the failure gives no heartbeat advice. The quadratic peaks at 1/4, and
-- `x ≤ x` fails only because `x - x` is enclosed by a box-wide interval at every depth. An
-- argument that is itself a registered call is shown by its enclosure alone.
example (x : ℝ) (_hx : x ∈ Set.Icc 0 1) : True := by
  check_interval_failure (x ≤ x) "does not establish" "maxHeartbeats" (depth := 64)
  check_interval_failure (x * (1 - x) ≤ 1 / 5) "does not establish" "maxHeartbeats"
  check_interval_failure (Real.exp x < 2) "does not establish" "maxHeartbeats"
  check_interval_failure (Real.log x ≤ 1)
    "accepts only argument enclosures with a positive lower endpoint" "maxHeartbeats"
  check_interval_failure (Real.log (Real.sin x) ≤ 1)
    "the Real.log enclosure rejected its argument in [" "argument argument"
  trivial

-- The initial enclosure is too wide, so subdivision must preserve the original variable bounds.
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

/-! ## Real powers, base logarithms, and inverse hyperbolic functions -/

-- The exponent is a real variable, and negative exponents are included in the same enclosure.
example (x y : ℝ) (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc (-2) 2) :
    x ^ y < 5 := by
  interval (depth := 0)

-- Explicit function application follows the same path as power notation.
example (x y : ℝ) (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc (-2) 2) :
    Real.rpow x y < 5 := by
  interval (depth := 0)

example (x y : ℝ) (hx : x ∈ Set.Icc (1 / 4) (1 / 2))
    (hy : y ∈ Set.Icc (-2) (-1)) : x ^ y < 17 := by
  interval (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc 1 2) : x ^ (0 : ℝ) ≤ 1 := by
  interval (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc 1 2) : x ^ (1 / 2 : ℝ) < 3 / 2 := by
  interval (precision := 128) (degree := 24) (depth := 0)

-- A base below one reverses the sign of the logarithm, and the base may also vary.
example (x : ℝ) (hx : x ∈ Set.Icc 1 2) : Real.logb 2 x < 11 / 10 := by
  interval (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc 1 100) : Real.logb 10 x < 21 / 10 := by
  interval (degree := 24) (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc 2 4) : Real.logb (1 / 2) x < -9 / 10 := by
  interval (depth := 0)

example (b x : ℝ) (hb : b ∈ Set.Icc 2 3) (hx : x ∈ Set.Icc 4 8) :
    Real.logb b x < 31 / 10 := by
  interval (depth := 0)

-- Variable bases below one and bases close to one use the general logb enclosure.
example (b x : ℝ) (hb : b ∈ Set.Icc (1 / 4) (1 / 2)) (hx : x ∈ Set.Icc 2 3) :
    Real.logb b x < -2 / 5 := by
  interval (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc 1 (1001 / 1000)) :
    Real.logb (1001 / 1000) x < 11 / 10 := by
  interval (precision := 128) (degree := 24) (depth := 0)

-- A narrow numerical target exercises approximation degree as well as endpoint precision.
example : Real.logb 2 (3 / 2) < (10790653543520307106 : ℝ) / 2 ^ 64 := by
  interval (precision := 64) (degree := 88) (depth := 0)

-- Monotonicity and odd symmetry preserve tight bounds across zero.
example (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) : |Real.arsinh x| < 1 := by
  interval (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc (-1) (-1 / 2)) : Real.arsinh x < -2 / 5 := by
  interval (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc (-100) (-10)) : Real.arsinh x < 0 := by
  interval (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc (-100) 100) : |Real.arsinh x| < 6 := by
  interval (depth := 0)

example (x : ℝ) (hx : x = 0) : Real.arsinh x ≤ 0 := by
  interval (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc 1 2) : Real.arcosh x < 7 / 5 := by
  interval (depth := 0)

example (x : ℝ) (hx : x = 1) : Real.arcosh x ≤ 0 := by
  interval (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc (-1 / 2) (1 / 2)) : |Real.artanh x| < 3 / 5 := by
  interval (depth := 0)

-- Reification and equality reconstruction also work through local definitions.
example (x y : ℝ) (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc (-1) 1) :
    x ^ y + Real.logb 2 x < 4 := by
  let power := x ^ y
  let logarithm := Real.logb 2 x
  change power + logarithm < 4
  interval (depth := 0)

-- False goals and rejected real-power domains must never produce proofs.
example (x : ℝ) (_hx : x ∈ Set.Icc 0 2) : True := by
  fail_if_success have : x ^ (1 / 2 : ℝ) < 2 := by interval (depth := 2)
  fail_if_success have : Real.logb 2 x < 2 := by interval (depth := 2)
  trivial

example (x : ℝ) (_hx : x ∈ Set.Icc (-2) (-1)) : True := by
  fail_if_success have : x ^ (1 / 2 : ℝ) < 2 := by interval (depth := 2)
  fail_if_success have : Real.arcosh x < 2 := by interval (depth := 2)
  trivial

example (b x : ℝ) (_hb : b ∈ Set.Icc (1 / 2) 2) (_hx : x ∈ Set.Icc 2 3) : True := by
  fail_if_success have : Real.logb b x < 10 := by interval (depth := 2)
  trivial

example (x : ℝ) (_hx : x ∈ Set.Icc (-1) 1) : True := by
  fail_if_success have : Real.artanh x < 10 := by interval (depth := 2)
  trivial

example (x y : ℝ) (_hx : x ∈ Set.Icc 1 2) (_hy : y ∈ Set.Icc 1 2) : True := by
  fail_if_success have : x ^ y < 1 := by interval (depth := 2)
  fail_if_success have : Real.logb 2 x < 0 := by interval (depth := 2)
  trivial

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

-- Nonnegative-real inputs need only an upper bound; stronger explicit lower bounds still apply.
example (x : NNReal) (hx : x ≤ 1) : x * x ≤ 1 := by
  interval

example (x : NNReal) (hx : x < 1) : x < 2 := by
  interval

example (x : NNReal) (hlo : 1 ≤ x) (hhi : x ≤ 2) : 1 ≤ x := by
  interval

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

-- The operator norm is the largest absolute row sum, which differs from the elementwise maximum.
example (A : Matrix (Fin 2) (Fin 3) ℝ) (hA : ∀ i j, A i j ∈ Set.Icc (-1) 1) :
    ‖A‖ ≤ 3 := by
  fail_if_success have : ‖A‖ ≤ 1 := by interval (depth := 0)
  interval (depth := 0)

end

/-! ## Failure diagnostics -/

section Diagnostics
open Lean Meta Qq Interval Interval.Tactic

/--
info: interval could not certify: the enclosure of (x[0] - (1/2)) is [-1, 1]; its upper endpoint does not establish ≤ 0.
Box: x[0] in [0, 1/4]. Subdivision depth 0 exhausted after 0 splits on this branch.
A diagnostic retry passes on this box with precision := 16; retry the tactic with that setting.
-/
#guard_msgs in
#eval show MetaM Unit from do
  logInfo (← diagnoseFailure q(Interval.Expr.binary .sub (.var 0) (.const (1 / 2)))
    q(([⟨0, 1 / 4⟩] : Box)) q((⟨0, 16⟩ : Backend.Config)) q(Relation.nonpositive) q(0))

-- An algebraic failure that a larger precision does not fix gets no retry hint: the Taylor
-- degree is never probed, since the binary-grid backend reads it only for elementary functions.
/--
info: interval could not certify: the enclosure of ((x[0] * x[0]) - (1/2)) is [-1/4, 1/16]; its upper endpoint does not establish < 0.
Box: x[0] in [1/2, 3/4]. Subdivision depth 2 exhausted after 2 splits on this branch.
Try tighter input bounds or more subdivision depth.
-/
#guard_msgs in
#eval show MetaM Unit from do
  logInfo (← diagnoseFailure
    q(Interval.Expr.binary .sub (.binary .mul (.var 0) (.var 0)) (.const (1 / 2)))
    q(([⟨0, 1⟩] : Box)) q((⟨64, 16⟩ : Backend.Config)) q(Relation.negative) q(2))

/-- A strict relation reached through an abbreviation rather than the literal constructor. -/
abbrev strictRelation : Relation := .negative

-- A registered-function diagnosis reduces the relation, so a strict goal whose enclosure only
-- reaches `0` is reported as a failure, not as a heartbeat problem.
/--
info: interval could not certify: on the original box, the expression is enclosed by [-1, 0]; its upper endpoint does not establish < 0.
Box: x[0] in [-1, 0]. Verification used subdivision depth 8. Try tighter input bounds, more subdivision, or higher approximation settings.
-/
#guard_msgs in
#eval show MetaM Unit from do
  logInfo (← diagnoseRegisteredFailure q(Interval.Expr.var 0) q(Backend.binaryGrid {})
    q(([⟨-1, 0⟩] : Box)) q(({} : Backend.Config)) q(strictRelation) q(8))

-- A registered call outside its enclosure's accepted domain is named, with the argument enclosure
-- and the domain its registration states, rather than a request to raise a budget.
/--
info: interval could not certify: on the original box, the Real.log enclosure rejected its argument x[0] in [0, 1]. It accepts only argument enclosures with a positive lower endpoint.
Box: x[0] in [0, 1].
-/
#guard_msgs in
#eval show MetaM Unit from do
  logInfo (← diagnoseRegisteredFailure q(Interval.Expr.call 0 [.var 0])
    q(Backend.withExtensions (Backend.binaryGrid {}) {} [Backend.elementaryExtension .log])
    q(([⟨0, 1⟩] : Box)) q(({} : Backend.Config)) q(Relation.nonpositive) q(8)
    (calls := #[{ function := ``Real.log
                  acceptedDomain? := Interval.acceptedDomain? ``Interval.log_extension_sound }]))

-- An argument that is itself a registered call has no algebraic source text, so the message names
-- its position, when there are several, and its enclosure.
/--
info: interval could not certify: on the original box, the Real.rpow enclosure rejected its first argument x[0] in [-1, 1] and its second argument in [-379531823822684255/18446744073709551616, 9033606124943433681/9223372036854775808]. It accepts only base enclosures with a positive lower endpoint.
Box: x[0] in [-1, 1], x[1] in [0, 1].
-/
#guard_msgs in
#eval show MetaM Unit from do
  logInfo (← diagnoseRegisteredFailure q(Interval.Expr.call 0 [.var 0, .call 1 [.var 1] ])
    q(Backend.withExtensions (Backend.binaryGrid {}) {}
      [Backend.rpowExtension, Backend.elementaryExtension .sin])
    q(([⟨-1, 1⟩, ⟨0, 1⟩] : Box)) q(({} : Backend.Config)) q(Relation.nonpositive) q(8)
    (calls := #[{ function := ``Real.rpow
                  acceptedDomain? := Interval.acceptedDomain? ``Interval.rpow_extension_sound },
                { function := ``Real.sin }]))

end Diagnostics

end FloatLibTests.Conformance.Numerics.Automation
