/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.Interval.Constraints
meta import FloatLib.Tactic.Interval.Constraints

/-!
# Constraint sets refuted by `interval`

Each example is one instance of what the constraint route of `interval` does, and says so. The
sections follow the route: the shapes of goals and constraints it reads, the functions it
evaluates, coordinates of several types, the points and sets where a margin vanishes, sets
without a box, ranges with infinite ends, existential statements, comparisons whose sides meet
at an end of the range, the hints, the failures with their messages, and the trace. The last
section checks the certificate checker itself on certificates written by hand, and the
evaluation on ranges.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.Constraints

open FloatLib.Numerics FloatLib.Numerics.Interval

/-! ## Goals and connectives -/

/-- `False` from hypotheses: a disc and a half-plane that do not meet. -/
example (x y : ℝ) (hx : -2 ≤ x) (hx' : x ≤ 2) (hy : -2 ≤ y) (hy' : y ≤ 2)
    (h1 : x ^ 2 + y ^ 2 ≤ 1) (h2 : x + y ≥ 3 / 2) : False := by
  interval

/-- A negated existential, with the box inside the statement. -/
example : ¬ ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ x * (1 - x) > 13 / 50 := by
  interval

/-- Binders and an implication to `False`. -/
example : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → Real.exp (x * y) > 3 → False := by
  interval

/-- A goal that is not an inequality is proved by refuting its negation: a membership. -/
example (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2) : x ^ 2 ∈ Set.Icc (1 : ℝ) 4 := by
  interval

/-- An equality at a point. -/
example (x : ℝ) (hx : x = 2) : x + x = 4 := by
  interval

/-- A conjunction with a disjunction: every part of the negation is refuted on its boxes. -/
example (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    x * y ≤ 1 ∧ (Real.sin x ≤ 9 / 10 ∨ 1 / 2 ≤ y ∨ y < 3 / 5) := by
  interval

/-- Negations and an implication among the hypotheses. -/
example (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1)
    (h1 : ¬ (x + y < 8 / 5)) (h2 : x < 9 / 10 → y ≤ 1 / 4) (h3 : ¬ (x ≥ 4 / 5 ∧ y ≥ 1 / 2)) :
    False := by
  interval

/-- A goal with `≠`. -/
example (x : ℝ) (hx : 1 ≤ x ∧ x ≤ 2) : x ^ 2 ≠ 5 := by
  interval

/-- A disjunction of boxes: the bounds of each case are constraints like any other. -/
example (x : ℝ) (h : (0 ≤ x ∧ x ≤ 1) ∨ (2 ≤ x ∧ x ≤ 3)) (hx : -1 ≤ x) (hx' : x ≤ 4)
    (h' : (x - 3 / 2) ^ 2 < 1 / 5) : False := by
  interval

/-- Implications among the hypotheses are cases: here four, of which two pin a variable. -/
example (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (h : x ≤ 1 / 2 → y ≤ 1 / 2)
    (h' : x > 1 / 2 → y ≥ 1 / 2) : (x - 1 / 2) * (y - 1 / 2) ≥ 0 := by
  interval

/-- An inclusion of sets is unfolded to its points. -/
example : {x : ℝ | 0 ≤ x ∧ x ≤ 1} ⊆ {x : ℝ | x ^ 2 ≤ 1} := by
  interval

/-- A local definition stays a variable, with its equation: the bound is attained at
`y = 1 / 2`, a rational point, where it would be attained at an irrational `x`. -/
example (x : ℝ) : let y := x ^ 2; y * (1 - y) ≤ 1 / 4 := by
  interval

/-- An equivalence is a disjunction of two conjunctions. -/
example (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 2) : x ^ 2 ≤ 1 ↔ x ≤ 1 := by
  interval

/-- A named set is unfolded, and a hypothesis that is no constraint is ignored. -/
def disc : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

example (p : ℝ × ℝ) (n : ℕ) (_hn : 2 ≤ n) (hp : p ∈ disc) (h1 : -1 ≤ p.1 ∧ p.1 ≤ 1)
    (h2 : -1 ≤ p.2 ∧ p.2 ≤ 1) (h : p.1 * p.2 > 3 / 5) : False := by
  interval

/-! ## Functions -/

/-- Exponential, logarithm, square root and division. -/
example (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2)
    (h : Real.log x / x > 2 / 5 ∨ Real.sqrt x * Real.exp (-x) > 2 / 5) : False := by
  interval

/-- Trigonometric functions, the hyperbolic tangent, the arctangent and `π`. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2)
    (h : Real.sin x + Real.cos x > 3 / 2 ∨ Real.tanh x > 19 / 20 ∨ Real.arctan x > 11 / 10) :
    False := by
  interval

/-! ## Coordinates -/

/-- A state vector `Fin n → ℝ`. -/
example : ¬ ∃ x : Fin 3 → ℝ, (∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) ∧
    x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≥ 7 / 2 := by
  interval

/-- A constraint for every coordinate of a vector is read for each of them. -/
example (x : Fin 2 → ℝ) (h : ∀ i, |x i| ≤ 1) : x 0 * x 1 ≤ 1 := by
  interval

/-- A structure. -/
structure Pendulum where
  /-- The angle. -/
  angle : ℝ
  /-- The angular velocity. -/
  velocity : ℝ

example (s : Pendulum) (ha : -1 ≤ s.angle ∧ s.angle ≤ 1) (hv : -1 ≤ s.velocity ∧ s.velocity ≤ 1)
    (h : (1 - Real.cos s.angle) + s.velocity ^ 2 / 2 > 1) : False := by
  interval

/-- Definitions are unfolded where their value has no bound of its own: a map and an energy. -/
noncomputable def step (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![x 0 + 1 / 100 * x 1, x 1 - 1 / 100 * Real.sin (x 0)]

/-- The energy of a state. -/
noncomputable def energy (x : Fin 2 → ℝ) : ℝ := 1 - x 0 ^ 2 - x 1 ^ 2

example : ¬ ∃ x : Fin 2 → ℝ, (x 0 ≥ -1 / 2 ∧ x 0 ≤ 1 / 2 ∧ x 1 ≥ -1 / 2 ∧ x 1 ≤ 1 / 2) ∧
    energy x ≥ 0 ∧ energy (step x) < 2 / 5 := by
  interval

/-! ## Zero margin

A comparison that holds with equality at a point of the box is never separated from zero by
intervals. Its quadratic form decides it there.
-/

/-- An equilibrium: the derivative of a Lyapunov function is negative except at the origin. -/
theorem equilibrium (x y : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : -1 ≤ y) (hy' : y ≤ 1)
    (h0 : x ^ 2 + y ^ 2 > 0)
    (h : 2 * x * (-x + y / 2 - x * y ^ 2 / 10) + 2 * y * (-x / 2 - y) ≥ 0) : False := by
  interval

/-- The matrix of the form depends on the point: an exponential on the diagonal. -/
theorem weighted (x y : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : -1 ≤ y) (hy' : y ≤ 1)
    (h0 : x ^ 2 + y ^ 2 > 0) (h : x ^ 2 * Real.exp (2 * y) + y ^ 2 ≤ 0) : False := by
  interval

/-- A point that is not the origin. -/
theorem shifted (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 2) (hy : 0 ≤ y) (hy' : y ≤ 2)
    (h0 : (x - 1) ^ 2 + (y - 1 / 2) ^ 2 > 0)
    (h : (x - 1) ^ 2 + 3 * (y - 1 / 2) ^ 2 + (x - 1) * (y - 1 / 2) ≤ 0) : False := by
  interval

/-- A strict comparison that fails with equality on a whole line: a semidefinite form. -/
theorem semidefinite (x y : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : -1 ≤ y) (hy' : y ≤ 1)
    (h : 5 * x ^ 2 + y ^ 2 < x ^ 2 + y ^ 2) : False := by
  interval

/-- Three dimensions, with a cross term. -/
theorem three (x : Fin 3 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1)
    (h0 : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 > 0)
    (h : 2 * x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 + 3 * x 2 ^ 2 * (1 + x 0 ^ 2) ≤ 0) : False := by
  interval

/-- A sum of nonnegative terms that is at most zero: each term is zero, which pins `x` and `y`
without any box. -/
theorem vanishing (x y : ℝ) (h0 : x ^ 2 + y ^ 2 > 0)
    (h : x ^ 2 * Real.exp (2 * y) + y ^ 2 ≤ 0) : False := by
  interval

/-- Zero margin on a whole circle: the terms that vanish give the circle and pin `z`. -/
theorem circle (x y z : ℝ) (h : -((x ^ 2 + y ^ 2 - 1) ^ 2 + z ^ 2) ≥ 0)
    (h' : x < -1 ∨ x > 1 ∨ y < -1 ∨ y > 1 ∨ z < -1 ∨ z > 1) : False := by
  interval

/-- An ellipse and a half-plane that touch at `(1, 1)`, inside the box: one multiplier, `1 / 3`,
gives a semidefinite form. -/
theorem touches (x y : ℝ) (h : x ^ 2 + x * y + y ^ 2 ≤ 3) (h' : x + y > 2) : False := by
  interval

/-- A function that vanishes at the point: the sine is `y - y ^ 3 * r` with a bounded `r`. -/
theorem sine (x y : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : -1 ≤ y) (hy' : y ≤ 1)
    (h0 : x ^ 2 + y ^ 2 > 0) (h : x * Real.sin y - 2 * (x ^ 2 + y ^ 2) ≥ 0) : False := by
  interval

/-- The same for the hyperbolic tangent and the arctangent. -/
theorem hyperbolic (x y : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : -1 ≤ y) (hy' : y ≤ 1)
    (h0 : x ^ 2 + y ^ 2 > 0)
    (h : x * Real.tanh y + y * Real.arctan x - 2 * (x ^ 2 + y ^ 2) ≥ 0) : False := by
  interval

/-! ## Sets without a box -/

/-- The variables are bounded by a sublevel set of a quadratic, which gives the box. -/
theorem sublevel (x y : ℝ) (h : 3 / 2 * x ^ 2 - x * y + y ^ 2 ≤ 3 / 20)
    (h' : x < -6 / 5 ∨ x > 6 / 5 ∨ y < -6 / 5 ∨ y > 6 / 5 ∨ x ^ 2 + y ^ 2 > 36 / 25) : False := by
  interval

/-- A sublevel set that touches the constraint it is compared with: the bound is exact. -/
theorem touching (x : ℝ) (h : x ^ 2 ≤ 1) (h' : x < -1 ∨ x > 1) : False := by
  interval

/-- A ball and the complement of a larger ball. -/
theorem balls (x y z : ℝ) (h1 : x ^ 2 + y ^ 2 + z ^ 2 ≥ 9)
    (h2 : 1 - (x ^ 2 + y ^ 2 + z ^ 2) ≥ 0) : False := by
  interval

/-- A positive definite form without any bound on the variables. -/
theorem definite (x y : ℝ) (h0 : x ^ 2 + y ^ 2 > 0) (h : 2 * x ^ 2 + x * y + y ^ 2 ≤ 0) :
    False := by
  interval

/-- A bound that is affine in one variable, and a level set. -/
theorem level (x y z : ℝ) (hz : 2 * z - 1 = 0) (h : 1 - (x ^ 2 + y ^ 2 + z ^ 2) = 0)
    (h' : -(2 * x) * (-x / 8) + -(2 * y) * (-y / 8 + x ^ 2 / 5) + -(2 * z) * (-z / 8) ≤ 0) :
    False := by
  interval

/-- Two quadratics that no box separates: a ball and a half-space that almost touch. -/
theorem tangent (x : Fin 3 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1)
    (h1 : (x 0 - 7 / 10) ^ 2 + (x 1 + 7 / 10) ^ 2 + x 2 ^ 2 ≤ 1 / 100)
    (h2 : 1027 / 816 - x 0 + x 1 ≥ 0) : False := by
  interval

/-- A disc whose radius is given with `π` and a half-plane that touch at a point with irrational
coordinates: the multiplier of their combination is `80000 / 39999 * π⁻¹`, so the half-plane is
multiplied by `π`, and the form in `x`, `y` and `π` has a matrix of rational numbers. -/
theorem irrational (x y : ℝ)
    (h : 39999 / 640000 * Real.pi ^ 2 - x ^ 2 - y ^ 2 - 1 / 100 * x * y ≥ 0)
    (h' : y < -(1 / 4 * Real.pi)) : False := by
  interval

/-- The level of a sublevel set may be an expression in atoms with bounds, such as `π`. -/
theorem level_pi (x y : ℝ)
    (h : 39999 / 640000 * Real.pi ^ 2 - x ^ 2 - y ^ 2 - 1 / 100 * x * y ≥ 0)
    (h' : x < -1 ∨ x > 1 ∨ y < -1 ∨ y > 1) : False := by
  interval

/-- Nonnegative terms of degree four are dropped from a level set, and what is left confines
`x` and `y` to an ellipse. -/
theorem quartic (x y : ℝ) (h : 2 / 3 - y ^ 2 / 2 - 3 * x ^ 2 / 20 - x ^ 4 / 40 = 0)
    (h' : x > 3 ∨ y > 2 ∨ x ^ 2 + y ^ 2 > 7) : False := by
  interval

/-- Variables that equations define get their boxes from the enclosures of the other sides,
one after the other. -/
theorem defined (x y z : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : y = Real.exp x * Real.cos x)
    (hz : z = y ^ 2 - x) (h : z > 9 ∨ z < -2) : False := by
  interval

/-- Bounds through a maximum, a minimum and absolute values. -/
theorem lattice (x y : ℝ) (h : max |x| |y| ≤ 1) (h' : 0 ≤ min x y) : x * y + x ≤ 2 := by
  interval

/-- An atom with bounds may multiply the atoms without bounds. -/
theorem parameter (x y t : ℝ) (ht : 1 ≤ t) (ht' : t ≤ 2)
    (h : x ^ 2 + t * x * y + 2 * y ^ 2 ≤ t) (h' : x > 4) : False := by
  interval

/-- A value of a bounded function at an argument without bounds lies in the range of the
function. -/
theorem range (x y : ℝ) (hy : 0 ≤ y) (hy' : y ≤ 1)
    (h : Real.sin x * y > 3 / 2 ∨ Real.cos (x + y) < -2) : False := by
  interval

/-- An atom that an equation pins is replaced by its value, after which `y` cancels. -/
theorem pinned (x y : ℝ) (h : 5 / 4 - x = 0)
    (h' : -(x * (x - 1 / 10) * (1 - x) - 3 / 10 * x * y + 3 / 8 * y) ≤ 0) : False := by
  interval

/-- Quotients are multiplied by their denominators, and each case of the disjunction is
refuted without a box: the first by a form, the second by products of pairs. -/
theorem quotients (x : ℝ)
    (h : -x / (x ^ 2 + 1) < -1 ∨ (-3 * x) / (2 * Real.sqrt (x ^ 2 + 1)) > 5) : False := by
  interval

/-- Linear arithmetic with the tangent `t + 1 ≤ Real.exp t`. -/
theorem tangentLine (x y z : ℝ) (h : x + y + z ≥ 1)
    (h' : 2 - Real.exp (x + z) - Real.exp (x + y + z) ≥ 0) : False := by
  interval

/-- Linear arithmetic with `Real.exp t ≤ 1` for an argument that is nonpositive. -/
theorem nonpositive (x y z : ℝ) (hx : x ≤ 0) (hy : y ≤ 0) (hz : z ≤ 0)
    (h : 2 - Real.exp (x + z) - Real.exp (x + y + z) < 0) : False := by
  interval

/-! ## Ranges with infinite ends -/

/-- One evaluation on a half-line: `Real.exp (-x)` is in `[0, 1]` and `1 / (1 + x ^ 2)` in
`[0, 1 / 2]` there. -/
theorem halfLine (x : ℝ) (hx : 1 ≤ x)
    (h : Real.exp (-x) > 1 / 2 ∨ 1 / (1 + x ^ 2) > 1 / 2 ∨ Real.log x < 0) : False := by
  interval

/-- The whole line: the ranges of the hyperbolic tangent, the square root and the arctangent,
and a sum of exponentials that is at least one of them. -/
theorem wholeLine (x : ℝ) :
    Real.tanh x < 2 ∧ 0 ≤ Real.sqrt x ∧ Real.arctan x < 2 ∧ 0 ≤ Real.exp x + Real.exp (-x) := by
  interval

/-- Two variables with one bound each: a product of ranges by the signs of their ends. -/
theorem quadrant (x y : ℝ) (hx : 0 ≤ x) (hy : y ≤ 0) (h : Real.exp y * (1 + x) ≥ 2 + x) :
    False := by
  interval

/-- A tail gives the bound that the variable lacks: the left side is below `2` where `x ≥ 2`,
and a box decides the rest. -/
theorem tail (x : ℝ) (hx : 0 ≤ x) :
    -(173 / 250) * Real.exp (-(13 / 10) * x) + 319 / 100 - x - Real.exp (-(11 / 10) * x) < 2 := by
  interval

/-- A tail on each side of a variable without any bound. -/
theorem tails (x : ℝ) (h : x ^ 2 + Real.cosh x ≤ 3) : Real.sin x + x ^ 2 / 4 ≤ 3 / 2 := by
  interval

/-- The value of a function is kept while a tail bounds its argument: with the sine as a free
variable in `[-1, 1]` the two sides would meet at `x = 0`. -/
theorem coupled (x : ℝ) (hx : 0 ≤ x) (h : 2 + Real.sin x ≤ Real.exp (-x) - x) : False := by
  interval

/--
trace: [interval.constraints] derived the bounds [x < 2] from the tails on which the constraints fail
[interval.constraints] closed by a certificate of 7 boxes
-/
#guard_msgs in
set_option trace.interval.constraints true in
example (x : ℝ) (hx : 0 ≤ x)
    (h : 2 ≤ -(173 / 250) * Real.exp (-(13 / 10) * x) + 319 / 100 - x -
      Real.exp (-(11 / 10) * x)) : False := by
  interval

/-- A factor that the hypotheses pin to zero decides a product whose other factor has no
enclosure on the box. -/
example (x y : ℝ) (hy : -1 ≤ y ∧ y ≤ 1) (hx : x = 0) : x * (1 / y) ≤ 1 / 2 := by
  interval

/-! ## Existential statements -/

/-- A rational witness: `16` for the hyperbolic cosine, `1 / 512` for the logarithm, and `-1`
where the sine is above its argument. -/
example : (∃ x : ℝ, Real.cosh x > 2000000) ∧ (∃ x : ℝ, Real.log x < -6) ∧
    ∃ x : ℝ, Real.sin x > x := by
  refine ⟨?_, ?_, ?_⟩ <;> interval

/-- Two quantifiers are proved one after the other: the pair `(1 / 4, 1)`. -/
example : ∃ x y : ℝ, y + Real.log x < Real.log y := by
  interval

/-- A variable of the context, shifted by one, and a variable as it is. -/
example (a : ℝ) : (∃ x : ℝ, x > a) ∧ ∃ x : ℝ, Real.exp x > a := by
  constructor <;> interval

/-- A statement about every `y` at the witness is proved by the rest of the tactic. -/
example : ∃ x : ℝ, ∀ y : ℝ, y ≤ 1 → y < x * x - 1 := by
  interval

/--
trace: [interval.constraints] proved with the witness 128
-/
#guard_msgs in
set_option trace.interval.constraints true in
example : ∃ x : ℝ, Real.exp x > 10 ^ 50 := by
  interval

/-- Values that the statement names: the mean of two of its constants, also where they are
fractions or negative, and a constant with one added or taken off. -/
example : (∃ x : ℝ, 5 < x ∧ x < 7) ∧ (∃ x : ℝ, 100 < x ∧ x < 120) ∧
    (∃ x : ℝ, x < -5 ∧ -7 < x) ∧ (∃ x : ℝ, 1 / 3 < x ∧ x < 2 / 5) ∧
    (∃ x : ℝ, 0 < x ∧ x < 1 / 1000) ∧ (∃ x : ℝ, 1 / 200 < x ∧ x < 1 / 100) ∧
    (∃ x : ℝ, x > 2000) ∧ ∃ x : ℝ, x < -1000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> interval

/--
trace: [interval.constraints] closed by a certificate of 1 boxes
[interval.constraints] proved with the witness 6
-/
#guard_msgs in
set_option trace.interval.constraints true in
example : ∃ x : ℝ, 5 < x ∧ x < 7 := by
  interval

/-- Powers of two on both sides of one: `2048` and `1 / 2048` for the logarithm, `512`
between two bounds, `-256` for a cube, and numbers near a million. -/
example : (∃ x : ℝ, Real.log x > 7) ∧ (∃ x : ℝ, Real.log x < -7) ∧
    (∃ x : ℝ, 500 < x ∧ x < 1000 ∧ Real.log x < 13 / 2) ∧
    (∃ x : ℝ, x ^ 3 < -10 ^ 7) ∧ (∃ x : ℝ, x > 1000000) ∧
    ∃ x : ℝ, Real.log x > 13 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> interval


/-! The values of a statement: zero and the units, then by the larger of the numerator and the
denominator, with the constants of the statement, their neighbours and their means among the
powers of two, and nothing above `2 ^ 20`. -/

#guard (FloatLib.Numerics.Interval.Tactic.Constraints.witnessCandidates #[5, 7]).take 16 ==
  #[0, 1, -1, 2, -2, 1 / 2, -1 / 2, 4, -4, 1 / 4, -1 / 4, 5, 6, 7, 8, -8]

#guard (FloatLib.Numerics.Interval.Tactic.Constraints.witnessCandidates
    #[2000000, 1 / 5000000]).size ==
  (FloatLib.Numerics.Interval.Tactic.Constraints.witnessCandidates).size

#guard (FloatLib.Numerics.Interval.Tactic.Constraints.witnessCandidates).size == 83

/--
error: interval found no witness of the statement among the values that it tries: the real variables of the context, also shifted by one, and the rationals: zero, the powers of two from 2 ^ -20 to 2 ^ 20 with both signs, and the first 8 rational constants of the statement, each with the two numbers at distance one from it, and the mean of each two, without the numbers whose numerator or denominator is above 2 ^ 20; a value above 2 ^ 10 in size only where the statement takes no exponential of a number of that size
-/
#guard_msgs in
example : ∃ x : ℝ, x ^ 2 < 0 := by
  interval

/-! A value above `2 ^ 10` in size is passed over where the statement takes the exponential of
a number of that size: the evaluation that selects the values finds the hyperbolic cosine of
`2048` above two million, and with the guard it has no enclosure of it. -/

open Lean Elab Term FloatLib.Numerics.Interval.Tactic.Constraints in
#eval show TermElabM Unit from do
  let statement ← elabTerm (← `(Real.cosh (2048 : ℝ) > 2000000)) none
  let plain ← holdsByEvaluation statement 64 16
  let guarded ← holdsByEvaluation statement 64 16 (guard := some 10)
  unless plain == some true && guarded == some false do
    throwError "the evaluation gives {plain}, and {guarded} with the guard"

/-! ## Two sides that meet at an end of the range -/

/-- The two sides are equal at `0`, where no box separates them. The difference vanishes there,
and its derivative `Real.exp x - 2 * (x + 2) / 4` is nonnegative beyond, by the tangent of the
exponential. -/
theorem squareBelowExp (x : ℝ) (hx : 0 ≤ x) : (x + 2) ^ 2 / 4 ≤ Real.exp x := by
  interval

/-- Three derivatives in a row: the difference and its derivative vanish at `0`, the second
derivative is positive there, and the third is positive for `0 < x` by the tangent of the
exponential. -/
theorem fourthPowerBelowExp (x : ℝ) (hx : 0 ≤ x) : (x + 4) ^ 4 / 256 ≤ Real.exp x := by
  interval

/-- A quotient and a logarithm: the denominator and the argument are positive on the range, and
the derivative is a quotient of polynomials. -/
theorem logAbove (x : ℝ) (hx : 0 ≤ x) : 2 * x / (2 + x) ≤ Real.log (1 + x) := by
  interval

/-- From the upper end of the range: the two sides are equal at `1`, and the derivative of
their difference is nonpositive before. The range is open at `0`, where the quotient has no
value. -/
theorem logAboveBeforeOne (x : ℝ) (hx : 0 < x) (hx' : x ≤ 1) : 1 - 1 / x ≤ Real.log x := by
  interval

/-- A derivative that changes its sign in the range: `x * Real.sin x` is negative beyond `π`.
The range is cut at `2`, the derivative decides `[0, 2]`, and boxes the rest. -/
theorem sineAboveProduct (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 4) : x * Real.cos x ≤ Real.sin x := by
  interval

/-- An absolute value around one side: the two comparisons of the argument and of its negative
with the other side are proved one after the other. -/
theorem logNearArgument (x : ℝ) (hx : 0 ≤ x) : |Real.log (1 + x) - x| ≤ x ^ 2 := by
  interval

/--
trace: [interval.constraints] closed by linarith, without a box
[interval.constraints] the difference of the two sides has a sign at x = 0, and its derivative Real.exp x -
      (1 + 2 * x / 2) has one beyond
-/
#guard_msgs in
set_option trace.interval.constraints true in
example (x : ℝ) (hx : 0 ≤ x) (h : Real.exp x < 1 + x + x ^ 2 / 2) : False := by
  interval

/-- The theorem of the step, applied by hand to a square. -/
example (x : ℝ) (hx : 0 ≤ x) : (fun t : ℝ => t ^ 2) 0 ≤ (fun t : ℝ => t ^ 2) x :=
  le_of_deriv_nonneg (f' := fun t => 2 * t) hx
    (fun t _ _ => by simpa using hasDerivAt_pow 2 t) (fun t ht _ => by positivity)

/-- The theorem from an upper end, for a function that decreases. -/
example (x : ℝ) (hx : x < 0) : (fun t : ℝ => -t) 0 < (fun t : ℝ => -t) x :=
  lt_of_deriv_neg (f' := fun _ => -1) hx
    (fun t _ _ => (hasDerivAt_id' t).neg) (fun _ _ _ => by norm_num)

/-! ## Hints -/

/-- Cut points. -/
theorem cuts (x y : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : -1 ≤ y) (hy' : y ≤ 1)
    (h : |x| + |y| ≥ 5 / 2) : False := by
  interval (cut := [(x, 0), (y, 0)])

/-- A ball: it is cut out and decided by the forms around its center. -/
theorem ball (x y : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : -1 ≤ y) (hy' : y ≤ 1)
    (h0 : x ^ 2 + y ^ 2 > 0) (h : x ^ 2 * Real.exp (2 * y) + y ^ 2 ≤ 0) : False := by
  interval (ball := [(x, 0, 1 / 2), (y, 0, 1 / 2)])

/-- A ball with the matrix of the form. -/
theorem matrix (x y : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : -1 ≤ y) (hy' : y ≤ 1)
    (h0 : x ^ 2 + y ^ 2 > 0) (h : x ^ 2 * Real.exp (2 * y) + y ^ 2 ≤ 0) : False := by
  interval (ball := [(x, 0, 1 / 2), (y, 0, 1 / 2)]) (form := [[Real.exp (2 * y), 0], [1]])

/-- A box that the hypotheses imply and do not state, with the facts that prove it. -/
theorem stated (x y : ℝ) (h : x ^ 2 + y ^ 2 + Real.cos x ≤ 2) (h' : x * y > 4) : False := by
  interval (box := [(x, -2, 2), (y, -2, 2)])
    (facts := [Real.neg_one_le_cos x, sq_nonneg x, sq_nonneg y])

/-- Facts for the steps of linear and nonlinear arithmetic: the square that the products of
the linear comparisons lack. -/
theorem facts (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y ≤ 1) : x * y ≤ 1 / 4 := by
  interval (facts := [sq_nonneg (x - y)])

/-- Facts for a comparison that no step of the route reaches by itself: here two facts let
`nlinarith` decide where a disc and a half-plane touch. -/
theorem hinted (x y : ℝ)
    (h : 39999 / 640000 * Real.pi ^ 2 - x ^ 2 - y ^ 2 - 1 / 100 * x * y ≥ 0)
    (h' : y < -(1 / 4 * Real.pi)) : False := by
  interval (facts := [sq_nonneg (x + y / 200), Real.pi_pos])

/-! ## Inequalities that the boxes do not prove -/

/-- The bound is attained at `x = 1 / 2`: the form `(x - 1 / 2) ^ 2` of the negated goal. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  interval

/-- Half-lines are not boxes, but linear comparisons need none. -/
example {x y : ℝ} (hx : x ≤ 3) (hy : 2 ≤ y) : x - y ≤ 1 := by
  interval

/-- A bound stated with an absolute value, and `π` as a constant. -/
example (x : ℝ) (hx : |x| ≤ 1 / 2) : 1 / (1 - x) ≤ 2 ∧ |Real.pi - 3.14159265| < 1e-8 := by
  constructor <;> interval

/-- A quotient that touches its bounds at both ends of the box: when the search stops, the
comparisons are multiplied by their denominators and the cases are linear. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ x / (1 + x) ∧ x / (1 + x) ≤ 1 / 2 := by
  interval

/-- An absolute value that touches its bound inside the box: in each case of its sign the
quotient is multiplied out, and the form `(x - 1) ^ 2` or `(x + 1) ^ 2` decides it. -/
example (x : ℝ) (h0 : -2 ≤ x) (h1 : x ≤ 2) : |x / (1 + x ^ 2)| ≤ 1 / 2 := by
  interval

/-- Four corners where three constraints meet: the cases of the signs, then products of
pairs. -/
example (x y : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : -1 ≤ y) (hy' : y ≤ 1)
    (h : |x| + |y| ≥ 2 ∧ x * y < 1 ∧ x * y > -1) : False := by
  interval

/-- Half-lines: products of pairs, and the comparisons of an absolute value with its
argument. -/
example {x y : ℝ} (hx : 3 ≤ x) (hy : 2 ≤ y) : 6 ≤ x * y ∧ 3 ≤ |x| + |y| := by
  interval

/-- Polynomials on half-lines: each is a combination of products of the bounds. -/
example {x y : ℝ} (hx : x ≤ -2) (hy : 3 ≤ y) : 16 ≤ x ^ 4 ∧ x ^ 3 ≤ -8 ∧ 6 ≤ -x * y := by
  interval

/-- Linear comparisons that are not bounds have slacks too, and here they pin `y`. -/
example (x y : ℝ) (h : x + y ≥ 2) (h' : x - y ≥ 0) : x ^ 2 ≥ 1 := by
  interval

/-- Functions with a range, at any argument: the cases of the negated conjunction. -/
example (x : ℝ) :
    Real.sin x ^ 2 ≤ 1 ∧ 0 ≤ Real.exp x ∧ -1 ≤ Real.tanh x ∧ 1 ≤ Real.cosh x := by
  interval

/-- A comparison of constants to more digits than the default precision gives: at a point the
precision and the degree are doubled. -/
example : |Real.exp 1 - 2.718281828459045235360287471| < 1e-27 := by
  interval

/-! ## Failures -/

/-- A failed call leaves the goal as it was. -/
example (x y : ℝ) (hx : 0 ≤ x) (_hx' : x ≤ 1) (_hy : 0 ≤ y) (_hy' : y ≤ 1) (h : x + y ≤ 3) :
    x + y ≤ 3 ∧ 0 ≤ x := by
  fail_if_success have : False := by interval
  exact ⟨h, hx⟩

/--
error: interval could not refute the constraints on the box
  x ∈ [0, 1], y ∈ [0, 1]
Every constraint holds at every point of this box, so the constraints have a common point and the goal is false as stated.
-/
#guard_msgs in
example (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1) (h : x + y ≤ 3) :
    False := by
  interval

/--
error: interval could not refute the constraints on the box
  x ∈ [0, 1]
Every constraint that was read holds at every point of this box. Not read as constraints, since they are not combinations of real comparisons:
  ∀ (n : ℕ), ↑n ≠ x
-/
#guard_msgs in
example (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (h : ∀ n : ℕ, (n : ℝ) ≠ x) : False := by
  interval

/-- error: interval needs a rational upper bound for y -/
#guard_msgs in
example (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (h : x * y ≥ 3) : False := by
  interval

/--
error: interval could not refute the constraints on the box
  x ∈ [0, 1], y ∈ [1/2, 1]
The limit of 5 boxes was reached after 1 cuts on this branch; `(boxes := n)` raises it.
Undecided there:
  1 / 2 < x * y
    right side minus left side is in [-1/2, 1/2]; it fails on the box once the upper end is nonpositive
  x + y < 7 / 5
    right side minus left side is in [-0.600000, 0.900000]; it fails on the box once the upper end is nonpositive
-/
#guard_msgs in
example (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1)
    (h : x * y > 1 / 2) (h' : x + y < 7 / 5) : False := by
  interval (boxes := 5)

/--
error: interval found no real constraint among the hypotheses: it refutes combinations by ∧, ∨ and ¬ of ≤, <, = and ≠ between real expressions
-/
#guard_msgs in
example (n : ℕ) (h : 2 ≤ n) : False := by
  interval

/--
error: interval: the stated form is not the difference of the two sides of a comparison that holds outright (checked by ring)
-/
#guard_msgs in
example (x y : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : -1 ≤ y) (hy' : y ≤ 1)
    (h0 : x ^ 2 + y ^ 2 > 0) (h : x ^ 2 * Real.exp (2 * y) + y ^ 2 ≤ 0) : False := by
  interval (ball := [(x, 0, 1 / 2), (y, 0, 1 / 2)]) (form := [[1, 0], [1]])

/--
error: interval: linarith and nlinarith did not prove the stated bound
  x ≤ 5
from the comparisons of the hypotheses; `(facts := [...])` gives them further terms
-/
#guard_msgs in
example (x : ℝ) (h : Real.log x ≤ 1) (h' : x > 3) : False := by
  interval (box := [(x, 0, 5)])

/--
error: expected precision, degree, depth, boxes, maxHeartbeats, cut, ball, form, box or facts for a goal that is a set of constraints
-/
#guard_msgs in
example (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (h : x > 2) : False := by
  interval (speed := 3)

/-- error: interval: x + 1 is not an atom of the constraints -/
#guard_msgs in
example (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (h : x > 2) : False := by
  interval (cut := [(x + 1, 0)])

/-- error: in a case of the disjunctions among the hypotheses, interval needs a rational upper bound for y -/
#guard_msgs in
example (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (h : x * y ≥ 3 ∨ x + y < -1) :
    False := by
  interval

/--
The route stopped there, with its later steps untried: it had used
-/
#guard_msgs (substring := true) in
set_option maxHeartbeats 20000 in
example (x y : ℝ) (h0 : 0 < x) (h1 : x < y) (h2 : y < Real.pi / 2)
    (h : 1 / 2000 + Real.sin x / Real.sin y < x / y) : False := by
  interval

/-! ## The trace of the route -/

/--
trace: [interval.constraints] derived the bounds [5 / 4 ≤ x, x ≤ 5 / 4]
[interval.constraints] x is pinned to 5 / 4 and replaced by it
[interval.constraints] closed by a certificate of 1 boxes
-/
#guard_msgs in
set_option trace.interval.constraints true in
example (x y : ℝ) (hy : 0 ≤ y) (hy' : y ≤ 1) (h : 5 / 4 - x = 0)
    (h' : x * Real.sin y > 3 / 2) : False := by
  interval

/-! ## The checker on certificates written by hand -/

/-- `3 / 4 ≤ x` and `x ≤ 1 / 4`, as the atoms `0 ≤ x - 3 / 4` and `0 ≤ 1 / 4 - x`. -/
def apart : Constraint :=
  .and (.fails .negative (.binary .sub (.var 0) (.const (3 / 4))))
    (.fails .negative (.binary .sub (.const (1 / 4)) (.var 0)))

/-- One cut at `1 / 2`: the first atom fails below it and the second above it. -/
def separated : Refutation := .cut 0 (1 / 2) (.left (.atom 0)) (.right (.atom 0))

example : apart.refutes (Backend.rational {}) separated [⟨0, 1⟩] = true := by decide +kernel

/-- A certificate that names the wrong atom is rejected. -/
example : apart.refutes (Backend.rational {}) (.left (.atom 0)) [⟨0, 1⟩] = false := by
  decide +kernel

/-- The soundness theorem on the certificate: no real of `[0, 1]` satisfies both. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : ¬ apart.Holds (fun _ => x) := by
  have hbox : Box.ContainsReal [⟨0, 1⟩] (fun _ => x) := by
    refine Box.containsReal_cons ⟨?_, ?_⟩ (Box.containsReal_nil _) <;> simpa
  exact Constraint.refutes_sound (Backend.rational_sound {}) separated (by decide +kernel) hbox

/-- The matrix `[[2, 1], [1, 2]]` is positive definite, `[[1, 2], [2, 1]]` is not, and
`[[1, 1], [1, 1]]` is semidefinite only. -/
example : Form.definiteOn (Backend.rational {}) true
    ⟨[.var 0 0 0, .var 1 0 0], [[.const 2, .const 1], [.const 2]]⟩ [] = true := by
  decide +kernel

example : Form.definiteOn (Backend.rational {}) false
    ⟨[.var 0 0 0, .var 1 0 0], [[.const 1, .const 2], [.const 1]]⟩ [] = false := by
  decide +kernel

example : Form.definiteOn (Backend.rational {}) false
    ⟨[.var 0 0 0, .var 1 0 0], [[.const 1, .const 1], [.const 1]]⟩ [] = true ∧
    Form.definiteOn (Backend.rational {}) true
    ⟨[.var 0 0 0, .var 1 0 0], [[.const 1, .const 1], [.const 1]]⟩ [] = false := by
  decide +kernel

/-- The range of `Real.exp (-x)` on `x ≥ 0` is `[0, 1]`, and that of `0 * (1 / x)` is the point
zero whatever `x` is. -/
example : (Expr.unary .exp (.unary .neg (.var 0))).range (Backend.rational {}) []
      (Range.env [⟨some 0, none⟩]) = ⟨some 0, some 1⟩ ∧
    (Expr.binary .mul (.const 0) (.binary .div (.const 1) (.var 0))).range (Backend.rational {}) []
      (Range.env [Range.whole]) = ⟨some 0, some 0⟩ := by
  decide +kernel

/-- A product with a factor that is exactly zero is zero where the other factor has no
enclosure, here `1 / x` on a box that contains `x = 0`, and so is a quotient with such a
numerator: the evaluation with the zero rule has the enclosure of zero. In `Expr.eval?` a
failed operand fails the operation, so it has none. -/
example : (Expr.binary .mul (.const 0) (.binary .div (.const 1) (.var 0))).evalZero?
      (Backend.rational {}) (fun _ => some ⟨-1, 1⟩) = some ⟨0, 0⟩ ∧
    (Expr.binary .div (.const 0) (.var 0)).evalZero? (Backend.rational {})
      (fun _ => some ⟨-1, 1⟩) = some ⟨0, 0⟩ ∧
    (Expr.binary .mul (.const 2) (.binary .div (.const 1) (.var 0))).evalZero?
      (Backend.rational {}) (fun _ => some ⟨-1, 1⟩) = none ∧
    (Expr.binary .mul (.const 0) (.binary .div (.const 1) (.var 0))).eval?
      (Backend.rational {}) (fun _ => some ⟨-1, 1⟩) = none := by
  decide +kernel

/-- The equation of `Expr.eval?` at a binary operation: the operands in order, then the
backend's operation. -/
example (a b : Expr) (env : Nat → Option (Interval ℚ)) :
    (Expr.binary .mul a b).eval? (Backend.rational {}) env =
      (a.eval? (Backend.rational {}) env).bind fun I =>
        (b.eval? (Backend.rational {}) env).bind fun J =>
          (Backend.rational {}).binary? .mul I J :=
  Expr.eval?_binary (Backend.rational {}) env .mul a b

/-- An operation that the backend encloses evaluates to that enclosure
(`Expr.eval?_binary_of_some`), and the evaluation with the zero rule has every enclosure of
`Expr.eval?` (`Expr.evalZero?_of_eval?`). -/
example : (Expr.binary .add (.const 1) (.const 2)).evalZero? (Backend.rational {})
    (fun _ => none) = some ⟨3, 3⟩ :=
  Expr.evalZero?_of_eval? (Backend.rational {}) (fun _ => none) _
    (Expr.eval?_binary_of_some (Backend.rational {}) (fun _ => none) (I := ⟨1, 1⟩) (J := ⟨2, 2⟩)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

/-- `0 * (1 / x) - 1 < 0` on `[-1, 1]`: the check with the zero rule passes, the check on
`Expr.eval?` does not, and a certificate whose leaf is that atom refutes `0 * (1 / x) ≥ 1`. -/
def zeroTimes : Expr :=
  .binary .sub (.binary .mul (.const 0) (.binary .div (.const 1) (.var 0))) (.const 1)

example : zeroTimes.checkZero (Backend.rational {}) .negative [⟨-1, 1⟩] 0 = true ∧
    zeroTimes.check (Backend.rational {}) .negative [⟨-1, 1⟩] 3 = false ∧
    (Constraint.fails .negative zeroTimes).refutes (Backend.rational {}) (.atom 0) [⟨-1, 1⟩] =
      true := by
  decide +kernel

/-- The soundness theorem of the check with the zero rule, and a box that the check on
`Expr.eval?` passes passes it too. -/
example (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 1) :
    Relation.negative.Holds (zeroTimes.eval (fun _ => x) fun _ _ => 0) := by
  have hbox : Box.ContainsReal [⟨-1, 1⟩] (fun _ => x) := by
    refine Box.containsReal_cons ⟨?_, ?_⟩ (Box.containsReal_nil _) <;> simpa
  exact zeroTimes.checkZero_sound (Backend.rational_sound {}) (depth := 0) (by decide +kernel)
    hbox

example : (Expr.binary .sub (.var 0) (.const 2)).checkZero (Backend.rational {}) .negative
    [⟨0, 1⟩] 0 = true :=
  Expr.checkZero_of_check _ (by decide +kernel)

/-- The check on `Expr.eval?` keeps its theorems: the leaf in the ordinary notation, which
fails here because the quotient has no enclosure, and the soundness of the adaptive check. -/
example : zeroTimes.checkBox (Backend.rational {}) .negative [⟨-1, 1⟩] = false := by
  rw [Expr.checkBox_def]
  decide +kernel

example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Relation.negative.Holds ((Expr.binary .sub (.var 0) (.const 2)).eval (fun _ => x)
      fun _ _ => 0) := by
  have hbox : Box.ContainsReal [⟨0, 1⟩] (fun _ => x) := by
    refine Box.containsReal_cons ⟨?_, ?_⟩ (Box.containsReal_nil _) <;> simpa
  exact Expr.check_sound _ (Backend.rational_sound {}) (depth := 0) (by decide +kernel) hbox

/-- `x ≥ 1` and `Real.exp (-x) ≥ 1 / 2` have no common point: the check on the half-line, and
its soundness theorem. -/
def decays : Constraint :=
  .fails .negative (.binary .sub (.unary .exp (.unary .neg (.var 0))) (.const (1 / 2)))

example (x : ℝ) (hx : 1 ≤ x) : ¬ decays.Holds (fun _ => x) := by
  have hbox : Range.BoxContains [⟨some 1, none⟩] (fun _ => x) :=
    Range.boxContains_cons (Range.contains_lower (by simpa using hx)) (Range.boxContains_nil _)
  exact Constraint.not_holds_of_failsOn (Backend.rational_sound {}) (fun _ => rfl)
    (names := []) (fun _ _ h => by simp at h) (by decide +kernel) hbox

end FloatLibTests.Conformance.Numerics.Constraints
