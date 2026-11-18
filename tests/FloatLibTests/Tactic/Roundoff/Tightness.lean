/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Tactic.Roundoff

/-!
# Tightness: exact subtraction, centered forms, rounding attributes and linear constants

* A subtraction of two values within a factor of two of each other does not round (Sterbenz).
  `roundoff` recognizes it from the classic bounds `y / 2 ≤ x ≤ 2 y` among the hypotheses, from
  interval facts about the inputs, and for negative operands, in the forward, closed and backward
  modes. The difference is finite with no range condition. Without such facts a subtraction
  keeps its one rounding.
* A mixed bound encloses the exact value around the computed one (`MixedError.mem_Icc_computed`),
  as it encloses the computed value around the exact one.
* A rounding of a real in a rounding attribute states the unit roundoff of that attribute:
  `u` for the two that round to nearest, `2 u` for the four directed ones.
* A sum, a difference or a product with a rounding attribute, `ExecFloat.Binary.add x y
  (mode := .down)` and the others, states the unit roundoff of that attribute in the forward,
  closed and backward modes, also in a loop, in each of the six attributes. A directed rounding
  saturates on overflow, so the exact result is asked to be within the largest finite magnitude,
  and then the result is finite. A quotient in a directed attribute has no rule.
* A fused multiply-add rounds the exact `x * y + z` once, in the default attribute and in the
  five others, in every mode of the analysis and in a loop.
* The sum of `n` values has error at most `(n - 1) u ∑ |x i|` and the inner product at most
  `n u ∑ |x i y i|` (Rump 2012; Jeannerod and Rump 2013), here applied to loops over `Fin n`.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffTightness

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

section Configured

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

local notation "real" => ExecFloat.Binary.toReal

local notation "finite " x => ExecFloat.Binary.isFinite x = true

local notation "u" => Model.unitRoundoffAt format

local notation "η" => Model.underflowErrorAt format

local notation "Ω" => Model.toReal (Model.posMaxFinite format)

/-! ## Exact subtraction -/

/-- The classic bounds: the difference is exact and finite, with no range condition. -/
roundoff mixed theorem sterbenz_mixedError :=
  fun (x y : Value) (hformat : format.isIEEE = true)
      (hlow : real y / 2 ≤ real x) (hhigh : real x ≤ 2 * real y) =>
    real (x - y)

example (x y : Value) (hformat : format.isIEEE = true)
    (hlow : real y / 2 ≤ real x) (hhigh : real x ≤ 2 * real y) (hx : finite x) (hy : finite y) :
    (finite (x - y)) ∧ MixedError (real (x - y)) (real x - real y) 0 0 :=
  sterbenz_mixedError x y hformat hlow hhigh ⟨hx, hy⟩

/-- Interval facts about the inputs, as a membership and as a conjunction. -/
roundoff mixed theorem interval_mixedError :=
  fun (x y : Value) (hformat : format.isIEEE = true)
      (hx : real x ∈ Set.Icc 1 2) (hy : 1 ≤ real y ∧ real y ≤ 2) =>
    real (x - y)

example (x y : Value) (hformat : format.isIEEE = true)
    (hx : real x ∈ Set.Icc 1 2) (hy : 1 ≤ real y ∧ real y ≤ 2) (fx : finite x) (fy : finite y) :
    (finite (x - y)) ∧ MixedError (real (x - y)) (real x - real y) 0 0 :=
  interval_mixedError x y hformat hx hy ⟨fx, fy⟩

/-- Negative operands within a factor of two. -/
roundoff mixed theorem negative_mixedError :=
  fun (x y : Value) (hformat : format.isIEEE = true)
      (hlow : 2 * real y ≤ real x) (hhigh : real x ≤ real y / 2) =>
    real (x - y)

example (x y : Value) (hformat : format.isIEEE = true)
    (hlow : 2 * real y ≤ real x) (hhigh : real x ≤ real y / 2) (hx : finite x) (hy : finite y) :
    (finite (x - y)) ∧ MixedError (real (x - y)) (real x - real y) 0 0 :=
  negative_mixedError x y hformat hlow hhigh ⟨hx, hy⟩

/-- Inside a larger computation the product alone rounds. -/
roundoff mixed theorem scaled_mixedError :=
  fun (x y z : Value) (hformat : format.isIEEE = true)
      (hlow : real y / 2 ≤ real x) (hhigh : real x ≤ 2 * real y) =>
    real ((x - y) * z)

example (x y z : Value) (hformat : format.isIEEE = true)
    (hlow : real y / 2 ≤ real x) (hhigh : real x ≤ 2 * real y) :=
  show _ → _ ∧ MixedError _ ((real x - real y) * real z) u η from
    scaled_mixedError x y z hformat hlow hhigh

/-- Closed forward: each input carries one rounding, that of the product. -/
roundoff closed theorem scaled_closed :=
  fun (x y z : Value) (hformat : format.isIEEE = true)
      (hlow : real y / 2 ≤ real x) (hhigh : real x ≤ 2 * real y) =>
    real ((x - y) * z)

example (x y z : Value) (hformat : format.isIEEE = true)
    (hlow : real y / 2 ≤ real x) (hhigh : real x ≤ 2 * real y)
    (hfinite : finite ((x - y) * z)) :
    |real ((x - y) * z) - (real x - real y) * real z| ≤
      (|real x| * u + |real y| * u) * |real z| + η :=
  scaled_closed x y z hformat hlow hhigh hfinite

/-- Backward: the perturbations are those of one rounding. -/
roundoff (backward := true) theorem scaled_backward :=
  fun (x y z : Value) (hformat : format.isIEEE = true)
      (hlow : real y / 2 ≤ real x) (hhigh : real x ≤ 2 * real y) =>
    real ((x - y) * z)

example (x y z : Value) (hformat : format.isIEEE = true)
    (hlow : real y / 2 ≤ real x) (hhigh : real x ≤ 2 * real y)
    (hfinite : finite ((x - y) * z)) :
    ∃ δx δy, |δx| ≤ u ∧ |δy| ≤ u ∧
      |real ((x - y) * z) - (real x * (1 + δx) - real y * (1 + δy)) * real z| ≤ η :=
  scaled_backward x y z hformat hlow hhigh hfinite

/-- A sign alone does not make a subtraction exact: it keeps its rounding and its range. -/
roundoff mixed theorem plain_mixedError :=
  fun (x y : Value) (hformat : format.isIEEE = true) (hx : 0 ≤ real x) => real (x - y)

example (x y : Value) (hformat : format.isIEEE = true) (hx : 0 ≤ real x) (fx : finite x)
    (fy : finite y) (hrange : |real x - real y| ≤ Ω) :
    (finite (x - y)) ∧ MixedError (real (x - y)) (real x - real y) u 0 :=
  plain_mixedError x y hformat hx ⟨fx, fy, hrange⟩

/-! ## Centered forms -/

/-- A product, as a generated mixed theorem. -/
roundoff mixed theorem product_mixedError :=
  fun (x y : Value) (hformat : format.isIEEE = true) => real (x * y)

/-- A mixed theorem encloses the computed value around the exact one, and the exact value
around the computed one: the second enclosure reads only quantities the program has. -/
example (x y : Value) (hformat : format.isIEEE = true) (hx : finite x) (hy : finite y)
    (hrange : |real x * real y| ≤ Ω) :
    real x * real y - (u * |real x * real y| + η) ≤ real (x * y) ∧
      real x * real y ∈ Set.Icc (real (x * y) - (u * |real (x * y)| + η) / (1 - u))
        (real (x * y) + (u * |real (x * y)| + η) / (1 - u)) :=
  have h := (product_mixedError x y hformat ⟨hx, hy, hrange⟩).2
  ⟨h.lower_le, h.mem_Icc_computed (Model.unitRoundoffAt_lt_one format)⟩

/-! ## The linear constants of sums and inner products -/

/-- The sum of `n` values over `Fin n` has error at most `(n - 1) u ∑ |x j|`. -/
example {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : finite (Fin.foldl n (fun s j => s + x j) 0)) :
    |real (Fin.foldl n (fun s j => s + x j) 0) - ∑ j, real (x j)| ≤
      (n - 1 : ℕ) * u * ∑ j, |real (x j)| := by
  rw [Fin.foldl_eq_foldl_finRange] at hfinite ⊢
  have h := ExecFloat.Binary.abs_toReal_foldl_add_sub_le (l := List.finRange n) (term := x)
    (seed := 0) (by simp) hfinite
  simpa [Fin.sum_univ_def] using h

/-- The inner product over `Fin n` has error at most `n u ∑ |x j y j|` when no product
underflows. -/
example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : finite (Fin.foldl n (fun s j => s + x j * y j) 0))
    (hnormal : ∀ j, Model.NoUnderflowAt format (real (x j) * real (y j))) :
    |real (Fin.foldl n (fun s j => s + x j * y j) 0) - ∑ j, real (x j) * real (y j)| ≤
      n * u * ∑ j, |real (x j) * real (y j)| := by
  rw [Fin.foldl_eq_foldl_finRange] at hfinite ⊢
  have h := ExecFloat.Binary.abs_toReal_foldl_add_mul_sub_le (l := List.finRange n) (left := x)
    (right := y) (seed := 0) (by simp) hfinite (fun j _ => hnormal j)
  simpa [Fin.sum_univ_def] using h

/-! ## Operations in a rounding attribute -/

/-- The lower endpoint of a sum: one rounding toward negative infinity. -/
def lowerSum (x y : Value) : Value := ExecFloat.Binary.add x y (mode := .down)

/-- A sum in a directed attribute has the unit roundoff of that attribute and no absolute part.
The exact sum is within the largest finite magnitude, and then the result is finite. -/
roundoff mixed theorem lowerSum_mixedError :=
  fun (x y : Value) (hformat : format.isIEEE = true) => real (lowerSum x y)

example (x y : Value) (hformat : format.isIEEE = true) (hrange : |real x + real y| ≤ Ω)
    (hx : finite x) (hy : finite y) :
    (finite lowerSum x y) ∧
      MixedError (real (lowerSum x y)) (real x + real y) (Model.unitRoundoffIn format .down) 0 :=
  lowerSum_mixedError x y hformat ⟨hrange, hx, hy⟩

/-- The closed form weights each operand by the one rounding it takes part in. -/
roundoff closed theorem lowerSum_closed :=
  fun (x y : Value) (hformat : format.isIEEE = true) => real (lowerSum x y)

example (x y : Value) (hformat : format.isIEEE = true) (hrange : |real x + real y| ≤ Ω)
    (hx : finite x) (hy : finite y) :
    |real (lowerSum x y) - (real x + real y)| ≤
      |real x| * Model.unitRoundoffIn format .down +
        |real y| * Model.unitRoundoffIn format .down :=
  lowerSum_closed x y hformat ⟨hrange, hx, hy⟩

/-- The backward form moves the rounding onto the operands, each perturbed by at most the unit
roundoff of the attribute. -/
roundoff (backward := true) theorem lowerSum_backward :=
  fun (x y : Value) (hformat : format.isIEEE = true) => real (lowerSum x y)

example (x y : Value) (hformat : format.isIEEE = true) (hrange : |real x + real y| ≤ Ω)
    (hx : finite x) (hy : finite y) :
    ∃ δx δy, |δx| ≤ Model.unitRoundoffIn format .down ∧
      |δy| ≤ Model.unitRoundoffIn format .down ∧
        real (lowerSum x y) = real x * (1 + δx) + real y * (1 + δy) :=
  lowerSum_backward x y hformat ⟨hrange, hx, hy⟩

/-- The upper endpoint of `x * y + z`: both operations round toward positive infinity. -/
def upperAffine (x y z : Value) : Value :=
  ExecFloat.Binary.add (ExecFloat.Binary.mul x y (mode := .up)) z (mode := .up)

/-- Two operations in one attribute compose, and the product keeps the absolute part of its
attribute. -/
roundoff mixed theorem upperAffine_mixedError :=
  fun (x y z : Value) (hformat : format.isIEEE = true) => real (upperAffine x y z)

example (x y z : Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError (real (upperAffine x y z)) (real x * real y + real z)
      (Model.unitRoundoffIn format .up)
      ((1 + Model.unitRoundoffIn format .up) *
        (Model.unitRoundoffIn format .up * |real x * real y| + Model.underflowErrorIn format .up))
    from upperAffine_mixedError x y z hformat

roundoff closed theorem upperAffine_closed :=
  fun (x y z : Value) (hformat : format.isIEEE = true) => real (upperAffine x y z)

example (x y z : Value) (hformat : format.isIEEE = true) :=
  show _ → |real (upperAffine x y z) - (real x * real y + real z)| ≤
      |real x| * ((1 + Model.unitRoundoffIn format .up) ^ 2 - 1) * |real y| +
          |real z| * Model.unitRoundoffIn format .up +
        Model.underflowErrorIn format .up * (1 + Model.unitRoundoffIn format .up)
    from upperAffine_closed x y z hformat

/-- An operator and a call with an attribute in one program: each rounding has its own unit
roundoff. -/
roundoff mixed theorem mixedCalls_mixedError :=
  fun (x y z : Value) (hformat : format.isIEEE = true) =>
    real (ExecFloat.Binary.add (x * y) z (mode := .down))

example (x y z : Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _ (real x * real y + real z) (Model.unitRoundoffIn format .down)
      ((1 + Model.unitRoundoffIn format .down) * (u * |real x * real y| + η))
    from mixedCalls_mixedError x y z hformat

/-- The absolute analysis of a difference rounded toward zero. -/
roundoff theorem truncatedDifference_error :=
  fun (x y : Value) (hformat : format.isIEEE = true) =>
    real (ExecFloat.Binary.sub x y (mode := .towardZero))

example (x y : Value) (hformat : format.isIEEE = true) :=
  show _ → |real (ExecFloat.Binary.sub x y (mode := .towardZero)) - (real x - real y)| ≤
      0 + Model.unitRoundoffIn format .towardZero * |real x - real y|
    from truncatedDifference_error x y hformat

/-- The attribute as a variable: the rule holds in every one of the six. -/
roundoff mixed theorem anyAttribute_mixedError :=
  fun (mode : Model.IEEERoundingMode) (x y : Value) (hformat : format.isIEEE = true) =>
    real (ExecFloat.Binary.add x y (mode := mode))

example (mode : Model.IEEERoundingMode) (x y : Value) (hformat : format.isIEEE = true)
    (hrange : |real x + real y| ≤ Ω) (hx : finite x) (hy : finite y) :
    MixedError (real (ExecFloat.Binary.add x y (mode := mode))) (real x + real y)
      (Model.unitRoundoffIn format mode) 0 :=
  (anyAttribute_mixedError mode x y hformat ⟨hrange, hx, hy⟩).2

/-- The default attribute written out is the operator, and has its theorem. -/
roundoff mixed theorem writtenNearest_mixedError :=
  fun (x y : Value) (hformat : format.isIEEE = true) =>
    real (ExecFloat.Binary.add x y (mode := .nearest))

example (x y : Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _ (real x + real y) u 0 from writtenNearest_mixedError x y hformat

/-- A loop of sums rounded downward, in closed form: each term is weighted by the roundings it
takes part in, with the unit roundoff of the attribute. -/
roundoff closed theorem lowerTotal_closed :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    real (Fin.foldl n (fun s j => ExecFloat.Binary.add s (x j) (mode := .down)) 0)

example {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) :=
  show _ → |real (Fin.foldl n (fun s j => ExecFloat.Binary.add s (x j) (mode := .down)) 0) -
        List.foldl (fun s j => s + real (x j)) 0 (List.finRange n)| ≤
      ∑ j, |real (x j)| * ((1 + Model.unitRoundoffIn format .down) ^ (n - 1 - (j : ℕ) + 1) - 1)
    from lowerTotal_closed x hformat

/-- `nearestAway` rounds to a nearest value: a sum with it has the unit roundoff of the format. -/
roundoff mixed theorem tiesAway_mixedError :=
  fun (x y : Value) (hformat : format.isIEEE = true) =>
    real (ExecFloat.Binary.add x y (mode := .nearestAway))

example (x y : Value) (hformat : format.isIEEE = true) (hrange : |real x + real y| ≤ Ω)
    (hx : finite x) (hy : finite y) :
    MixedError (real (ExecFloat.Binary.add x y (mode := .nearestAway))) (real x + real y) u 0 := by
  simpa [Model.unitRoundoffIn, Model.IEEERoundingMode.halfUlps] using
    (tiesAway_mixedError x y hformat ⟨hrange, hx, hy⟩).2

/-! ## Fused multiply-add -/

/-- A fused multiply-add rounds the exact `x * y + z` once. -/
roundoff mixed theorem fused_mixedError :=
  fun (x y z : Value) (hformat : format.isIEEE = true) => real (ExecFloat.Binary.fma x y z)

example (x y z : Value) (hformat : format.isIEEE = true) (hx : finite x) (hy : finite y)
    (hz : finite z) (hrange : |real x * real y + real z| ≤ Ω) :
    (finite ExecFloat.Binary.fma x y z) ∧
      MixedError (real (ExecFloat.Binary.fma x y z)) (real x * real y + real z) u η :=
  fused_mixedError x y z hformat ⟨hx, hy, hz, hrange⟩

/-- Horner's rule by fused multiply-adds: one rounding for each step. -/
roundoff mixed theorem fusedHorner_mixedError :=
  fun (a b c x : Value) (hformat : format.isIEEE = true) =>
    real (ExecFloat.Binary.fma (ExecFloat.Binary.fma a x b) x c)

example (a b c x : Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _ ((real a * real x + real b) * real x + real c) u
      ((1 + u) * (u * |(real a * real x + real b) * real x| + η * |real x|) + η)
    from fusedHorner_mixedError a b c x hformat

/-- The absolute analysis: half an ulp of the exact value. -/
roundoff theorem fused_error :=
  fun (x y z : Value) (hformat : format.isIEEE = true) => real (ExecFloat.Binary.fma x y z)

example (x y z : Value) (hformat : format.isIEEE = true) :=
  show _ → |real (ExecFloat.Binary.fma x y z) - (real x * real y + real z)| ≤
      0 + Model.halfUlpAt format (real x * real y + real z)
    from fused_error x y z hformat

roundoff closed theorem fused_closed :=
  fun (x y z : Value) (hformat : format.isIEEE = true) => real (ExecFloat.Binary.fma x y z)

example (x y z : Value) (hformat : format.isIEEE = true) :=
  show _ → |real (ExecFloat.Binary.fma x y z) - (real x * real y + real z)| ≤
      |real x| * u * |real y| + |real z| * u + η
    from fused_closed x y z hformat

roundoff (backward := true) theorem fused_backward :=
  fun (x y z : Value) (hformat : format.isIEEE = true) => real (ExecFloat.Binary.fma x y z)

example (x y z : Value) (hformat : format.isIEEE = true) :=
  show _ → ∃ δx δz, |δx| ≤ u ∧ |δz| ≤ u ∧
      |real (ExecFloat.Binary.fma x y z) -
          (real x * (1 + δx) * real y + real z * (1 + δz))| ≤ η
    from fused_backward x y z hformat

/-- In a directed attribute the one rounding has the unit roundoff of that attribute. -/
roundoff mixed theorem fusedDown_mixedError :=
  fun (x y z : Value) (hformat : format.isIEEE = true) =>
    real (ExecFloat.Binary.fma x y z (mode := .down))

example (x y z : Value) (hformat : format.isIEEE = true)
    (hrange : |real x * real y + real z| ≤ Ω) (hx : finite x) (hy : finite y) (hz : finite z) :
    (finite ExecFloat.Binary.fma x y z (mode := .down)) ∧
      MixedError (real (ExecFloat.Binary.fma x y z (mode := .down))) (real x * real y + real z)
        (Model.unitRoundoffIn format .down) (Model.underflowErrorIn format .down) :=
  fusedDown_mixedError x y z hformat ⟨hrange, hx, hy, hz⟩

/-- A dot product accumulated by fused multiply-adds: one rounding for each term. -/
roundoff mixed theorem fusedDot_mixedError :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    real (Fin.foldl n (fun s j => ExecFloat.Binary.fma (x j) (y j) s) 0)

example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _
      (List.foldl (fun reference j => real (x j) * real (y j) + reference) 0 (List.finRange n))
      _ _
    from fusedDot_mixedError x y hformat

-- A quotient in a directed attribute has enclosure theorems only, so it has no rule.
/--
error: roundoff: no numerical rule for ExecFloat.Binary.div x y Model.IEEERoundingMode.down;
expose its arithmetic or supply an explicit bound in the context
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem lowerQuotient_mixedError :=
  fun (x y : Value) (hformat : format.isIEEE = true) =>
    real (ExecFloat.Binary.div x y (mode := .down))

end Configured

/-! ## Rounding attributes -/

section Attributes

variable {format : FloatFormat}

/-- Nearest-even states half an ulp at the real, with no relative part: the bound of one
rounding that the unit roundoff and the underflow allowance of the format are at least. -/
roundoff mixed theorem nearest_mixedError :=
  fun (x : ℝ) (hformat : format.isIEEE = true) => Model.roundAt format x

example (x : ℝ) (hformat : format.isIEEE = true) :
    MixedError (Model.roundAt format x) x 0 (Model.halfUlpAt format x) :=
  nearest_mixedError x hformat

/-- For a format without variables the constants of the standard model are numerals, and the
rounding states them. -/
roundoff mixed theorem nearest32_mixedError :=
  fun (x : ℝ) => Model.roundAt FloatFormat.binary32 x

example (x : ℝ) :
    MixedError (Model.roundAt FloatFormat.binary32 x) x
      (Model.unitRoundoffAt FloatFormat.binary32) (Model.underflowErrorAt FloatFormat.binary32) :=
  nearest32_mixedError x

/-- A directed rounding states the unit roundoff of its attribute. -/
roundoff mixed theorem down_mixedError :=
  fun (x : ℝ) (hformat : format.isIEEE = true) => Model.roundAt format x .down

example (x : ℝ) (hformat : format.isIEEE = true) :
    MixedError (Model.roundAt format x .down) x (Model.unitRoundoffIn format .down)
      (Model.underflowErrorIn format .down) :=
  down_mixedError x hformat

/-- The unit roundoff of a directed attribute is twice that of the format, and that of
`nearestAway` is that of the format. -/
example : Model.unitRoundoffIn format .down = 2 * Model.unitRoundoffAt format ∧
    Model.unitRoundoffIn format .towardZero = 2 * Model.unitRoundoffAt format ∧
    Model.unitRoundoffIn format .nearestAway = Model.unitRoundoffAt format := by
  simp [Model.unitRoundoffIn, Model.IEEERoundingMode.halfUlps]

/-- Two roundings in two attributes compose, each with its own unit roundoff. -/
roundoff mixed theorem mixedAttributes_mixedError :=
  fun (x y : ℝ) (hformat : format.isIEEE = true) =>
    Model.roundAt format (Model.roundAt format x .down * y) .towardZero

example (x y : ℝ) (hformat : format.isIEEE = true) :=
  show MixedError _ (x * y)
    ((1 + Model.unitRoundoffIn format .towardZero) * Model.unitRoundoffIn format .down +
      Model.unitRoundoffIn format .towardZero) _ from mixedAttributes_mixedError x y hformat

/-- A fused multiply-add of the model in any attribute is one rounding of the exact
`x * y + z`. -/
example (x y z : Model format) (hformat : format.isIEEE = true) (hx : x.isFinite = true)
    (hy : y.isFinite = true) (hz : z.isFinite = true) (mode : Model.IEEERoundingMode)
    (hrange : |x.toReal * y.toReal + z.toReal| ≤ (Model.posMaxFinite format).toReal) :
    Model.toReal (Model.fma x y z (mode := mode)) =
      Model.roundAt format (x.toReal * y.toReal + z.toReal) mode :=
  (Model.fma_finite_roundAt hformat hx hy hz hrange).2

/-- The absolute analysis of a directed rounding. -/
roundoff theorem up_error :=
  fun (x : ℝ) (hformat : format.isIEEE = true) => Model.roundAt format x .up

example (x : ℝ) (hformat : format.isIEEE = true) :=
  show |Model.roundAt format x .up - x| ≤ _ from up_error x hformat

/-- A sum of the descriptor model in a directed attribute is one rounding of the exact sum in
that attribute, and is finite, when the exact sum is within the largest finite magnitude. -/
example (x y : Model format) (hformat : format.isIEEE = true) (hx : x.isFinite = true)
    (hy : y.isFinite = true)
    (hrange : |x.toReal + y.toReal| ≤ (Model.posMaxFinite format).toReal) :
    (Model.add x y (mode := .down)).isFinite = true ∧
      Model.toReal (Model.add x y (mode := .down)) =
        Model.roundAt format (x.toReal + y.toReal) .down :=
  Model.add_finite_roundAt hformat hx hy hrange

/-- The absolute analysis of a sum of the descriptor model in a directed attribute: the unit
roundoff of that attribute, for an exact sum within the largest finite magnitude. -/
roundoff theorem modelSumDown_error :=
  fun (x y : Model format) (hformat : format.isIEEE = true) =>
    Model.toReal (Model.add x y .down)

example (x y : Model format) (hformat : format.isIEEE = true) (hx : x.isFinite = true)
    (hy : y.isFinite = true)
    (hrange : |x.toReal + y.toReal| ≤ (Model.posMaxFinite format).toReal) :
    |Model.toReal (Model.add x y .down) - (x.toReal + y.toReal)| ≤
      0 + Model.unitRoundoffIn format .down * |x.toReal + y.toReal| :=
  modelSumDown_error x y hformat ⟨hx, hy, hrange⟩

/-- The default attribute keeps its rule, half an ulp under a finite result: the rules of one
computation are tried in the order of their registration. -/
roundoff theorem modelSum_error :=
  fun (x y : Model format) (hformat : format.isIEEE = true) => Model.toReal (Model.add x y)

example (x y : Model format) (hformat : format.isIEEE = true)
    (hfinite : (Model.add x y).isFinite = true) :
    |Model.toReal (Model.add x y) - (x.toReal + y.toReal)| ≤
      0 + Model.halfUlpAt format (x.toReal + y.toReal) :=
  modelSum_error x y hformat hfinite

/-- A difference of the model in an attribute that is a variable. -/
roundoff theorem modelDifference_error :=
  fun (x y : Model format) (mode : Model.IEEERoundingMode) (hformat : format.isIEEE = true) =>
    Model.toReal (Model.sub x y mode)

example (x y : Model format) (mode : Model.IEEERoundingMode) (hformat : format.isIEEE = true) :=
  show _ → |Model.toReal (Model.sub x y mode) - (x.toReal - y.toReal)| ≤
      0 + Model.unitRoundoffIn format mode * |x.toReal - y.toReal|
    from modelDifference_error x y mode hformat

/-- A fused multiply-add of the model rounded upward. -/
roundoff theorem modelFusedUp_error :=
  fun (x y z : Model format) (hformat : format.isIEEE = true) =>
    Model.toReal (Model.fma x y z .up)

example (x y z : Model format) (hformat : format.isIEEE = true) :=
  show _ → |Model.toReal (Model.fma x y z .up) - (x.toReal * y.toReal + z.toReal)| ≤
      0 + (Model.unitRoundoffIn format .up * |x.toReal * y.toReal + z.toReal| +
        Model.underflowErrorIn format .up)
    from modelFusedUp_error x y z hformat

/-- The mixed rules of the descriptor model's operations are registered by
`Analysis.MixedError.Rounding`, which this module does not import. Without them the mixed
analysis reads the absolute bound, with no relative part. `MixedPrecision` has the relative
forms. -/
roundoff mixed theorem directedAdd_mixedError :=
  fun (x y : Model format) (hformat : format.isIEEE = true) =>
    Model.toReal (Model.add x y .down)

example (x y : Model format) (hformat : format.isIEEE = true) :=
  show _ → MixedError (Model.toReal (Model.add x y .down)) (x.toReal + y.toReal) 0
      (Model.unitRoundoffIn format .down * |x.toReal + y.toReal|)
    from directedAdd_mixedError x y hformat

/-- The value of `ieee 2 1` with the given bits. Its finite magnitudes are
`0, 1/2, 1, 3/2, 2, 3`, with the bits `0` to `5`, and `6` is `+∞`. -/
abbrev tiny (bits : Nat) : Model (.ieee 2 1) := Model.ofNatBits bits

/-- The bits of the sum of two values of `ieee 2 1` in a rounding attribute. -/
abbrev tinySum (left right : Nat) (mode : Model.IEEERoundingMode) : Nat :=
  (Model.add (tiny left) (tiny right) (mode := mode)).toNatBits

-- Why the rules ask for the range and not for a finite result: `3 + 3 = 6` is above the largest
-- finite value `3`. Rounded downward or toward zero the sum saturates at `3`, which is finite
-- and half the exact sum. The other attributes overflow.
example : tinySum 5 5 .down = 5 ∧ tinySum 5 5 .towardZero = 5 ∧ tinySum 5 5 .up = 6 ∧
    tinySum 5 5 .away = 6 ∧ tinySum 5 5 .nearest = 6 := by decide +kernel

-- `3/2 + 1 = 5/2` is within range and lies halfway between `2` and `3`: the directed
-- attributes take the two neighbors, nearest-even the even one and `nearestAway` the larger.
example : tinySum 3 2 .down = 4 ∧ tinySum 3 2 .towardZero = 4 ∧ tinySum 3 2 .up = 5 ∧
    tinySum 3 2 .away = 5 ∧ tinySum 3 2 .nearest = 4 ∧ tinySum 3 2 .nearestAway = 5 := by
  decide +kernel

/-- The tie test that `nearestAway` runs on the bits of an exact sum is the tie of its real
value, so the sum is the rounding of the exact sum to nearest with ties away from zero. -/
example (x y : Model format) (hformat : format.isIEEE = true) (hx : x.isFinite = true)
    (hy : y.isFinite = true)
    (hrange : |x.toReal + y.toReal| ≤ (Model.posMaxFinite format).toReal) :
    Model.toReal (Model.add x y (mode := .nearestAway)) =
      Model.roundAt format (x.toReal + y.toReal) .nearestAway :=
  (Model.add_finite_roundAt hformat hx hy hrange).2

end Attributes

end FloatLibTests.Conformance.BinaryInterchange.RoundoffTightness
