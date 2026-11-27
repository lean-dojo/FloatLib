/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Affine.ModelProof

meta import FloatLib.Numerics.Enclosure.Affine.Model

/-!
# Affine forms and models

Lean's kernel computes the ranges of affine forms and models on literal inputs, and each range has
to equal the exact interval written next to it. The cases cover forms of different lengths,
negative coefficients and remainders, constants, and powers up to the seventh.

Then a few properties of the representation: trailing zero coefficients change nothing, `x - x`
is exactly zero, the range on the unit box is `center ± Σ i, |coefficients[i]|`, and compiled
code gives the same ranges as the kernel. Last, the square of `1 + ε₀ / 2` through the soundness
theorems.
-/

@[expose] public section

namespace FloatLibTests.Numerics.Affine

open FloatLib.Numerics FloatLib.Numerics.Enclosure.Affine

/-- `1 / 2 + ε₀ - ε₁ / 3`. -/
def a : AffineForm := ⟨1 / 2, [1, -1 / 3]⟩

/-- `-2 + ε₀ / 4 + 3 ε₂`. -/
def b : AffineForm := ⟨-2, [1 / 4, 0, 3]⟩

/-- `2 ε₀`. -/
def c : AffineForm := ⟨0, [2]⟩

/-- `3 / 5 - ε₀ / 2 + 2 ε₁ / 3 - 5 ε₂ / 4 + 7 ε₃ / 8`. -/
def d : AffineForm := ⟨3 / 5, [-1 / 2, 2 / 3, -5 / 4, 7 / 8]⟩

/-- A box of noise intervals: `ε₀ ∈ [-1/2, 1]`, `ε₁ ∈ [0, 2]`, `ε₂ ∈ [-3, -1]` and
`ε₃ ∈ [1/3, 5/2]`. -/
def box (i : Nat) : Interval ℚ :=
  [⟨-1 / 2, 1⟩, ⟨0, 2⟩, ⟨-3, -1⟩, ⟨1 / 3, 5 / 2⟩].getD i (Interval.point 0)

/-- The form `a` with the remainder `[-1/10, 1/5]`. -/
def A : AffineModel := ⟨a, ⟨-1 / 10, 1 / 5⟩⟩

/-- The form `b` with the remainder `[0, 1/7]`. -/
def B : AffineModel := ⟨b, ⟨0, 1 / 7⟩⟩

/-- The form `c` with remainder zero. -/
def C : AffineModel := .ofAffine c

/-- The form `d` with the negative remainder `[-1/3, -1/4]`. -/
def D : AffineModel := ⟨d, ⟨-1 / 3, -1 / 4⟩⟩

/-! ## Ranges on literal inputs -/

/-- Forms on a box and on the unit box. -/
example : a.rangeOn box = ⟨-2 / 3, 3 / 2⟩ ∧ d.rangeOn box = ⟨197 / 120, 1949 / 240⟩ ∧
    a.range = ⟨-5 / 6, 11 / 6⟩ ∧ b.range = ⟨-21 / 4, 5 / 4⟩ := by
  decide +kernel

/-- Products of forms, their parts, scaling and differences. -/
example : a.mulRangeOn b box = ⟨-33 / 2, 125 / 12⟩ ∧ a.mulRange b = ⟨-75 / 8, 59 / 8⟩ ∧
    a.mulRemainderOn b box = ⟨-73 / 8, 511 / 48⟩ ∧
    d.mulRangeOn b box = ⟨-173461 / 1920, -3743 / 480⟩ ∧
    b.mulRangeOn d box = ⟨-173461 / 1920, -3743 / 480⟩ ∧
    d.mulRange d = ⟨-207721 / 14400, 218089 / 14400⟩ ∧
    (a.linearMul b).range = ⟨-121 / 24, 73 / 24⟩ ∧ (a.scale (-3)).range = ⟨-11 / 2, 5 / 2⟩ ∧
    (a.sub b).range = ⟨-19 / 12, 79 / 12⟩ := by
  decide +kernel

/-- The pairwise enclosure of the product of two deviations, for lists of different lengths in
both orders and for a square. -/
example : AffineModel.quadraticRange a.coefficients b.coefficients = ⟨-49 / 12, 13 / 3⟩ ∧
    AffineModel.quadraticRange b.coefficients a.coefficients = ⟨-49 / 12, 13 / 3⟩ ∧
    AffineModel.quadraticRange d.coefficients b.coefficients = ⟨-1027 / 96, 655 / 96⟩ ∧
    AffineModel.quadraticRange d.coefficients d.coefficients = ⟨-125 / 16, 6241 / 576⟩ := by
  decide +kernel

/-- Products, sums, differences and negations of models. -/
example : (A.mul B).range = ⟨-1237 / 120, 172 / 21⟩ ∧
    (A.mul B).remainder = ⟨-79 / 15, 865 / 168⟩ ∧ (B.mul A).range = ⟨-1237 / 120, 172 / 21⟩ ∧
    (D.mul B).range = ⟨-71501 / 3360, 55313 / 3360⟩ ∧
    (D.mul D).range = ⟨-12541 / 900, 27281 / 1600⟩ ∧
    (A.add B).range = ⟨-371 / 60, 1439 / 420⟩ ∧ (A.sub B).range = ⟨-767 / 420, 407 / 60⟩ ∧
    (D.sub D).range = ⟨-1 / 12, 1 / 12⟩ ∧ A.neg.range = ⟨-61 / 30, 14 / 15⟩ ∧
    (A.mul A).range = ⟨-641 / 300, 3721 / 900⟩ ∧
    ((A.mul B).mul C).range = ⟨-1237 / 60, 253 / 15⟩ := by
  decide +kernel

/-- Products with constant models. -/
example : (A.mul (.const 3)).range = ⟨-14 / 5, 61 / 10⟩ ∧
    ((AffineModel.const (-2)).mul D).range = ⟨-437 / 60, 121 / 20⟩ := by
  decide +kernel

/-- Powers by binary exponentiation. The square is the product `A.mul A`. -/
example : (A.pow 0).range = ⟨1, 1⟩ ∧ (A.pow 1).range = ⟨-14 / 15, 61 / 30⟩ ∧
    (A.pow 2).range = ⟨-641 / 300, 3721 / 900⟩ ∧
    (A.pow 3).range = ⟨-111763 / 27000, 226981 / 27000⟩ ∧
    (A.pow 4).range = ⟨-853687 / 90000, 13845841 / 810000⟩ ∧
    (A.pow 5).range = ⟨-51024907 / 2700000, 844596301 / 24300000⟩ ∧
    (B.pow 3).range = ⟨-66483 / 448, 311397 / 5488⟩ ∧ (C.pow 4).range = ⟨0, 16⟩ ∧
    (D.pow 4).range = ⟨-9489471 / 40000, 744252961 / 2560000⟩ ∧
    (D.pow 7).range = ⟨-401766764438025587 / 22394880000000,
      7528541249594978203 / 358318080000000⟩ := by
  decide +kernel

/-! ## The representation -/

/-- Trailing zero coefficients change no range: `[1, -1/3, 0]` is `[1, -1/3]`. -/
example : (⟨1 / 2, [1, -1 / 3, 0]⟩ : AffineForm).rangeOn box = a.rangeOn box ∧
    (AffineModel.mul ⟨⟨1 / 2, [1, -1 / 3, 0]⟩, ⟨-1 / 10, 1 / 5⟩⟩ B).range = (A.mul B).range := by
  decide +kernel

/-- `x - x` is exactly zero for `x = 1 + ε₀`, where interval arithmetic on `[0, 2]` gives
`[-2, 2]`. -/
example : (((AffineForm.const 1).add (AffineForm.noise 0)).sub
    ((AffineForm.const 1).add (AffineForm.noise 0))).range = ⟨0, 0⟩ := by
  decide +kernel

/-- The range on the unit box is the center plus or minus the sum of the absolute values of the
coefficients, here `-2 ± 13/4`. -/
example : b.range.lo = -2 - 13 / 4 ∧ b.range.hi = -2 + 13 / 4 := by
  simp only [AffineForm.range_lo, AffineForm.range_hi, b]
  norm_num

/-- The operations keep compiled code: this is evaluated by the compiler, not by the kernel. -/
def compiledPower : Interval ℚ := (D.pow 7).range

#guard compiledPower ==
  ⟨-401766764438025587 / 22394880000000, 7528541249594978203 / 358318080000000⟩
#guard (A.mul B).range == ⟨-1237 / 120, 172 / 21⟩

/-! ## Soundness -/

/-- The one-noise form `1 + ε₀ / 2`. -/
def shiftedNoise : AffineForm := ⟨1, [1 / 2]⟩

/-- The value of `shiftedNoise` is `1 + ε₀ / 2`, from the sum of its terms. -/
theorem shiftedNoise_eval (ε : Nat → ℝ) : shiftedNoise.eval ε = 1 + ε 0 / 2 := by
  simp only [AffineForm.eval_eq_sum, shiftedNoise, List.length_singleton, Fin.sum_univ_one]
  simp
  ring

/-- `mulRange` contains the square of `1 + ε₀ / 2` at every assignment in the unit box. -/
example (ε : Nat → ℝ) (hε : ∀ i, |ε i| ≤ 1) :
    (shiftedNoise.mulRange shiftedNoise).ContainsReal some ((1 + ε 0 / 2) ^ 2) := by
  rw [← shiftedNoise_eval, pow_two]
  exact AffineForm.mul_mem_mulRange shiftedNoise shiftedNoise hε

/-- The product of models represents the square, and its range contains it. -/
example (ε : Nat → ℝ) (hε : ∀ i, |ε i| ≤ 1) :
    ((AffineModel.ofAffine shiftedNoise).mul (.ofAffine shiftedNoise)).range.ContainsReal some
      ((1 + ε 0 / 2) ^ 2) := by
  have h := AffineModel.represents_ofAffine shiftedNoise ε
  rw [shiftedNoise_eval] at h
  rw [pow_two]
  exact AffineModel.mem_range (h.mul h hε) hε

/-- The two enclosures of the square: the model keeps `ε₀ ^ 2 ≥ 0`, the product of forms does
not. -/
example : shiftedNoise.mulRange shiftedNoise = ⟨-1 / 4, 9 / 4⟩ ∧
    ((AffineModel.ofAffine shiftedNoise).mul (.ofAffine shiftedNoise)).range = ⟨0, 9 / 4⟩ := by
  decide +kernel

end FloatLibTests.Numerics.Affine
