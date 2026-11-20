/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Util.CollectAxioms

import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.StochasticSupport
import FloatLib.Numerics.Quantization.Stochastic.Network
import FloatLib.Numerics.Quantization.Stochastic.Requantize
import FloatLib.Tactic.Roundoff.Stochastic

/-! The command follows wrappers to the actual entropy-consuming loops.
All generated results are parametric in the loop length and input values.
The final tests discharge every premise for a bfloat16 sum, dot product and affine map of
length three, through the finite supports, and read off rational budgets. The last section
instantiates the two-layer score-gap bound and the classification bound on a two-unit layer. -/

open FloatLib.Floats FloatLib.Floats.Formats
open FloatLib.Numerics.Quantization.Stochastic
open BinaryInterchange BinaryInterchange.Model.Policy
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochasticRoundoffTests

def sumCode {E : Type*} (r : Rounder E) (x : ℕ → ℚ) (n : ℕ) :
    History E n → ℚ :=
  roundedSum r x 0 n

def matmulEntry {E F : Type*} (rp : Rounder E) (ra : Rounder F)
    (x y : ℕ → ℕ → ℚ) (i j n : ℕ) : History (E × F) n → ℚ :=
  roundedDot rp ra (x i) (fun k ↦ y k j) 0 n

def weightGradientEntry {E F : Type*} (rp : Rounder E) (ra : Rounder F)
    (input cotangent : ℕ → ℕ → ℚ) (i j batch : ℕ) :
    History (E × F) batch → ℚ :=
  matmulEntry rp ra (fun i k ↦ input k i) cotangent i j batch

roundoff stochastic theorem sum_generated :=
  fun (fmt : FloatFormat) (M : ℕ) (hM : 0 < M) (x : ℕ → ℚ) (n : ℕ) ↦
    sumCode (binaryRounder fmt M) x n

roundoff stochastic theorem dot_generated :=
  fun (fmt : FloatFormat) (M : ℕ) (hM : 0 < M) (x y : ℕ → ℚ) (n : ℕ) ↦
    roundedDot (binaryRounder fmt M) (binaryRounder fmt M) x y 0 n

roundoff stochastic theorem affine_generated :=
  fun (fmt : FloatFormat) (M : ℕ) (hM : 0 < M) (x y : ℕ → ℚ) (b : ℚ) (n : ℕ) ↦
    roundedAffine (binaryRounder fmt M) (binaryRounder fmt M) x y b n

roundoff stochastic theorem matmul_generated :=
  fun (fmt : FloatFormat) (M : ℕ) (hM : 0 < M) (x y : ℕ → ℕ → ℚ) (i j n : ℕ) ↦
    matmulEntry (binaryRounder fmt M) (binaryRounder fmt M) x y i j n

roundoff stochastic theorem wgrad_generated :=
  fun (fmt : FloatFormat) (M : ℕ) (hM : 0 < M)
      (input cotangent : ℕ → ℕ → ℚ) (i j batch : ℕ) ↦
    weightGradientEntry (binaryRounder fmt M) (binaryRounder fmt M)
      input cotangent i j batch

roundoff stochastic theorem abstract_sum_generated :=
  fun {E : Type} [Finite E] [MeasurableSpace E] [MeasurableSingletonClass E]
      (ν : Measure E) [IsProbabilityMeasure ν] (r : Rounder E) (_hr : r.Law ν)
      (x : ℕ → ℚ) (n : ℕ) ↦ sumCode r x n

/-! A bfloat16 loop of length three with 16 fresh entropy bits per rounding. `binarySupport`
lists the two possible outcomes of every rounding, so each premise below is a finite check on the
listed accumulators, and it covers every entropy history. -/

abbrev r := binaryRounder FloatFormat.bfloat16 65536
abbrev support := binarySupport FloatFormat.bfloat16 65536
noncomputable abbrev word := wordLaw 65536 (by decide)

def left (k : ℕ) : ℚ := [129 / 128, 3 / 2, 131 / 128].getD k 0
def right (k : ℕ) : ℚ := [131 / 128, 5 / 4, 133 / 128].getD k 0

/-- Concrete history lengths can use the named probability instances explicitly. -/
example : IsProbabilityMeasure (historyLaw word 2) := by
  let := wordLaw_probability 65536 (by decide)
  exact historyLaw_probability _ 2

theorem sum_safe : SumSafe r left 0 3 :=
  support.sum_safe left 0 3 (by decide +kernel)

theorem dot_safe : DotSafe r r left right 0 3 :=
  support.safe support left right 0 3 (by decide +kernel)

theorem affine_safe : AffineSafe r r left right (1 / 4) 3 :=
  ⟨dot_safe, support.terminal support left right 0 (1 / 4) 3 _ (by decide +kernel)⟩

/-- The generated mean theorem applies to the three-term sum, whose exact value is `113 / 32`. -/
example : (∫ h, (sumCode r left 3 h : ℝ) ∂historyLaw word 3) = 113 / 32 := by
  rw [show sumCode r left 3 = roundedSum r left 0 3 from rfl,
    sum_generated_mean FloatFormat.bfloat16 65536 (by decide) left 3 sum_safe]
  norm_num [Finset.sum_range_succ, left]

/-- The generated certificates apply to the dot product and to the affine map. -/
example := dot_generated FloatFormat.bfloat16 65536 (by decide) left right 3 dot_safe
example := affine_generated FloatFormat.bfloat16 65536 (by decide) left right (1 / 4) 3 affine_safe

/-- The three-term sum with a number for its budget: two inexact additions of cell width
`1 / 64` and one exact addition, bounded by three such cells. -/
theorem sum_certified :
    Certificate (historyLaw word 3) (fun h ↦ (roundedSum r left 0 3 h : ℝ))
      (((0 : ℚ) : ℝ) + ∑ k ∈ Finset.range 3, (left k : ℝ))
      (Real.toNNReal ((3 / 16384 : ℚ) : ℝ)) :=
  support.sum_certificate (binaryRounder_law _ _ _) left 0 3
    (fun _ ↦ 1 / 16384) (3 / 16384) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The affine map `left · right + 1 / 4` with a number for its budget: products of cell width
`1 / 128`, additions of cell width `1 / 64` and a bias addition of cell width `1 / 32`. -/
theorem affine_certified :
    Certificate ((historyLaw (word.prod word) 3).prod word)
      (fun h ↦ (roundedAffine r r left right (1 / 4) 3 h : ℝ))
      ((∑ k ∈ Finset.range 3, ((left k * right k : ℚ) : ℝ)) + (1 / 4 : ℚ))
      (Real.toNNReal ((31 / 65536 : ℚ) : ℝ)) :=
  support.affine_certificate support (binaryRounder_law _ _ _) (binaryRounder_law _ _ _)
    left right (1 / 4) 3 (fun _ ↦ 1 / 65536) (fun _ ↦ 1 / 16384) (1 / 4096) (31 / 65536)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The tail of the affine error, with the budget as a number. -/
example (ε : ℝ) (hε : 0 ≤ ε) :
    ((historyLaw (word.prod word) 3).prod word).real
        {h | ε ≤ |(roundedAffine r r left right (1 / 4) 3 h : ℝ) -
          ((∑ k ∈ Finset.range 3, ((left k * right k : ℚ) : ℝ)) + (1 / 4 : ℚ))|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * (31 / 65536))) := by
  have h := affine_certified.tail ε hε
  rwa [Real.coe_toNNReal _ (by norm_num), show ((31 / 65536 : ℚ) : ℝ) = 31 / 65536 by norm_num]
    at h

/-! ## A two-layer score gap

Two hidden units with a ReLU and two output scores, every value a bfloat16 number rounded once
with 16 fresh entropy bits. The first pre-activation `257 / 256` rounds to `1` or `129 / 128`;
the second, `-259 / 256`, stays negative, so its unit is always zero. The premises of
`Network.gap_mgf` and of `classification_confidence` are checked on the support lists. -/

/-- The exact pre-activations of the two hidden units. -/
def pre (k : ℕ) : ℚ := [257 / 256, -(259 / 256)].getD k 0
/-- Lower bounds of the two rounded pre-activations. -/
def lower (k : ℕ) : ℚ := [1, -(65 / 64)].getD k 0
/-- Upper bounds of the two rounded pre-activations. -/
def upper (k : ℕ) : ℚ := [129 / 128, -(129 / 128)].getD k 0
/-- Output weights of the class that should win; its bias is `1 / 4`. -/
def winnerWeight (k : ℕ) : ℚ := [3 / 2, 1].getD k 0
/-- Output weights of its rival; its bias is zero. -/
def rivalWeight (k : ℕ) : ℚ := [1 / 2, 1].getD k 0

/-- The rounded pre-activation of unit `k`. -/
def row (k : ℕ) (e : Fin 65536) : ℝ := (r.round e (pre k) : ℝ)

/-- The exact value of an output unit on the rounded hidden values. -/
def output (weight : ℕ → ℚ) (bias : ℚ) (h : History (Fin 65536) 2) : ℚ :=
  weight 0 * max (r.round h.1.2 (pre 0)) 0 + weight 1 * max (r.round h.2 (pre 1)) 0 + bias

/-- The values of an output unit that the supports of the two hidden roundings allow. -/
def outputs (weight : ℕ → ℚ) (bias : ℚ) : List ℚ :=
  (support.values (pre 0)).flatMap fun a ↦ (support.values (pre 1)).map fun c ↦
    weight 0 * max a 0 + weight 1 * max c 0 + bias

theorem output_mem (weight : ℕ → ℚ) (bias : ℚ) (h : History (Fin 65536) 2) :
    output weight bias h ∈ outputs weight bias :=
  List.mem_flatMap.mpr ⟨_, support.covers _ _, List.mem_map.mpr ⟨_, support.covers _ _, rfl⟩⟩

theorem cast_output (weight : ℕ → ℚ) (bias : ℚ) (h : History (Fin 65536) 2) :
    ((output weight bias h : ℚ) : ℝ) =
      Network.affine (Network.hidden row 2 h) (fun k ↦ (weight k : ℝ)) (bias : ℝ) 2 := by
  simp [output, Network.affine, Network.hidden, row, Finset.sum_range_succ, History.get,
    Rat.cast_max]

/-- One fresh rounding of an admissible rational is a certified program. -/
theorem round_certificate (q : ℚ) (budget : ℚ) (hq : r.Admissible q)
    (hbudget : r.width q ^ 2 / 4 ≤ budget) :
    Certificate word (fun e ↦ (r.round e q : ℝ)) q (Real.toNNReal (budget : ℝ)) :=
  have law := binaryRounder_law FloatFormat.bfloat16 65536 (by decide)
  Certificate.mono ⟨law.mean q hq, law.second q hq, law.mgf q hq⟩
    (r.proxy_le_of_rat q budget hbudget)

/-- Two roundings that share one entropy word are not independent, and their linear
combination still has the exact mean. -/
example :
    (∫ e, ∑ i : Fin 2, (rivalWeight i : ℝ) * (r.round e (pre i) : ℝ) ∂word) =
      ∑ i : Fin 2, (rivalWeight i : ℝ) * (pre i : ℝ) :=
  mean_linear_combination (fun (i : Fin 2) e ↦ (r.round e (pre i) : ℝ)) (fun i ↦ (pre i : ℝ))
    (fun i ↦ (rivalWeight i : ℝ))
    (fun i ↦ (binaryRounder_law FloatFormat.bfloat16 65536 (by decide)).mean (pre i)
      ((by decide +kernel : ∀ k : Fin 2, r.Admissible (pre k)) i))

/-- The rounded winner score of one execution. -/
def winner (e : History (Fin 65536) 2 × (Fin 65536 × Fin 65536)) : ℝ :=
  (r.round e.2.2 (output winnerWeight (1 / 4) e.1) : ℝ)
/-- The rounded rival score of one execution. -/
def rival (e : History (Fin 65536) 2 × (Fin 65536 × Fin 65536)) : ℝ :=
  (r.round e.2.1 (output rivalWeight 0 e.1) : ℝ)

/-- The error of the score gap against the exact gap `257 / 512 - 899 / 512` has the
exponential-moment bound of `Network.gap_mgf`: proxy `3 / 65536` and no penalty, because the
first unit never crosses zero and the second has the same weight in both scores. -/
theorem gap :
    MGFBound (fun e ↦ (rival e - winner e) - (257 / 512 - 899 / 512)) (3 / 65536) 0
      ((historyLaw word 2).prod (word.prod word)) := by
  have h := Network.gap_mgf (μ := word) (ν := word) row (fun k ↦ (pre k : ℝ))
    (fun _ ↦ Real.toNNReal ((1 / 65536 : ℚ) : ℝ)) (fun k ↦ (lower k : ℝ))
    (fun k ↦ (upper k : ℝ)) (fun k ↦ (rivalWeight k : ℝ)) (fun k ↦ (winnerWeight k : ℝ))
    ((0 : ℚ) : ℝ) ((1 / 4 : ℚ) : ℝ) 2
    (fun h f ↦ (r.round f (output winnerWeight (1 / 4) h) : ℝ))
    (fun h f ↦ (r.round f (output rivalWeight 0 h) : ℝ))
    (Real.toNNReal ((1 / 65536 : ℚ) : ℝ)) (Real.toNNReal ((1 / 65536 : ℚ) : ℝ))
    (fun k hk ↦ round_certificate (pre k) (1 / 65536)
      ((by decide +kernel : ∀ k : Fin 2, r.Admissible (pre k)) ⟨k, hk⟩)
      ((by decide +kernel : ∀ k : Fin 2, r.width (pre k) ^ 2 / 4 ≤ 1 / 65536) ⟨k, hk⟩))
    (fun k hk e ↦ (Rat.cast_le (K := ℝ)).mpr
      ((by decide +kernel : ∀ k : Fin 2, ∀ v ∈ support.values (pre k), lower k ≤ v)
        ⟨k, hk⟩ _ (support.covers (pre k) e)))
    (fun k hk e ↦ (Rat.cast_le (K := ℝ)).mpr
      ((by decide +kernel : ∀ k : Fin 2, ∀ v ∈ support.values (pre k), v ≤ upper k)
        ⟨k, hk⟩ _ (support.covers (pre k) e)))
    (fun h ↦ by
      have hcheck := (by decide +kernel : ∀ q ∈ outputs winnerWeight (1 / 4),
        r.Admissible q ∧ r.width q ^ 2 / 4 ≤ 1 / 65536) _ (output_mem winnerWeight (1 / 4) h)
      have hcert := round_certificate _ _ hcheck.1 hcheck.2
      rwa [cast_output] at hcert)
    (fun h ↦ by
      have hcheck := (by decide +kernel : ∀ q ∈ outputs rivalWeight 0,
        r.Admissible q ∧ r.width q ^ 2 / 4 ≤ 1 / 65536) _ (output_mem rivalWeight 0 h)
      have hcert := round_certificate _ _ hcheck.1 hcheck.2
      rwa [cast_output] at hcert)
  have hbudget : ((Real.toNNReal ((1 / 65536 : ℚ) : ℝ) : ℝ≥0) : ℝ) = 1 / 65536 := by
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  refine (h.mono ?_ ?_).congr fun e ↦ ?_
  · norm_num [Finset.sum_range_succ, reluProxy, rivalWeight, winnerWeight, upper, hbudget]
  · norm_num [Finset.sum_range_succ, reluPenalty, rivalWeight, winnerWeight, lower, upper]
  · norm_num [rival, winner, Network.affine, Finset.sum_range_succ, pre, rivalWeight,
      winnerWeight]

/-- With probability at least `999 / 1000` the rounded winner score is above the rounded rival
score. -/
theorem winner_confidence :
    ((historyLaw word 2).prod (word.prod word)).real {e | winner e ≤ rival e} ≤ 1 / 1000 := by
  have : IsProbabilityMeasure (historyLaw word 2) := historyLaw_probability word 2
  have h := classification_confidence (μ := (historyLaw word 2).prod (word.prod word))
    ({()} : Finset Unit) winner (fun _ ↦ rival) (899 / 512) (fun _ ↦ 257 / 512)
    (fun _ ↦ 3 / 65536) (fun _ ↦ 0) (fun _ ↦ 1 / 1000) (fun _ _ ↦ gap)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ le_rfl) (fun _ _ ↦ by norm_num)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ by norm_num) (fun _ _ ↦ by
      have hlog : Real.log (1 / (1 / 1000)) ≤ 999 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / (1 / 1000))
        norm_num at this ⊢
        linarith
      exact (Real.sqrt_le_one.mpr (by linarith)).trans (by norm_num))
  simpa using h

#check sum_generated
#check sum_generated_mean
#check sum_generated_second
#check sum_generated_tail
#check sum_generated_confidence
#check dot_generated
#check affine_generated
#check matmul_generated
#check wgrad_generated
#check abstract_sum_generated
run_cmd do
  for name in [``sum_safe, ``dot_safe, ``affine_safe, ``sum_certified, ``affine_certified,
      ``gap, ``winner_confidence,
      ``sum_generated, ``sum_generated_confidence, ``dot_generated,
      ``affine_generated, ``matmul_generated, ``wgrad_generated,
      ``Rounder.law_of_cell, ``Certificate.exact_of_zero, ``binaryRounder_law,
      ``second_moment_roundRat_stochastic, ``Rounder.Support.affine_certificate,
      ``binarySupport, ``mean_reindex, ``mean_linear_combination,
          ``mean_independent_rounded_product,
      ``MGFBound.mono, ``MGFBound.independent_sub, ``MGFBound.exact_of_zero,
      ``weighted_relu, ``relu_fresh, ``classification_confidence, ``Network.gap_mgf] do
    for dependency in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unexpected axiom {dependency}"
    Lean.logInfo m!"{name}: only the three permitted axioms"

end StochasticRoundoffTests
