/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Stochastic
import FloatLib.Numerics.Quantization.Stochastic.Realization
import FloatLib.Numerics.Quantization.Stochastic.Schedule
import FloatLib.Numerics.Quantization.Stochastic.Word
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A nonzero runtime instance of every sequential premise, for arbitrary loop length.
Each iteration quantizes one half with a fresh binary entropy word and adds its integer
result to the real observation. This is exact integer accumulation of rounded inputs.
-/

open MeasureTheory ProbabilityTheory
open FloatLib.Numerics.Quantization.Stochastic
open FloatLib.Floats.Formats.BinaryInterchange.Model.Policy
open scoped NNReal

namespace StochasticSequentialTests

def step (_ : ℕ) (s : ℝ) (e : Fin 2) : ℝ :=
  s + (roundQuot .stochastic false e.val 1 2 : ℝ)

noncomputable def ν : Measure (Fin 2) := wordLaw 2 (by decide)
instance : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (wordLaw 2 _))

theorem law :
    HasLaw (fun e : Fin 2 ↦ (roundQuot .stochastic false e.val 1 2 : ℝ))
      (cellLaw 0 1 (1 / 2) (by norm_num) (by constructor <;> norm_num)) ν := by
  have h := (roundQuot_cell false 2 1 2 (by decide) (by decide) (by decide)).comp
    (hasLaw_word_val 2 (by decide))
  convert h using 1 <;> norm_num [Function.comp_def, ν]

theorem local_mean (n : ℕ) (h : History (Fin 2) n) :
    ∫ e, increment id step 0 (fun _ ↦ 1 / 2) n (h, e) ∂ν = 0 := by
  convert mean_error_of_cell law using 1
  congr 1
  funext e
  simp [increment, step]

theorem local_mgf (n : ℕ) (h : History (Fin 2) n) :
    HasSubgaussianMGF (fun e ↦ increment id step 0 (fun _ ↦ 1 / 2) n (h, e))
      (1 / 4) ν := by
  have h := subgaussian_of_cell law
  convert h using 1
  · funext e
    simp [increment, step]
  · norm_num

theorem local_second (n : ℕ) (h : History (Fin 2) n) :
    ∫ e, (increment id step 0 (fun _ ↦ 1 / 2) n (h, e)) ^ 2 ∂ν ≤ 1 / 4 := by
  convert second_moment_of_cell_le law using 1
  · congr 1
    funext e
    simp [increment, step]
  · norm_num

example (n : ℕ) :
    ∫ h, run step 0 n h ∂historyLaw ν n = (n : ℝ) / 2 := by
  simpa [div_eq_mul_inv] using
    mean_run id step 0 (fun _ ↦ 1 / 2) n (fun k _ ↦ local_mean k)

example (n : ℕ) :
    ∫ h, (error id step 0 (fun _ ↦ 1 / 2) n h) ^ 2 ∂historyLaw ν n ≤ (n : ℝ) / 4 := by
  simpa [div_eq_mul_inv] using second_moment_error id step 0 (fun _ ↦ 1 / 2)
    n (fun k _ ↦ local_mean k) (fun _ ↦ 1 / 4) (fun k _ ↦ local_second k)

example (n : ℕ) :
    HasSubgaussianMGF (error id step 0 (fun _ ↦ 1 / 2) n) ((n : ℝ≥0) / 4)
      (historyLaw ν n) := by
  simpa [div_eq_mul_inv] using
    subgaussian_error id step 0 (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 4) n (fun k _ ↦ local_mgf k)

example (n : ℕ) :
    ((historyLaw ν n).prod ν)[increment id step 0 (fun _ ↦ 1 / 2) n |
      (inferInstance : MeasurableSpace (History (Fin 2) n)).comap Prod.fst] =ᵐ[
        (historyLaw ν n).prod ν] fun _ ↦ 0 :=
  condExp_fresh _ (local_mean n)

#print axioms mean_run
#print axioms second_moment_error
#print axioms subgaussian_error
#print axioms condExp_fresh
#print axioms tail_abs
#print axioms tail_delta
#print axioms hasLaw_word_val
#print axioms integral_wordLaw
#print axioms subgaussian_of_cell

end StochasticSequentialTests
