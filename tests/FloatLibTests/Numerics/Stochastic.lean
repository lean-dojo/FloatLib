/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.StochasticRuntime
import FloatLib.Floats.Formats.Stochastic
import FloatLib.Numerics.Quantization.Stochastic.Bits
import FloatLib.Numerics.Quantization.Stochastic.Boundary
import Mathlib.Tactic.NormNum

/-! Regression tests for the shared grid and the two actual finite-entropy algorithms.
The nondivisible range has a positive modulo bias and a negative add-truncate bias.
The format tests quantify over whole descriptor families rather than enumerating formats.
-/

open FloatLib.Numerics FloatLib.Numerics.Quantization
open FloatLib.Numerics.Quantization.Stochastic
open FloatLib.Floats.Formats MeasureTheory ProbabilityTheory

example :
    (∫ e, (BinaryInterchange.Model.Policy.roundQuot .stochastic false e 7 3 : ℝ)
      ∂entropyLaw 4) - 7 / 3 = 1 / 6 := by
  convert BinaryInterchange.Model.Policy.roundQuot_bias false 4 7 3
    (by decide) (by decide) using 1
  norm_num

example :
    (∫ e, (BinaryInterchange.Model.Policy.roundQuot .stochastic true e 7 3 : ℝ)
      ∂entropyLaw 6) = 7 / 3 :=
  BinaryInterchange.Model.Policy.roundQuot_mean_of_dvd true 6 7 3
    (by decide) (by decide) (by decide)

example : (∫ e, (addTrunc 4 3 1 e : ℝ) ∂entropyLaw 4) = 1 / 4 := by
  rw [addTrunc_mean 4 3 1 (by decide) (by decide) (by decide)]
  norm_num

example : (entropyLaw 4).real {e | 4 - 1 * 4 / 3 ≤ e} - 1 / 3 = -(1 / 12) := by
  convert addTrunc_bias 4 3 1 (by decide) (by decide) (by decide) using 1 <;> norm_num

example (r d k : ℕ) (hd : 0 < d) (hk : k ≤ d) :
    -(1 / (2 ^ r : ℝ)) <
      (entropyLaw (2 ^ r)).real {e | 2 ^ r - k * 2 ^ r / d ≤ e} - (k : ℝ) / d :=
  (bits_bias_bounds r d k hd hk).1

example (fmt : BinaryInterchange.FloatFormat) (x : ℝ)
    (hlo : ∃ a,
      ((BinaryInterchange.Model.numericalSystem fmt).mapScalar id).Representable a ∧ a ≤ x)
    (hhi : ∃ b,
      ((BinaryInterchange.Model.numericalSystem fmt).mapScalar id).Representable b ∧ x ≤ b) :
    ∃ lo hi,
      Ordered.Brackets ((BinaryInterchange.Model.numericalSystem fmt).mapScalar id) x lo hi :=
  neighbors_of_finite _ _ x hlo hhi

example (fmt : P3109.Format) :
    {x | ((P3109.Format.numericalSystem fmt).mapScalar
      (fun d : FloatLib.Numerics.Dyadic ↦ (d.toRat : ℝ))).Representable x}.Finite :=
  finite_representable _ _

example (radix : Radix) (digits width : ℕ) :
    {x | ((FixedPoint.Bounded.numericalSystem radix digits width).mapScalar
      (fun q : ℚ ↦ (q : ℝ))).Representable x}.Finite :=
  finite_representable _ _

example (radix : Radix) (digits : ℕ) (x : ℝ) :
    Ordered.Brackets ((FixedPoint.numericalSystem radix digits).mapScalar (fun q : ℚ ↦ (q : ℝ)))
      x ⟨⌊x * FixedPoint.scale radix digits⌋⟩ ⟨⌈x * FixedPoint.scale radix digits⌉⟩ :=
  FixedPoint.stochastic_brackets radix digits x

example : (cellLaw 0 1 (1 / 4) (by norm_num) (by constructor <;> norm_num)).real {1}
    = 1 / 4 := by
  convert cellLaw_upper 0 1 (1 / 4) (by norm_num) (by constructor <;> norm_num)
    using 1
  norm_num

example : variance (fun y : ℝ ↦ y)
    (cellLaw 0 1 (1 / 4) (by norm_num) (by constructor <;> norm_num)) = 3 / 16 := by
  convert variance_cellLaw 0 1 (1 / 4) (by norm_num) (by constructor <;> norm_num)
    using 1
  norm_num

example : cellLaw 0 1 0 (by norm_num) (by constructor <;> norm_num) = Measure.dirac 0 :=
  cellLaw_left _ _ _

example : (∫ y, y ∂neighborLaw 0 1 (max 0 (min 1 (2 : ℝ)))
    (clamp_mem 0 1 2 (by norm_num))) - 2 = -1 := by
  convert saturation_bias 0 1 0 1 2 (by norm_num) (by norm_num) using 1
  norm_num

example :
    (∫ y, (if y < 1 then 0 else y)
      ∂cellLaw 0 2 1 (by norm_num) (by constructor <;> norm_num)) - 1 = 0 := by
  convert flush_bias 0 2 1 (by norm_num) (by constructor <;> norm_num) (· < 1)
    using 1
  norm_num

example :
    (∫ y, (if |y| ≤ 2 then 0 else y)
      ∂cellLaw 0 2 1 (by norm_num) (by constructor <;> norm_num)) = 0 :=
  mean_flush_of_endpoints _ _ _ _ _ _ (by norm_num) (by norm_num)

/-! The cell law on the bfloat16 neighbours `1` and `129 / 128` of `257 / 256`. -/

theorem cell : (1 : ℝ) < 129 / 128 := by norm_num

theorem inside : (257 / 256 : ℝ) ∈ Set.Icc (1 : ℝ) (129 / 128) := by
  constructor <;> norm_num

/-- The lower neighbour has probability one half. -/
example : (cellLaw 1 (129 / 128) (257 / 256) cell inside).real {1} = 1 / 2 := by
  rw [cellLaw_lower]
  norm_num

/-- The variance is at most a quarter of the squared gap. -/
example :
    variance (fun y : ℝ ↦ y) (cellLaw 1 (129 / 128) (257 / 256) cell inside) ≤ 1 / 65536 :=
  (variance_cellLaw_le _ _ _ cell inside).trans (by norm_num)

/-- The same variance for the law that also covers exact grid inputs. -/
example : variance (fun y : ℝ ↦ y) (neighborLaw 1 (129 / 128) (257 / 256) inside) = 1 / 65536 := by
  rw [variance_neighborLaw]
  norm_num

/-- Almost surely the error is below the gap. -/
example : ∀ᵐ y ∂cellLaw 1 (129 / 128) (257 / 256) cell inside, |y - 257 / 256| < 1 / 128 := by
  filter_upwards [ae_error_lt_gap 1 (129 / 128) (257 / 256) cell inside] with y hy
  exact hy.trans_le (by norm_num)

/-- Choosing the upper neighbour with probability `2 / 3`, as three entropy words reduced modulo
two do, shifts the mean by `(2 / 3 - 1 / 2) / 128`. -/
example :
    (∫ y, y ∂bernoulliMeasure (129 / 128 : ℝ) 1 ⟨2 / 3, by norm_num, by norm_num⟩) - 257 / 256 =
      1 / 768 := by
  rw [mean_bias 1 (129 / 128) (257 / 256) cell inside]
  change ((2 / 3 : ℝ) - (257 / 256 - 1) / (129 / 128 - 1)) * (129 / 128 - 1) = 1 / 768
  norm_num

/-- A policy that returns `1` for both outcomes has bias `1 - 257 / 256`, whatever the
probability. -/
example (p : unitInterval) :
    (∫ y, (fun _ ↦ (1 : ℝ)) y ∂bernoulliMeasure (129 / 128 : ℝ) 1 p) - 257 / 256 = -(1 / 256) := by
  rw [bias_bernoulli]
  ring

#print axioms mean_cellLaw
#print axioms ae_error_lt_gap
#print axioms variance_cellLaw_le
#print axioms cellLaw_lower
#print axioms cellLaw_right
#print axioms bias_bernoulli
#print axioms mean_bias
#print axioms integral_finite_choice
#print axioms entropyLaw_mod_of_dvd
#print axioms mean_neighborLaw
#print axioms variance_neighborLaw
#print axioms ae_neighborLaw_representable
#print axioms neighborLaw_input_bias
#print axioms FixedPoint.stochastic_brackets
#print axioms BinaryInterchange.Model.Policy.roundQuot_bias
#print axioms addTrunc_mean
#print axioms bits_bias_bounds
#print axioms BinaryInterchange.Model.Policy.roundQuot_cell
#print axioms BinaryInterchange.Model.Policy.roundRat_stochastic_choice
#print axioms BinaryInterchange.Model.Policy.integral_roundRat_stochastic
