/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Basic
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.StochasticGrid
import Mathlib.Tactic.NormNum

/-! The complete bfloat16 runtime at a nonzero, inexact input. The output
finiteness obligations are discharged by its two actual encoded results. -/

open FloatLib.Floats FloatLib.Floats.Formats FloatLib.Numerics
open BinaryInterchange BinaryInterchange.Model BinaryInterchange.Model.Policy
open FloatLib.Numerics.Quantization.Stochastic MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochasticBinaryTests

abbrev fmt := FloatFormat.bfloat16

theorem aligned : alignedRatio fmt 257 256 = (32896, 256) := by decide

theorem spacing : stochasticSpacing fmt 257 256 = 1 / 128 := by
  change bpow (-7) = 1 / 128
  norm_num [bpow, Flocq.bpow, binaryRadix, Radix.toReal]

theorem finite (e : ℕ) :
    isFinite (roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
      e false 257 256 (by decide)) = true :=
  roundRat_stochastic_finite fmt _ rfl false 257 256 (by decide)
    (by decide) (by decide) e

theorem bounded (e : ℕ) :
    (roundQuot .stochastic false e (alignedRatio fmt 257 256).1
      (alignedRatio fmt 257 256).2 : ℝ) * stochasticSpacing fmt 257 256 ≤
        toReal (posMaxFinite fmt) := by
  rw [aligned, spacing]
  have h := roundQuot_stochastic_upper false e 32896 256
  have hq : roundQuot .stochastic false e 32896 256 ≤ 129 := h
  apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hq) (by norm_num : (0 : ℝ) ≤ 1 / 128)).trans
  rw [toReal_posMaxFinite_of_eq fmt (significand := 255) (exponent := 120)
    (by decide) (by decide)]
  norm_num

example :
    (∫ e, toReal (roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
      e false 257 256 (by decide)) ∂entropyLaw 256) = 257 / 256 := by
  simpa using mean_roundRat_stochastic fmt false 256 257 256
    (by decide) (by decide) (by decide) (by decide)
    (by rw [aligned]) finite bounded

example :
    HasSubgaussianMGF
      (fun e ↦ toReal (roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
        e false 257 256 (by decide)) - 257 / 256)
      (1 / 65536) (entropyLaw 256) := by
  have h := subgaussian_roundRat_stochastic fmt false 256 257 256
    (by decide) (by decide) (by decide) (by decide)
    (by rw [aligned]) finite bounded
  convert h using 1 <;> norm_num [spacing]

#print axioms toReal_roundRat_stochastic
#print axioms mean_roundRat_stochastic
#print axioms subgaussian_roundRat_stochastic
#print axioms alignedRatio_value
#print axioms roundQuot_stochastic_bounds

end StochasticBinaryTests
