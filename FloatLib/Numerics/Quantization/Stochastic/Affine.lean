/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Stochastic.Dot

/-!
# Affine contractions with the bias added last

The dot product begins at zero, rounds every product and addition, and then
rounds its addition to the fixed bias with another fresh word. The reference
uses the supplied stored operands and bias. Its mean and tail certificate
follow by one use of the general fresh-addition composition rule.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Multiply and accumulate from zero, then round the final bias addition. -/
def roundedAffine {E F : Type*} (rp : Rounder E) (ra : Rounder F)
    (x y : ℕ → ℚ) (bias : ℚ) (n : ℕ) : History (E × F) n × F → ℚ :=
  roundedAdd ra (roundedDot rp ra x y 0 n) bias

/-- Every product, accumulation and final bias addition is in the proved local domain. -/
def AffineSafe {E F : Type*} (rp : Rounder E) (ra : Rounder F)
    (x y : ℕ → ℚ) (bias : ℚ) (n : ℕ) : Prop :=
  DotSafe rp ra x y 0 n ∧
    ∀ h, ra.Admissible (roundedDot rp ra x y 0 n h + bias)

variable {E F : Type*} [Finite E] [Finite F]
  [MeasurableSpace E] [MeasurableSpace F]
  [MeasurableSingletonClass E] [MeasurableSingletonClass F]
  {ν : Measure E} {ρ : Measure F} [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

/-- Explicit uniform local budgets give the affine layer's exact mean and tail certificate. -/
theorem affine_certificate (rp : Rounder E) (ra : Rounder F)
    (hp : rp.Law ν) (ha : ra.Law ρ) (x y : ℕ → ℚ) (bias : ℚ) (n : ℕ)
    (c : ℕ → ℝ≥0) (b : ℝ≥0)
    (hs : AffineSafe rp ra x y bias n) (hc : DotBudget rp ra x y 0 n c)
    (hb : ∀ h, ra.proxy (roundedDot rp ra x y 0 n h + bias) ≤ b) :
    Certificate ((historyLaw (ν.prod ρ) n).prod ρ)
      (fun h ↦ (roundedAffine rp ra x y bias n h : ℝ))
      ((∑ i ∈ Finset.range n, ((x i * y i : ℚ) : ℝ)) + bias)
      ((∑ i ∈ Finset.range n, (rp.proxy (x i * y i) + c i)) + b) := by
  simpa only [roundedAffine, Rat.cast_zero, zero_add] using
    roundedAdd_certificate ra ha (roundedDot rp ra x y 0 n) _ _
      (dot_certificate rp ra hp ha x y 0 n c hs.1 hc) bias b hs.2 hb

/-- Automatic budgets are finite maxima over all reached accumulation and bias inputs. -/
theorem affine_certificate_auto (rp : Rounder E) (ra : Rounder F)
    (hp : rp.Law ν) (ha : ra.Law ρ) (x y : ℕ → ℚ) (bias : ℚ) (n : ℕ)
    (hs : AffineSafe rp ra x y bias n) :
    Certificate ((historyLaw (ν.prod ρ) n).prod ρ)
      (fun h ↦ (roundedAffine rp ra x y bias n h : ℝ))
      ((∑ i ∈ Finset.range n, ((x i * y i : ℚ) : ℝ)) + bias)
      ((∑ i ∈ Finset.range n, (rp.proxy (x i * y i) + dotBudget rp ra x y 0 i)) +
        finiteBudget (fun h ↦ ra.proxy (roundedDot rp ra x y 0 n h + bias))) := by
  simpa only [roundedAffine, Rat.cast_zero, zero_add] using
    roundedAdd_certificate_auto ra ha (roundedDot rp ra x y 0 n) _ _
      (dot_certificate_auto rp ra hp ha x y 0 n hs.1) bias hs.2

end FloatLib.Numerics.Quantization.Stochastic
