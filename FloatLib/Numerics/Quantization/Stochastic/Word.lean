/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Stochastic.Finite

/-!
# Finite entropy words and the integer runtime

`wordLaw` puts the existing finite uniform entropy law on `Fin M`. Reading the word's
natural value has exactly `entropyLaw M` as its law. This connects the integer runtime
to finite product spaces without assuming a different source of randomness.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory

/-- A positive finite entropy range carried by a bounded word type. -/
noncomputable def wordLaw (M : ℕ) (hM : 0 < M) : Measure (Fin M) :=
  (entropyLaw M).map (fun e ↦ (⟨e % M, Nat.mod_lt e hM⟩ : Fin M))

/-- The law of a word is a probability measure. -/
instance wordLaw_probability (M : ℕ) (hM : 0 < M) :
    IsProbabilityMeasure (wordLaw M hM) := by
  let := entropyLaw_probability M hM
  unfold wordLaw
  infer_instance

/-- Reading the finite word yields precisely the integer entropy law used by the runtime. -/
theorem hasLaw_word_val (M : ℕ) (hM : 0 < M) :
    HasLaw (fun e : Fin M ↦ e.val) (entropyLaw M) (wordLaw M hM) := by
  refine ⟨by measurability, ?_⟩
  rw [wordLaw, Measure.map_map (by measurability) (by measurability)]
  calc
    _ = (entropyLaw M).map id := Measure.map_congr (by
      filter_upwards [ae_entropyLaw_lt M] with e he
      exact Nat.mod_eq_of_lt he)
    _ = entropyLaw M := Measure.map_id

/-- Every real observation of a word has the same integral as the original integer sampler. -/
theorem integral_wordLaw (M : ℕ) (hM : 0 < M) (f : ℕ → ℝ) :
    ∫ e, f e.val ∂wordLaw M hM = ∫ e, f e ∂entropyLaw M :=
  (hasLaw_word_val M hM).integral_comp (by fun_prop)

end FloatLib.Numerics.Quantization.Stochastic
