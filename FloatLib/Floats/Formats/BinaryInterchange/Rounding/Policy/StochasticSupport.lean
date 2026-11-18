/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.StochasticRat
public import FloatLib.Numerics.Quantization.Stochastic.Support

/-!
# Two-output support of executable binary stochastic rounding

The finite support consists of the actual outputs at entropy zero and at
one less than the aligned denominator. Every entropy word selects one of
these, even at boundaries. This support does not itself assert unbiasedness;
that still requires `StochasticSafe` and a positive entropy range.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Policy

open FloatLib.Floats FloatLib.Numerics.Quantization.Stochastic

/-- Two actual runtime observations cover every finite entropy word. -/
def binarySupport (fmt : FloatFormat) (M : ℕ) : (binaryRounder fmt M).Support where
  values x := [stochasticValue fmt 0 x,
    stochasticValue fmt ((alignedRatio fmt x.num.natAbs x.den).2 - 1) x]
  covers x e := by
    change stochasticValue fmt e.val x ∈ _
    have h := stochasticValue_choice fmt x e.val
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    split_ifs at h
    · exact Or.inl h
    · exact Or.inr h

end FloatLib.Floats.Formats.BinaryInterchange.Model.Policy
