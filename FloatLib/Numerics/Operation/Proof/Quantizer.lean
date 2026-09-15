/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Operation.Semantics
public import FloatLib.Numerics.Core.Proof

/-!
# Proof-indexed quantizers

Application lemmas for scalar quantizers that implement a declared rounding map on an explicit
domain.

The contract records both where the quantizer is valid and which mathematical rounding function
it realizes. Generic numerical code can therefore request the contract it needs without knowing
whether execution uses fixed point, a codebook, a floating format, or another representation.
-/

@[expose] public section

namespace FloatLib.Numerics.Operation
namespace QuantizerOn

/-- A refining scalar quantizer represents its declared rounded value. -/
theorem represents {S : NumericalSystem} {quantize : S.Scalar → S.Code}
    {round : S.Scalar → S.Scalar} {pre : S.Scalar → Prop}
    (hrefines : QuantizerOn S quantize round pre) {value : S.Scalar}
    (hpre : pre value) :
    S.Represents (quantize value) (round value) :=
  hrefines value hpre

/--
A refining scalar quantizer represents an independently stated result equal to its rounding map.

This is the normalization-tolerant shape used by generic automation: the displayed result may
already have been simplified without changing the quantizer contract.
-/
theorem represents_eq {S : NumericalSystem} {quantize : S.Scalar → S.Code}
    {round : S.Scalar → S.Scalar} {pre : S.Scalar → Prop}
    {value expected : S.Scalar}
    (hrefines : QuantizerOn S quantize round pre) (hpre : pre value)
    (hround : round value = expected) :
    S.Represents (quantize value) expected := by
  rw [← hround]
  exact represents hrefines hpre

/-- Apply a scalar quantizer and attach its erased representation proof. -/
@[inline] def applyAt {S : NumericalSystem} {quantize : S.Scalar → S.Code}
    {round : S.Scalar → S.Scalar} {pre : S.Scalar → Prop}
    (hrefines : QuantizerOn S quantize round pre) (value : S.Scalar)
    (hpre : pre value) :
    S.AtFinite (round value) :=
  ⟨quantize value, hrefines value hpre⟩

end QuantizerOn
end FloatLib.Numerics.Operation
