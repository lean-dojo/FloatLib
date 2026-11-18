/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedPrecision
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real

/-!
# Exact wide products through configured carriers

This is the codec transport of `Model.toReal_mul_cast_exact`. It applies to every storage plan
and selected multiplication capability with the model specification. Precision and lower-grid
conditions concern arbitrary source descriptors; finite casts, finite output, and a zero or
normal exact product exclude range loss. The arithmetic argument lives in `Analysis.MixedPrecision`.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {left right dst : FloatFormat} {plan : Configured.StoragePlan dst} {code : Type}
  [ExecFloat.ModelCodec plan (Model dst) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family dst code plan)]
  [cap : ExecFloat.Mul (Configured.Family dst code plan)]
  [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]

local notation "Value" => ExecFloat (Configured.Family dst code plan)

/-- A configured wide product inherits exactness from its descriptor-model operation. -/
theorem toReal_mul_cast_exact (x : Model left) (y : Model right)
    (hdst : dst.isIEEE = true)
    (hlmin : dst.minSubnormalExponent ≤ left.minSubnormalExponent)
    (hrmin : dst.minSubnormalExponent ≤ right.minSubnormalExponent)
    (hprec : (left.fracWidth + 1) + (right.fracWidth + 1) ≤ dst.fracWidth + 1)
    (hnormal : Model.toReal x * Model.toReal y = 0 ∨
      Model.minNormalAt dst ≤ |Model.toReal x * Model.toReal y|)
    (hout : isFinite
      ((ofModel (Model.cast left dst x) : Value) * ofModel (Model.cast right dst y)) = true) :
    toReal ((ofModel (Model.cast left dst x) : Value) * ofModel (Model.cast right dst y)) =
      Model.toReal x * Model.toReal y := by
  simpa only [toReal, toModel_hMul, toModel_ofModel] using
    Model.toReal_mul_cast_exact x y hdst hlmin hrmin hprec hnormal
      (by simpa only [isFinite, toModel_hMul, toModel_ofModel] using hout)

end FloatLib.Floats.ExecFloat.Binary
