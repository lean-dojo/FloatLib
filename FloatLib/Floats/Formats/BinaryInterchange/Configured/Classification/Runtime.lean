/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Classification.Runtime

/-!
# Classification of configured binary values

These non-signaling queries use the descriptor's interpretation through the
existing exact model codec. The same interface covers every configured carrier,
including custom biases and exceptional-value policies.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Test normality under the complete configured descriptor. -/
@[inline] def isNormal (x : Value) : Bool := Model.isNormal (toModel x)

/-- Return the shared IEEE class without changing the value or signaling an exception. -/
@[inline] def classify (x : Value) : FloatLib.Numerics.IEEEClass := Model.classify (toModel x)

/-- Test canonical interchange encoding, independently of the selected runtime carrier. -/
@[inline] def isCanonical (x : Value) : Bool := Model.isCanonical (toModel x)

end FloatLib.Floats.ExecFloat.Binary
