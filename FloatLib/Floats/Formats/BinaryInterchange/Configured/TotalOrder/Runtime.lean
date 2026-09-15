/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Runtime

/-!
# Total ordering of configured binary values

These predicates decode the configured carrier and use the single exact semantic order.
Storage plans, field widths, and exponent biases require no separate implementation. The
predicates preserve NaN metadata and neither quiet signaling NaNs nor raise exceptions.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Total ordering of complete binary data, including signed zero and NaN class and payload. -/
@[inline] def totalOrder (x y : Value) : Bool :=
  Model.totalOrder (toModel x) (toModel y)

/-- Total ordering of magnitudes, retaining NaN class and payload while discarding signs. -/
@[inline] def totalOrderMag (x y : Value) : Bool :=
  Model.totalOrderMag (toModel x) (toModel y)

end FloatLib.Floats.ExecFloat.Binary
