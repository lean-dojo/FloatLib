/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Instances -- shake: keep
public import FloatLib.Floats.Formats.Logarithmic.Configured.Plan
public import FloatLib.Floats.ExecFloat.Core.Capability

/-!
# Dispatch instance for exact logarithmic multiplication

The ordinary `ExecFloat` multiplication interface selects the certified direct logarithmic
kernel.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Logarithmic

open FloatLib.Numerics

variable {radix : Radix}

/-- Exact logarithmic multiplication participates in ordinary `ExecFloat` dispatch. -/
@[always_inline] instance
    [planning : Backend.PolicyFor (Family radix)] :
    ExecFloat.Mul (Family radix) :=
  ExecFloat.Capability.ofDirectKernel
    .mul Logarithmic.mul Plan.mulCertified Logarithmic.mul rfl

end FloatLib.Floats.ExecFloat.Logarithmic
