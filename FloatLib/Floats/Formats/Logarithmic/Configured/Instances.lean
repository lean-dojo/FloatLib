/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Form
public import FloatLib.Kernels.Execution.Instances -- shake: keep
public import FloatLib.Floats.Formats.Logarithmic.Configured.Plan

/-!
# Dispatch instance for exact logarithmic multiplication

With this instance in scope, ordinary `ExecFloat` multiplication on logarithmic values runs the
certified direct kernel, which xors the signs and adds the exponents.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Logarithmic

open FloatLib.Numerics

variable {radix : Radix}

/--
Exact logarithmic multiplication participates in ordinary `ExecFloat` dispatch: the planner
selects among the exact baseline and every candidate tagged `@[compiler_optimize]` for
`Logarithmic.mul`.
-/
@[always_inline] instance
    [planning : Backend.PolicyFor (Family radix)]
    [portfolio : Backend.Portfolio (Logarithmic.mul (radix := radix))] :
    ExecFloat.Mul (Family radix) :=
  ExecFloat.Capability.ofTagged .mul portfolio Plan.mulCertified Logarithmic.mul rfl

/--
Lean's kernel evaluates logarithmic multiplication as the sum of the two exponents: the reference
operation is the kernel operation.
-/
instance [Backend.PolicyFor (Family radix)]
    [Backend.Portfolio (Logarithmic.mul (radix := radix))] :
    KernelPath.DirectReference (Family radix) .mul where

end FloatLib.Floats.ExecFloat.Logarithmic
