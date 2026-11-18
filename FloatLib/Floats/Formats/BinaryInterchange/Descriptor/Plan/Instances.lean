/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.Execution.Capability
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Candidates

/-!
# Binary descriptor arithmetic capabilities

These instances give every binary descriptor its six capabilities through the universal
`ExecFloat` interface. Each one selects among the width-generic baseline and every candidate
tagged `@[compiler_optimize]` for the descriptor operation: the tables and structural kernels of
`Descriptor.Plan.Candidates`, and any candidate that another imported module tags. Public
arithmetic calls the baseline directly when the planner keeps it, and otherwise the memoized
selected implementation, and does not rerun the selector.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange

/--
Addition on the binary descriptor `format`. The reference is `Descriptor.Spec.add`, and
the planning policy in scope selects among `Descriptor.Plan.addGeneric` and the tagged
candidates.
-/
instance addCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)]
    [portfolio : FloatLib.Floats.ExecFloat.Backend.Portfolio (@Descriptor.Spec.add format)] :
    FloatLib.Floats.ExecFloat.Add (Descriptor format) :=
  FloatLib.Floats.ExecFloat.Capability.ofTagged .add portfolio
    (Descriptor.Plan.addGeneric format) Descriptor.Backend.genericAdd rfl

/--
Subtraction on the binary descriptor `format`. The reference is `Descriptor.Spec.sub`, and
the planning policy in scope selects among `Descriptor.Plan.subGeneric` and the tagged
candidates.
-/
instance subCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)]
    [portfolio : FloatLib.Floats.ExecFloat.Backend.Portfolio (@Descriptor.Spec.sub format)] :
    FloatLib.Floats.ExecFloat.Sub (Descriptor format) :=
  FloatLib.Floats.ExecFloat.Capability.ofTagged .sub portfolio
    (Descriptor.Plan.subGeneric format) Descriptor.Backend.genericSub rfl

/--
Multiplication on the binary descriptor `format`. The reference is `Descriptor.Spec.mul`, and
the planning policy in scope selects among `Descriptor.Plan.mulGeneric` and the tagged
candidates.
-/
instance mulCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)]
    [portfolio : FloatLib.Floats.ExecFloat.Backend.Portfolio (@Descriptor.Spec.mul format)] :
    FloatLib.Floats.ExecFloat.Mul (Descriptor format) :=
  FloatLib.Floats.ExecFloat.Capability.ofTagged .mul portfolio
    (Descriptor.Plan.mulGeneric format) Descriptor.Backend.genericMul rfl

/--
Division on the binary descriptor `format`. The reference is `Descriptor.Spec.div`, and
the planning policy in scope selects among `Descriptor.Plan.divGeneric` and the tagged
candidates.
-/
instance divCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)]
    [portfolio : FloatLib.Floats.ExecFloat.Backend.Portfolio (@Descriptor.Spec.div format)] :
    FloatLib.Floats.ExecFloat.Div (Descriptor format) :=
  FloatLib.Floats.ExecFloat.Capability.ofTagged .div portfolio
    (Descriptor.Plan.divGeneric format) Descriptor.Backend.genericDiv rfl

/--
Square root on the binary descriptor `format`. The reference is `Descriptor.Spec.sqrt`, and
the planning policy in scope selects among `Descriptor.Plan.sqrtGeneric` and the tagged
candidates.
-/
instance sqrtCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)]
    [portfolio : FloatLib.Floats.ExecFloat.Backend.Portfolio (@Descriptor.Spec.sqrt format)] :
    FloatLib.Floats.ExecFloat.Sqrt (Descriptor format) :=
  FloatLib.Floats.ExecFloat.Capability.ofTagged .sqrt portfolio
    (Descriptor.Plan.sqrtGeneric format) Descriptor.Backend.genericSqrt rfl

/--
Fused multiply-add on the binary descriptor `format`. The reference is `Descriptor.Spec.fma`, and
the planning policy in scope selects among `Descriptor.Plan.fmaGeneric` and the tagged
candidates.
-/
instance fmaCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)]
    [portfolio : FloatLib.Floats.ExecFloat.Backend.Portfolio (@Descriptor.Spec.fma format)] :
    FloatLib.Floats.ExecFloat.Fma (Descriptor format) :=
  FloatLib.Floats.ExecFloat.Capability.ofTagged .fma portfolio
    (Descriptor.Plan.fmaGeneric format) Descriptor.Backend.genericFma rfl

end FloatLib.Floats.Formats.BinaryInterchange
