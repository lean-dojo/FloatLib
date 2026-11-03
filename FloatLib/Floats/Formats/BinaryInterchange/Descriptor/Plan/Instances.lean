/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Candidates
public import FloatLib.Floats.ExecFloat.Core.Capability

/-!
# Binary descriptor arithmetic capabilities

These instances register the complete certified candidate sets with the universal `ExecFloat`
interface. Public arithmetic projects the memoized selected implementation and does not rerun the
selector.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange

/--
Addition on the binary descriptor `format`: the reference is `Descriptor.Spec.add`, and the
planning policy in scope selects among the certified kernels of `Descriptor.Plan.addCandidates`.
-/
instance addCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)] :
    FloatLib.Floats.ExecFloat.Add (Descriptor format) where
  spec := Descriptor.Spec.add
  candidates := Descriptor.Plan.addCandidates format

/--
Subtraction on the binary descriptor `format`: the reference is `Descriptor.Spec.sub`, and the
planning policy in scope selects among the certified kernels of `Descriptor.Plan.subCandidates`.
-/
instance subCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)] :
    FloatLib.Floats.ExecFloat.Sub (Descriptor format) where
  spec := Descriptor.Spec.sub
  candidates := Descriptor.Plan.subCandidates format

/--
Multiplication on the binary descriptor `format`: the reference is `Descriptor.Spec.mul`, and the
planning policy in scope selects among the certified kernels of `Descriptor.Plan.mulCandidates`.
-/
instance mulCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)] :
    FloatLib.Floats.ExecFloat.Mul (Descriptor format) where
  spec := Descriptor.Spec.mul
  candidates := Descriptor.Plan.mulCandidates format

/--
Division on the binary descriptor `format`: the reference is `Descriptor.Spec.div`, and the
planning policy in scope selects among the certified kernels of `Descriptor.Plan.divCandidates`.
-/
instance divCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)] :
    FloatLib.Floats.ExecFloat.Div (Descriptor format) where
  spec := Descriptor.Spec.div
  candidates := Descriptor.Plan.divCandidates format

/--
Square root on the binary descriptor `format`: the reference is `Descriptor.Spec.sqrt`, and the
planning policy in scope selects among the certified kernels of `Descriptor.Plan.sqrtCandidates`.
-/
instance sqrtCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)] :
    FloatLib.Floats.ExecFloat.Sqrt (Descriptor format) where
  spec := Descriptor.Spec.sqrt
  candidates := Descriptor.Plan.sqrtCandidates format

/--
Fused multiply-add on the binary descriptor `format`: the reference is `Descriptor.Spec.fma`, and
the planning policy in scope selects among the certified kernels of
`Descriptor.Plan.fmaCandidates`.
-/
instance fmaCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)] :
    FloatLib.Floats.ExecFloat.Fma (Descriptor format) where
  spec := Descriptor.Spec.fma
  candidates := Descriptor.Plan.fmaCandidates format

end FloatLib.Floats.Formats.BinaryInterchange
