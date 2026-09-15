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

instance addCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)] :
    FloatLib.Floats.ExecFloat.Add (Descriptor format) where
  spec := Descriptor.Spec.add
  candidates := Descriptor.Plan.addCandidates format

instance subCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)] :
    FloatLib.Floats.ExecFloat.Sub (Descriptor format) where
  spec := Descriptor.Spec.sub
  candidates := Descriptor.Plan.subCandidates format

instance mulCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)] :
    FloatLib.Floats.ExecFloat.Mul (Descriptor format) where
  spec := Descriptor.Spec.mul
  candidates := Descriptor.Plan.mulCandidates format

instance divCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)] :
    FloatLib.Floats.ExecFloat.Div (Descriptor format) where
  spec := Descriptor.Spec.div
  candidates := Descriptor.Plan.divCandidates format

instance sqrtCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)] :
    FloatLib.Floats.ExecFloat.Sqrt (Descriptor format) where
  spec := Descriptor.Spec.sqrt
  candidates := Descriptor.Plan.sqrtCandidates format

instance fmaCapability (format : FloatFormat)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Descriptor format)] :
    FloatLib.Floats.ExecFloat.Fma (Descriptor format) where
  spec := Descriptor.Spec.fma
  candidates := Descriptor.Plan.fmaCandidates format

end FloatLib.Floats.Formats.BinaryInterchange
