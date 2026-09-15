/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.NativeCandidates
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Type
public import FloatLib.Floats.ExecFloat.Core.Capability

/-!
# First-order dispatch for binary32 and binary64

Binary32 and binary64 use first-order operation instances that name their fixed-format
specializations. The public type constructor lives in `Configured.Type`, while the generic
table, word, limb, and baseline instances live in `Configured.Plan.Instances`.

Each instance names the fixed-format certificate it executes.
`Plan.selectCertified_binary32AddCandidates` and its siblings prove that the planner selects this
certificate under every `Policy`. The kernel that runs is therefore the proved kernel
`#float_info` reports, whichever `PolicyFor` instance is in scope.

The explicit guarded host operations remain in `Configured.NativeFPU.Unchecked`, but no compiler
substitution or certified candidate places them behind these capabilities.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.Binary

/--
Configured IEEE binary32 and binary64 operations name their first-order software kernels directly.

These instances are attached to the public parameterized families rather than to a storage-plan
constructor. Lean's typeclass index preserves `Binary.Family 8 23` and `Binary.Family 11 52`,
while it does not always unfold their computed `forKnownWidth` plans during instance search.
All six operations execute the proved fixed-format word kernels. Guarded host-primitive
experiments are separate functions and are not candidates until an exact equality proof exists.
-/
@[always_inline] instance (priority := 400) binary32AddCapability
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family 8 23)] :
    FloatLib.Floats.ExecFloat.Add (Family 8 23) where
  spec := Configured.Spec.add
  candidates := Configured.Plan.binary32AddCandidates _
  implementation := Configured.Plan.softwareAdd32Certified _
  implementation_is_selected :=
    (Configured.Plan.selectCertified_binary32AddCandidates planning.policy _).symm
  execute := Configured.Backend.wordAdd
  execute_eq_implementation := rfl

@[always_inline] instance (priority := 400) binary32SubCapability
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family 8 23)] :
    FloatLib.Floats.ExecFloat.Sub (Family 8 23) where
  spec := Configured.Spec.sub
  candidates := Configured.Plan.binary32SubCandidates _
  implementation := Configured.Plan.softwareSub32Certified _
  implementation_is_selected :=
    (Configured.Plan.selectCertified_binary32SubCandidates planning.policy _).symm
  execute := Configured.Backend.wordSub
  execute_eq_implementation := rfl

@[always_inline] instance (priority := 400) binary32MulCapability
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family 8 23)] :
    FloatLib.Floats.ExecFloat.Mul (Family 8 23) where
  spec := Configured.Spec.mul
  candidates := Configured.Plan.binary32MulCandidates _
  implementation := Configured.Plan.softwareMul32Certified _
  implementation_is_selected :=
    (Configured.Plan.selectCertified_binary32MulCandidates planning.policy _).symm
  execute := Configured.Backend.wordMul
  execute_eq_implementation := rfl

@[always_inline] instance (priority := 400) binary32DivCapability
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family 8 23)] :
    FloatLib.Floats.ExecFloat.Div (Family 8 23) where
  spec := Configured.Spec.div
  candidates := Configured.Plan.binary32DivCandidates _
  implementation := Configured.Plan.softwareDiv32Certified _
  implementation_is_selected :=
    (Configured.Plan.selectCertified_binary32DivCandidates planning.policy _).symm
  execute := Configured.Backend.wordDiv
  execute_eq_implementation := rfl

@[always_inline] instance (priority := 400) binary32SqrtCapability
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family 8 23)] :
    FloatLib.Floats.ExecFloat.Sqrt (Family 8 23) where
  spec := Configured.Spec.sqrt
  candidates := Configured.Plan.binary32SqrtCandidates _
  implementation := Configured.Plan.softwareSqrt32Certified _
  implementation_is_selected :=
    (Configured.Plan.selectCertified_binary32SqrtCandidates planning.policy _).symm
  execute := Configured.Backend.wordSqrt
  execute_eq_implementation := rfl

@[always_inline] instance (priority := 400) binary32FmaCapability
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family 8 23)] :
    FloatLib.Floats.ExecFloat.Fma (Family 8 23) where
  spec := Configured.Spec.fma
  candidates := Configured.Plan.binary32FmaCandidates _
  implementation := Configured.Plan.softwareFma32Certified _
  implementation_is_selected :=
    (Configured.Plan.selectCertified_binary32FmaCandidates planning.policy _).symm
  execute := Configured.Backend.wordFma
  execute_eq_implementation := rfl

@[always_inline] instance (priority := 400) binary64AddCapability
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family 11 52)] :
    FloatLib.Floats.ExecFloat.Add (Family 11 52) where
  spec := Configured.Spec.add
  candidates := Configured.Plan.binary64AddCandidates _
  implementation := Configured.Plan.softwareAdd64Certified _
  implementation_is_selected :=
    (Configured.Plan.selectCertified_binary64AddCandidates planning.policy _).symm
  execute := Configured.Backend.wordAdd
  execute_eq_implementation := rfl

@[always_inline] instance (priority := 400) binary64SubCapability
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family 11 52)] :
    FloatLib.Floats.ExecFloat.Sub (Family 11 52) where
  spec := Configured.Spec.sub
  candidates := Configured.Plan.binary64SubCandidates _
  implementation := Configured.Plan.softwareSub64Certified _
  implementation_is_selected :=
    (Configured.Plan.selectCertified_binary64SubCandidates planning.policy _).symm
  execute := Configured.Backend.wordSub
  execute_eq_implementation := rfl

@[always_inline] instance (priority := 400) binary64MulCapability
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family 11 52)] :
    FloatLib.Floats.ExecFloat.Mul (Family 11 52) where
  spec := Configured.Spec.mul
  candidates := Configured.Plan.binary64MulCandidates _
  implementation := Configured.Plan.softwareMul64Certified _
  implementation_is_selected :=
    (Configured.Plan.selectCertified_binary64MulCandidates planning.policy _).symm
  execute := Configured.Backend.wordMul
  execute_eq_implementation := rfl

@[always_inline] instance (priority := 400) binary64DivCapability
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family 11 52)] :
    FloatLib.Floats.ExecFloat.Div (Family 11 52) where
  spec := Configured.Spec.div
  candidates := Configured.Plan.binary64DivCandidates _
  implementation := Configured.Plan.softwareDiv64Certified _
  implementation_is_selected :=
    (Configured.Plan.selectCertified_binary64DivCandidates planning.policy _).symm
  execute := Configured.Backend.wordDiv
  execute_eq_implementation := rfl

@[always_inline] instance (priority := 400) binary64SqrtCapability
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family 11 52)] :
    FloatLib.Floats.ExecFloat.Sqrt (Family 11 52) where
  spec := Configured.Spec.sqrt
  candidates := Configured.Plan.binary64SqrtCandidates _
  implementation := Configured.Plan.softwareSqrt64Certified _
  implementation_is_selected :=
    (Configured.Plan.selectCertified_binary64SqrtCandidates planning.policy _).symm
  execute := Configured.Backend.wordSqrt
  execute_eq_implementation := rfl

@[always_inline] instance (priority := 400) binary64FmaCapability
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family 11 52)] :
    FloatLib.Floats.ExecFloat.Fma (Family 11 52) where
  spec := Configured.Spec.fma
  candidates := Configured.Plan.binary64FmaCandidates _
  implementation := Configured.Plan.softwareFma64Certified _
  implementation_is_selected :=
    (Configured.Plan.selectCertified_binary64FmaCandidates planning.policy _).symm
  execute := Configured.Backend.wordFma
  execute_eq_implementation := rfl

end FloatLib.Floats.ExecFloat.Binary
