/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Core.Proof

/-!
# Correctness of direct-carrier software FMA

These theorems connect the binary32 and binary64 FMA adapters in `NativeFPU.Runtime` to the
independent configured specification. The adapters use proved fixed-word software arithmetic in
both logical and compiled execution. Host experiments live in the separately imported
`NativeFPU.Unchecked` module and cannot enter this proof surface transitively.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU

/-! ## Binary32 -/

/-- The direct-carrier binary32 FMA agrees with the independent configured specification. -/
theorem softwareFma32_eq_spec
    {width_le : FloatFormat.binary32.bitWidth ≤ 32}
    (left right addend : Binary32Value width_le) :
    softwareFma32 left right addend = Spec.fma left right addend :=
  Backend.wordFma_eq_spec left right addend

/-! ## Binary64 -/

/-- The direct-carrier binary64 FMA agrees with the independent configured specification. -/
theorem softwareFma64_eq_spec
    {width_le : FloatFormat.binary64.bitWidth ≤ 64}
    (left right addend : Binary64Value width_le) :
    softwareFma64 left right addend = Spec.fma left right addend :=
  Backend.wordFma_eq_spec left right addend

end FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU
