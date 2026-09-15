/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.FmaWord.Runtime
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Fma.Runtime

/-!
# Executable fused multiply-add dispatch

The dispatcher adds the fixed-limb pair-layout route to the smaller word-specialized kernels
without importing their refinement proofs. The pair route contains a complete finite candidate
chain; the dispatcher handles only exceptional inputs after that chain returns `none`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace FmaBackend

/-- Use the fixed-limb FMA when eligible, otherwise use the word dispatcher. -/
@[inline] def dispatch {fmt : FloatFormat}
    (x y z : Model fmt) : Model fmt :=
  -- Keep one fallback call to `word`. The fixed-format guard lets specialization discard
  -- the pair probe for binary32 and binary64, neither of which is pair-eligible.
  let fast : Option (Model fmt) :=
    if FloatFormat.IsBinary32 fmt ∨ FloatFormat.IsBinary64 fmt then none
    else if _hpair : NativePair.Eligible fmt then NativePair.fmaFinite? x y z
    else none
  match fast with
  | some result => result
  | none => word x y z

end FmaBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange
