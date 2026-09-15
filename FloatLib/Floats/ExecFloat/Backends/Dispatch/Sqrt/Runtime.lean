/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.SqrtWord.Runtime
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Sqrt.Runtime

/-!
# Executable square-root dispatch

The dispatcher adds the certified pair-layout route to the smaller word-specialized kernels
without importing their refinement proofs. It alone selects the exact word baseline when the
partial pair kernel declines.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace SqrtBackend

/--
Use the fixed-pair square-root kernel when eligible, otherwise use the word dispatcher.

The partial pair result has one fallback call to `word`. The fixed-format guard lets
specialization discard the pair probe for binary32 and binary64; neither is pair-eligible.
-/
@[inline] def dispatch {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  let fast : Option (Model fmt) :=
    if FloatFormat.IsBinary32 fmt ∨ FloatFormat.IsBinary64 fmt then none
    else if _hpair : NativePair.Eligible fmt then NativePair.sqrtNormal? x
    else none
  match fast with
  | some result => result
  | none => word x

end SqrtBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange
