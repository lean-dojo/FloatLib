/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Compiled.Dispatch.FmaWord.Proof
public import FloatLib.Floats.ExecFloat.Backends.Compiled.FixedLimb.Pair.Fma.Proof
public import FloatLib.Floats.ExecFloat.Backends.Compiled.Generic.Kernel.Proof

/-!
# Correctness of fused multiply-add dispatch

`dispatch_eq_spec` combines the word and fixed-limb refinements to identify the complete dispatcher
with `Spec.fma`. On finite inputs that contract rounds the exact product-plus-addend once.
`Fma.Runtime` can be imported on its own.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace FmaBackend

/--
Final structurally selected dispatch equals `Spec.fma` for every descriptor and on every input,
exceptional values included.
-/
theorem dispatch_eq_spec {fmt : FloatFormat} (x y z : Model fmt) :
    dispatch x y z = Spec.fma x y z := by
  by_cases hfixed : FloatFormat.IsBinary32 fmt ∨ FloatFormat.IsBinary64 fmt
  · simp [dispatch, hfixed, word_eq_spec]
  by_cases hpair : NativePair.Eligible fmt
  · cases hfinite : FiniteKernel.fma? x y z with
    | none =>
        simp [dispatch, hfixed, hpair, NativePair.fmaFinite_eq hpair, hfinite, word_eq_spec]
    | some result =>
        have hresult := eq_spec_of_finite hfinite
        simp [dispatch, hfixed, hpair, NativePair.fmaFinite_eq hpair, hfinite, hresult]
  · simp [dispatch, hfixed, hpair, word_eq_spec]

end FmaBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange
