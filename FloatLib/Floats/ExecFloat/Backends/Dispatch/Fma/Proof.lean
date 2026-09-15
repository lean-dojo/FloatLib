/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Fma.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.FmaWord.Proof
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Fma.Proof

/-!
# Correctness of fused multiply-add dispatch

`dispatch_eq_spec` combines the word and fixed-limb refinements to identify the complete
dispatcher with `Spec.fma`. For finite inputs, this contract rounds the exact product-plus-addend
once. Runtime clients can import `Fma.Runtime` separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace FmaBackend

/-- Final structurally selected dispatch preserves fused multiply-add. -/
theorem dispatch_eq_spec {fmt : FloatFormat} (x y z : Model fmt) :
    dispatch x y z = Spec.fma x y z := by
  by_cases hfixed : FloatFormat.IsBinary32 fmt ∨ FloatFormat.IsBinary64 fmt
  · simp [dispatch, hfixed, word_eq_spec]
  by_cases hpair : NativePair.Eligible fmt
  · cases hfinite : FiniteKernel.fma? x y z with
    | none =>
        simp [dispatch, hfixed, hpair, NativePair.fmaFinite_eq hpair, hfinite, word_eq_spec]
    | some result =>
        have hresult : result = Spec.fma x y z := by
          calc
            result = generic x y z := by
              simp [generic, FiniteKernel.fmaRuntimeFlat_eq,
                FiniteKernel.fmaRuntime_eq, hfinite]
            _ = Spec.fma x y z := generic_eq_spec x y z
        simp [dispatch, hfixed, hpair, NativePair.fmaFinite_eq hpair, hfinite, hresult]
  · simp [dispatch, hfixed, hpair, word_eq_spec]

end FmaBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange
