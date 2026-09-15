/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Sqrt.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.SqrtWord.Proof
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Sqrt.Proof

/-!
# Correctness of square-root dispatch

`dispatch_eq_spec` combines the word and fixed-pair refinements to identify the complete
dispatcher with `Spec.sqrt`, including exceptional inputs. Runtime clients can import
`Sqrt.Runtime` separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace SqrtBackend

/-- Final structurally selected dispatch preserves square root. -/
theorem dispatch_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    dispatch x = Spec.sqrt x := by
  by_cases hfixed : FloatFormat.IsBinary32 fmt ∨ FloatFormat.IsBinary64 fmt
  · simp [dispatch, hfixed, word_eq_spec]
  by_cases hpair : NativePair.Eligible fmt
  · cases hfast : NativePair.sqrtNormal? x with
    | none =>
        simp [dispatch, hfixed, hpair, hfast, word_eq_spec]
    | some result =>
        have hrefines := NativePair.sqrtNormal_refines hpair x result hfast
        simp [dispatch, hfixed, hpair, hfast, hrefines]
  · simp [dispatch, hfixed, hpair, word_eq_spec]

end SqrtBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange
