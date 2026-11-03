/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.FmaWord.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.Dyadic
import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
import FloatLib.Floats.ExecFloat.Backends.Word.Small.Finite.Proof
import FloatLib.Floats.ExecFloat.Backends.Word.Small.Fma.Proof
import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Agreement
import FloatLib.Floats.ExecFloat.Backends.Word.Full.Fma.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Classification
import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Fma.Proof
/-!
# Correctness of word-specialized fused multiply-add dispatch

Fused multiply-add forms the exact product-plus-addend before one rounding step. The refinements
here establish that contract for the binary32, binary64, one-word `UInt64`, and native-storage
kernels.

Accepted kernel results and the generic fallback all agree with `Spec.fma`, including its
exceptional-value policy.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace FmaBackend

/-- Compact generic FMA equals the exact-dyadic `Spec.fma` on every input. -/
theorem generic_eq_spec {fmt : FloatFormat}
    (x y z : Model fmt) :
    generic x y z = Spec.fma x y z := by
  unfold generic Spec.fma
  rw [FiniteKernel.fmaRuntimeFlat_eq, FiniteKernel.fmaRuntime_eq]
  rw [FiniteKernel.fma_eq_spec]
  cases hx : toDyadic? x with
  | none =>
      simp
      rfl
  | some dx =>
    cases hy : toDyadic? y with
    | none =>
        simp
        rfl
    | some dy =>
      cases hz : toDyadic? z with
      | none =>
          simp
          rfl
      | some dz =>
        have hxNaN := isNaN_eq_false_of_toDyadic?_some hx
        have hyNaN := isNaN_eq_false_of_toDyadic?_some hy
        have hzNaN := isNaN_eq_false_of_toDyadic?_some hz
        have hxSNaN := isSNaN_eq_false_of_toDyadic?_some hx
        have hySNaN := isSNaN_eq_false_of_toDyadic?_some hy
        have hzSNaN := isSNaN_eq_false_of_toDyadic?_some hz
        have hxInf := isInf_eq_false_of_toDyadic?_some hx
        have hyInf := isInf_eq_false_of_toDyadic?_some hy
        have hzInf := isInf_eq_false_of_toDyadic?_some hz
        simp [chooseNaN3, hxNaN, hyNaN, hzNaN, hxSNaN, hySNaN,
          hzSNaN, hxInf, hyInf, hzInf]

/-- A result that the finite kernel accepts is the specification result. -/
theorem eq_spec_of_finite {fmt : FloatFormat} {x y z result : Model fmt}
    (hfinite : FiniteKernel.fma? x y z = some result) : result = Spec.fma x y z := by
  rw [← generic_eq_spec]
  simp [generic, FiniteKernel.fmaRuntimeFlat_eq, FiniteKernel.fmaRuntime_eq, hfinite]

/--
The binary32 finite kernel agrees with the generic finite kernel `FiniteKernel.fma?`.

As a named lemma it keeps the exceptional-value case split out of the dispatcher proof.
-/
private theorem binary32_fmaFiniteWord_eq_kernel
    (x y z : Model FloatFormat.binary32) :
    NativeBinary32.fmaFiniteWord? x y z = FiniteKernel.fma? x y z := by
  rw [NativeBinary32.fmaFiniteWord_eq, NativeBinary32.fmaFinite_eq,
    FiniteKernel.fma_eq_spec]
  rfl

/--
A kernel whose accepted results the finite kernel also returns, backed by a fallback equal to
`Spec.fma` for the inputs it declines, computes `Spec.fma`.
-/
private theorem fallback_eq_spec {fmt : FloatFormat} {x y z fallback : Model fmt}
    {fast : Option (Model fmt)}
    (hfast : ∀ result, fast = some result → FiniteKernel.fma? x y z = some result)
    (hfallback : fallback = Spec.fma x y z) :
    (match (generalizing := false) fast with
      | some result => result
      | none => fallback) = Spec.fma x y z := by
  cases fast with
  | none => exact hfallback
  | some result => exact eq_spec_of_finite (hfast result rfl)

/--
Word-specialized fused multiply-add equals `Spec.fma` for every descriptor and on every input,
exceptional values included.
-/
theorem word_eq_spec {fmt : FloatFormat} (x y z : Model fmt) :
    word x y z = Spec.fma x y z := by
  unfold word
  split
  · rename_i h32
    have hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    subst fmt
    dsimp only
    split
    · rename_i result hresult
      exact eq_spec_of_finite (by
        simpa [binary32_fmaFiniteWord_eq_kernel] using hresult)
    · exact generic_eq_spec x y z
  split
  · rename_i h64
    have hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
    subst fmt
    dsimp only
    split
    · rename_i result hresult
      exact eq_spec_of_finite (by simpa [NativeBinary64.fmaFinite_eq] using hresult)
    · exact generic_eq_spec x y z
  split
  · rename_i hsmall
    have hstorage : NativeSmallWord.StorageEligible fmt := ⟨hsmall.1, hsmall.2.1⟩
    exact fallback_eq_spec (NativeSmallWordFma.fmaFinite_refines hsmall x y z)
      (fallback_eq_spec
        (fun result hresult => by rwa [NativeSmallWordFinite.fmaFinite_eq hstorage] at hresult)
        (generic_eq_spec x y z))
  split
  · exact fallback_eq_spec
      (fun result hresult => by rwa [NativeSmallWordFinite.fmaFinite_eq ‹_›] at hresult)
      (generic_eq_spec x y z)
  · exact generic_eq_spec x y z

end FmaBackend

end Model

end FloatLib.Floats.Formats.BinaryInterchange
