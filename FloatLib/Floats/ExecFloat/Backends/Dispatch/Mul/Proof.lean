/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Mul.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Mul.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.TwoWordMul.Proof
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Multiplication.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Core.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.Dyadic
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Agreement
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Multiplication.Proof
/-!
# Correctness of multiplication backends

Every route through the multiplication dispatcher meets `Spec.mul`. Binary32, binary64, fixed-pair,
parameterized one-word, two-word, and generic implementations differ only in storage and execution
strategy. Each fast kernel may decline when its structural or finite-input preconditions fail, and
the proof shows both that accepted results refine `Spec.mul` and that every decline reaches
`generic`. `Mul.Runtime` loads without these theorems.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace MulBackend

/-- Compact generic multiplication equals the exact-dyadic `Spec.mul` on every input. -/
theorem generic_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    generic x y = Spec.mul x y := by
  unfold generic Spec.mul
  rw [FiniteKernel.mulRuntime_eq, FiniteKernel.mul_eq_spec]
  cases hx : toDyadic? x with
  | none =>
      cases toDyadic? y <;>
        simp <;>
        rfl
  | some dx =>
    cases hy : toDyadic? y with
      | none =>
          simp
          rfl
      | some dy =>
          by_cases hzero : dx.significand = 0 ∨ dy.significand = 0 <;>
            simp [hzero]

/-- A product that the finite kernel accepts is the specification product. -/
private theorem eq_spec_of_finite {fmt : FloatFormat} {x y product : Model fmt}
    (hfinite : FiniteKernel.mul? x y = some product) : product = Spec.mul x y := by
  simpa [generic, FiniteKernel.mulRuntime_eq, hfinite] using generic_eq_spec x y

/--
A kernel whose accepted products the finite kernel also returns, backed by a fallback equal to
`Spec.mul` for the inputs it declines, computes `Spec.mul`.
-/
private theorem fallback_eq_spec {fmt : FloatFormat} {x y fallback : Model fmt}
    {fast : Option (Model fmt)}
    (hfast : ∀ product, fast = some product → FiniteKernel.mul? x y = some product)
    (hfallback : fallback = Spec.mul x y) :
    (match (generalizing := false) fast with
      | some product => product
      | none => fallback) = Spec.mul x y := by
  cases fast with
  | none => exact hfallback
  | some product => exact eq_spec_of_finite (hfast product rfl)

/--
Multiplication through the native fixed-format and parameterized one- and two-word kernels
equals `Spec.mul` for every descriptor and on every input, exceptional values included.
-/
theorem word_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    word x y = Spec.mul x y := by
  unfold word
  split
  · rename_i h32
    have hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    subst fmt
    cases hx : toDyadic? x with
    | none =>
        cases hy : toDyadic? y <;>
          simp [Spec.mul, NativeBinary32.mulFiniteWord_eq, NativeBinary32.mulFinite_eq,
            generic_eq_spec, hx, hy]
    | some dx =>
        cases hy : toDyadic? y with
        | none =>
            simp [Spec.mul, NativeBinary32.mulFiniteWord_eq, NativeBinary32.mulFinite_eq,
              generic_eq_spec, hx, hy]
        | some dy =>
            by_cases hzero : dx.significand = 0 ∨ dy.significand = 0 <;>
              simp [Spec.mul, NativeBinary32.mulFiniteWord_eq, NativeBinary32.mulFinite_eq,
                hx, hy, hzero]
  split
  · rename_i h64
    have hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
    subst fmt
    refine fallback_eq_spec (NativeTwoWordMul.mulNormal_refines (by decide) x y) ?_
    dsimp only
    split
    · rename_i product hproduct
      exact eq_spec_of_finite (by
        simpa [NativeBinary64.mulFinite_eq] using
          NativeBinary64.mulNormalLimb_refines x y product hproduct)
    · exact generic_eq_spec x y
  split
  · exact fallback_eq_spec (NativePair.mulNormalLimb_refines ‹_› x y) (generic_eq_spec x y)
  split
  · rename_i heligible
    dsimp only
    split
    · exact generic_eq_spec x y
    · rename_i hdecline
      refine eq_spec_of_finite (NativeSmallWordMul.mulNormal_refines heligible x y _ ?_)
      rw [← NativeSmallWordMul.mulNormalWord_decode heligible]
      simp [hdecline]
  split
  · exact fallback_eq_spec (NativeTwoWordMul.mulNormal_refines ‹_› x y) (generic_eq_spec x y)
  · exact generic_eq_spec x y

end MulBackend

end Model

end FloatLib.Floats.Formats.BinaryInterchange
