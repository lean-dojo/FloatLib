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

Every route through the multiplication dispatcher meets `Spec.mul`: binary32, binary64,
fixed-pair, parameterized one-word, two-word, and generic implementations differ only in storage
and execution strategy.

Each fast kernel is allowed to decline when its structural or finite-input preconditions fail.
The proof shows that successful results are exact refinements and that every decline reaches the
single generic specification-preserving path. Runtime clients can import `Mul.Runtime` without
loading these theorems.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace MulBackend

/-- Compact generic multiplication preserves the public exact-dyadic operation. -/
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

/--
The native fixed-format and parameterized one- and two-word dispatches preserve multiplication.
-/
theorem word_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    word x y = Spec.mul x y := by
  by_cases h32 : FloatFormat.IsBinary32 fmt
  · have hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    subst fmt
    cases hx : toDyadic? x with
    | none =>
        cases hy : toDyadic? y <;>
          simp [word, Spec.mul, NativeBinary32.mulFiniteImpl_eq,
            NativeBinary32.mulFinite_eq, generic_eq_spec, hx, hy]
    | some dx =>
        cases hy : toDyadic? y with
        | none =>
            simp [word, Spec.mul, NativeBinary32.mulFiniteImpl_eq,
              NativeBinary32.mulFinite_eq, generic_eq_spec, hx, hy]
        | some dy =>
            by_cases hzero : dx.significand = 0 ∨ dy.significand = 0 <;>
              simp [word, Spec.mul, NativeBinary32.mulFiniteImpl_eq,
                NativeBinary32.mulFinite_eq, hx, hy, hzero]
  · by_cases h64 : FloatFormat.IsBinary64 fmt
    · have hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
      subst fmt
      cases htwoWord : NativeTwoWordMul.mulNormal? x y with
      | some product =>
          have hrefines :=
            NativeTwoWordMul.mulNormal_refines (by decide) x y product htwoWord
          have hproduct : product = Spec.mul x y := by
            calc
              product = generic x y := by
                simp [generic, FiniteKernel.mulRuntime_eq, hrefines]
              _ = Spec.mul x y := generic_eq_spec x y
          simp [word, h32, htwoWord, hproduct]
      | none =>
          cases hfast : NativeBinary64.mulNormalLimb? x y with
          | none =>
              simp [word, h32, htwoWord, hfast, generic_eq_spec]
          | some product =>
              have hrefines :=
                NativeBinary64.mulNormalLimb_refines x y product hfast
              have hfinite : FiniteKernel.mul? x y = some product := by
                rw [← NativeBinary64.mulFiniteImpl_eq]
                exact hrefines
              have hproduct : product = Spec.mul x y := by
                calc
                  product = generic x y := by
                    simp [generic, FiniteKernel.mulRuntime_eq, hfinite]
                  _ = Spec.mul x y := generic_eq_spec x y
              simp [word, h32, htwoWord, hfast, hproduct]
    · by_cases hpair : NativePair.Eligible fmt
      · cases hfast : NativePair.mulNormalLimb? x y with
        | none =>
            simp [word, h32, h64, hpair, hfast, generic_eq_spec]
        | some product =>
            have hrefines :=
              NativePair.mulNormalLimb_refines hpair x y product hfast
            have hproduct : product = Spec.mul x y := by
              calc
                product = generic x y := by
                  simp [generic, FiniteKernel.mulRuntime_eq, hrefines]
                _ = Spec.mul x y := generic_eq_spec x y
            simp [word, h32, h64, hpair, hfast, hproduct]
      · by_cases heligible : NativeSmallWordMul.Eligible fmt
        · let product := NativeSmallWordMul.mulNormalWord x y
          by_cases hdecline :
              product == NativeSmallWordMul.declineWord
          · have hdecode :=
              NativeSmallWordMul.mulNormalWord_decode heligible x y
            have hnone :
                NativeSmallWordMul.mulNormal? x y = none := by
              simpa [product, hdecline] using hdecode.symm
            simp [word, h32, h64, hpair, heligible, product, hdecline,
              generic_eq_spec]
          · have hdecode :=
              NativeSmallWordMul.mulNormalWord_decode heligible x y
            have hsome :
                NativeSmallWordMul.mulNormal? x y =
                  some (NativeSmallWord.ofWord product) := by
              simpa [product, hdecline] using hdecode.symm
            have hrefines :=
              NativeSmallWordMul.mulNormal_refines heligible x y
                (NativeSmallWord.ofWord product) hsome
            have hproduct :
                NativeSmallWord.ofWord product = Spec.mul x y := by
              calc
                NativeSmallWord.ofWord product = generic x y := by
                  simp [generic, FiniteKernel.mulRuntime_eq, hrefines]
                _ = Spec.mul x y := generic_eq_spec x y
            simp [word, h32, h64, hpair, heligible, product, hdecline,
              hproduct]
        · by_cases htwoWord : NativeTwoWordMul.Eligible fmt
          · cases hfast : NativeTwoWordMul.mulNormal? x y with
            | none =>
                simp [word, h32, h64, hpair, heligible, htwoWord, hfast,
                  generic_eq_spec]
            | some product =>
                have hrefines :=
                  NativeTwoWordMul.mulNormal_refines htwoWord x y product hfast
                have hproduct : product = Spec.mul x y := by
                  calc
                    product = generic x y := by
                      simp [generic, FiniteKernel.mulRuntime_eq, hrefines]
                    _ = Spec.mul x y := generic_eq_spec x y
                simp [word, h32, h64, hpair, heligible, htwoWord, hfast,
                  hproduct]
          · simp [word, generic_eq_spec, h32, h64, hpair, heligible,
              htwoWord]

end MulBackend

end Model

end FloatLib.Floats.Formats.BinaryInterchange
