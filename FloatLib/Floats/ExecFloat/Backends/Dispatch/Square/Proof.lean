/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Square.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Mul.Proof

/-!
# Refinement of unary binary squaring

Each single-operand decoder is related to the corresponding multiplication kernel on equal
operands. The existing multiplication proofs then supply exact rounding and equality of the
complete result encoding, including NaN signs and payloads.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.SquareBackend

/-- The single finite decode agrees with multiplication's two-operand decoder. -/
theorem finite_eq_mul {fmt : FloatFormat} (x : Model fmt) :
    finite? x = FiniteKernel.mulRuntime? x x := by
  simp only [finite?, FiniteKernel.mulRuntime?, FiniteKernel.withFinite_eq]
  cases FiniteKernel.decode? x <;> simp [FiniteKernel.mulFields]

/-- Generic squaring preserves multiplication's complete encoded result. -/
theorem generic_eq_mul {fmt : FloatFormat} (x : Model fmt) :
    generic x = MulBackend.generic x x := by
  unfold generic
  rw [finite_eq_mul]
  cases hfinite : FiniteKernel.mulRuntime? x x <;>
    simp [MulBackend.generic, hfinite]

/-- The binary32 unary kernel preserves the certified finite product. -/
theorem binary32_eq_mul (x : NativeBinary32.Value) :
    binary32? x = NativeBinary32.mulFiniteImpl? x x := by
  simp [binary32?, NativeBinary32.mulFiniteImpl?]

/-- The one-word unary kernel preserves both successful results and the decline sentinel. -/
theorem smallWord_eq_mul {fmt : FloatFormat} (x : Model fmt) :
    smallWord x = NativeSmallWordMul.mulNormalWord x x := by
  simp [smallWord, NativeSmallWordMul.mulNormalWord, or_left_comm, or_comm]

/-- The two-word unary kernel preserves the certified normal product. -/
theorem twoWord_eq_mul {fmt : FloatFormat} (x : Model fmt) :
    twoWord? x = NativeTwoWordMul.mulNormal? x x := by
  simp [twoWord?, NativeTwoWordMul.mulNormal?, NativeSmallWord.withNormalPair?,
    or_left_comm, or_comm]

/-- The fixed-pair unary kernel preserves the certified four-limb product. -/
theorem pair_eq_mul {fmt : FloatFormat} (x : Model fmt) :
    pair? x = NativePair.mulNormalLimb? x x := by
  simp [pair?, NativePair.mulNormalLimb?, or_left_comm, or_comm]

/-- Every unary dispatch branch preserves the existing multiplication dispatcher. -/
theorem dispatch_eq_mul {fmt : FloatFormat} (x : Model fmt) :
    dispatch x = MulBackend.word x x := by
  simp only [dispatch, MulBackend.word, binary32_eq_mul, twoWord_eq_mul, pair_eq_mul,
    smallWord_eq_mul, generic_eq_mul]
  rfl

/-- Binary squaring is the once-rounded exact product, with multiplication's encoding policy. -/
theorem dispatch_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    dispatch x = Spec.mul x x := by
  rw [dispatch_eq_mul, MulBackend.word_eq_spec]

end FloatLib.Floats.Formats.BinaryInterchange.Model.SquareBackend
