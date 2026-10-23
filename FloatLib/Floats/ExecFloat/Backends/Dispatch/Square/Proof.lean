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

Each single-operand kernel equals the corresponding multiplication kernel on equal operands. The
multiplication proofs then supply correct rounding and the complete result encoding, including
NaN signs and payloads.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.SquareBackend

/-- Finite squaring with one decode equals the finite product `mulRuntime? x x`. -/
theorem finite_eq_mul {fmt : FloatFormat} (x : Model fmt) :
    finite? x = FiniteKernel.mulRuntime? x x := by
  simp only [finite?, FiniteKernel.mulRuntime?, FiniteKernel.withFinite_eq]
  cases FiniteKernel.decode? x <;> simp [FiniteKernel.mulFields]

/-- Generic squaring equals generic multiplication of `x` by itself. -/
theorem generic_eq_mul {fmt : FloatFormat} (x : Model fmt) :
    generic x = MulBackend.generic x x := by
  unfold generic
  rw [finite_eq_mul]
  cases hfinite : FiniteKernel.mulRuntime? x x <;>
    simp [MulBackend.generic, hfinite]

/-- Binary32 squaring agrees with `NativeBinary32.mulFiniteWord? x x`. -/
theorem binary32_eq_mul (x : NativeBinary32.Value) :
    binary32? x = NativeBinary32.mulFiniteWord? x x := by
  simp [binary32?, NativeBinary32.mulFiniteWord?]

/-- One-word squaring agrees with `mulNormalWord x x`, decline sentinel included. -/
theorem smallWord_eq_mul {fmt : FloatFormat} (x : Model fmt) :
    smallWord x = NativeSmallWordMul.mulNormalWord x x := by
  simp [smallWord, NativeSmallWordMul.mulNormalWord, or_left_comm, or_comm]

/-- Two-word squaring agrees with `NativeTwoWordMul.mulNormal? x x`. -/
theorem twoWord_eq_mul {fmt : FloatFormat} (x : Model fmt) :
    twoWord? x = NativeTwoWordMul.mulNormal? x x := by
  unfold twoWord? NativeTwoWordMul.mulNormal? NativeTwoWordMul.mulNormalWord?
    NativeSmallWord.withNormalPairWord? NativeTwoWordMul.roundNormalProduct?
  dsimp only
  cases hzero : (NativeSmallWord.exponentField fmt (NativeSmallWord.toWord x) == 0) <;>
    cases hmask : (NativeSmallWord.exponentField fmt (NativeSmallWord.toWord x) ==
      NativeSmallWord.exponentMask fmt) <;>
    simp

/-- Fixed-pair squaring agrees with the four-limb product `mulNormalLimb? x x`. -/
theorem pair_eq_mul {fmt : FloatFormat} (x : Model fmt) :
    pair? x = NativePair.mulNormalLimb? x x := by
  simp [pair?, NativePair.mulNormalLimb?, NativePair.mulNormalWords?, NativePair.roundNormalLimb?,
    NativePair.roundNormalProduct?, apply_ite (Option.map (NativePair.ofWords fmt)), or_left_comm,
    or_comm]

/-- Squaring dispatch agrees with the multiplication dispatcher on `x * x`, branch by branch. -/
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
