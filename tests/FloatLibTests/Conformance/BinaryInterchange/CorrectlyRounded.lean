/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.ExpLog

/-!
# Kernel-checked correctly rounded exponentials

The smallest IEEE descriptor `ieee 2 1` has the finite magnitudes `0`, `1/2`, `1`, `3/2`, `2` and
`3`, and nearest-even rounding overflows from `7/2`. Its approximation kernel rounds
`exp (3/2) ≈ 4.48` to `+∞`, so `exp x - 1` formed from it is `+∞` too. The correctly rounded
`expMinus1` returns `3`, both from its enclosure search and, with an empty budget, from exact
comparisons alone, on the descriptor model and on the configured type `ExecFloat.Binary 2 1`.
`toReal_expMinus1_eq_roundAt` states that `3` is the rounding of `exp (3/2) - 1`.

In binary32, `exp 89 ≈ 4.49e38` overflows while `exp 89 * 0.5` does not. Rounding the
exponential first gives `+∞` for that product and a NaN for a zero weight. The weighted
exponential returns the finite product and a signed zero. `exp_eq_nativeOverflow` states that the
exponential itself returns `+∞` there.

At the least subnormal of binary32 and bfloat16, the sign theorems show that `expMinus1` of the
negative value is negative and `logPlus1` of the positive value is positive, so neither rounds to
zero. The logarithm of `-1` is not finite, as for every finite input outside the domain.

The `MathFunctions` instances keep the approximation kernels. A client opts in to the correctly
rounded `exp` and `log` with the scope `CorrectlyRoundedMath`, or by passing the dictionary
`CorrectlyRounded.mathFunctions` by name, here as the parent of another class's instance.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals

/-- The value `3/2` of `ieee 2 1`, whose `exp x - 1` rounds to `3`. -/
abbrev tinyThreeHalves : Model (.ieee 2 1) := Model.ofNatBits 3

example : (Model.exp tinyThreeHalves).toNatBits = 6 := by decide +kernel

example : (CorrectlyRounded.expMinus1 tinyThreeHalves).toNatBits = 5 := by decide +kernel

example :
    (CorrectlyRounded.expMinus1 tinyThreeHalves (budget := { maxAttempts := 0 })).toNatBits = 5 := by
  decide +kernel

/-- The configured type of `ieee 2 1`. -/
abbrev Tiny := ExecFloat.Binary 2 1

example : ExecFloat.Binary.toNatBits
    (ExecFloat.Binary.CorrectlyRounded.expMinus1 (ExecFloat.Binary.ofNatBits 3 : Tiny)) = 5 := by
  decide +kernel

example : ExecFloat.Binary.toNatBits (ExecFloat.Binary.CorrectlyRounded.expMinus1
    (ExecFloat.Binary.ofNatBits 3 : Tiny) (budget := { maxAttempts := 0 })) = 5 := by
  decide +kernel

/-- The finite result `3` of `ieee 2 1` is the nearest-even rounding of `exp (3/2) - 1`. -/
theorem toReal_expMinus1_tinyThreeHalves :
    Model.toReal (CorrectlyRounded.expMinus1 tinyThreeHalves) =
      Model.roundAt (.ieee 2 1) (Real.exp (3 / 2) - 1) := by
  have hinput : Model.toReal tinyThreeHalves = 3 / 2 := by
    rw [Model.Algebraic.toReal_of_toRat?_eq_some (q := 3 / 2) (by decide +kernel)]
    norm_num
  have hexp : Real.exp ((3 / 2 : ℚ) : ℝ) < ((9 / 2 : ℚ) : ℝ) := by
    have h := FloatLib.Numerics.ElementaryComparison.compareExp_eq_real (3 / 2) (9 / 2)
    rw [show FloatLib.Numerics.ElementaryComparison.compareExp (3 / 2) (9 / 2) = .lt by
      decide +kernel] at h
    exact (cmp_eq_lt_iff _ _).mp h.symm
  have hthreshold : Certified.overflowThreshold (.ieee 2 1) = 7 / 2 := by decide +kernel
  rw [← hinput]
  apply CorrectlyRounded.toReal_expMinus1_eq_roundAt (by decide) (by decide +kernel)
  rw [hinput, hthreshold]
  push_cast at hexp ⊢
  linarith

/-- Encodings `89` and `0.5` of binary32. -/
abbrev eightyNine : Model .binary32 := Model.ofNatBits 0x42b20000

example : (Model.mul (Model.exp eightyNine) (Model.ofNatBits 0x3f000000)).toNatBits =
    0x7f800000 := by decide +kernel

example : (CorrectlyRounded.expMul eightyNine (Model.ofNatBits 0x3f000000)).toNatBits =
    0x7f28e166 := by decide +kernel

example : (Model.mul (Model.exp eightyNine) (Model.posZero .binary32)).toNatBits =
    0x7fc00000 := by decide +kernel

example : CorrectlyRounded.expMul eightyNine (Model.posZero .binary32) = Model.posZero _ := by
  decide +kernel

example : CorrectlyRounded.expMul eightyNine (Model.negZero .binary32) = Model.negZero _ := by
  decide +kernel

example : (CorrectlyRounded.exp (Model.ofNatBits (fmt := .binary32) 0x3f800000)).toNatBits =
    0x402df854 := by decide +kernel

example : (CorrectlyRounded.log (Model.ofNatBits (fmt := .binary32) 0x40000000)).toNatBits =
    0x3f317218 := by decide +kernel

/-- The exponential of `89` is beyond the binary32 range, and it returns `+∞`. -/
theorem exp_eightyNine_overflows :
    CorrectlyRounded.exp eightyNine = Model.nativeOverflow .binary32 false := by
  have hinput : Model.toReal eightyNine = 89 := by
    rw [Model.Algebraic.toReal_of_toRat?_eq_some (q := 89) (by decide +kernel)]
    norm_num
  have hthreshold : Certified.overflowThreshold .binary32 =
      340282356779733661637539395458142568448 := by decide +kernel
  have hexp : ((340282356779733661637539395458142568448 : ℚ) : ℝ) < Real.exp ((89 : ℚ) : ℝ) := by
    have h := FloatLib.Numerics.ElementaryComparison.compareExp_eq_real 89
      340282356779733661637539395458142568448
    rw [show FloatLib.Numerics.ElementaryComparison.compareExp 89
      340282356779733661637539395458142568448 = .gt by decide +kernel] at h
    exact (cmp_eq_gt_iff _ _).mp h.symm
  refine CorrectlyRounded.exp_eq_nativeOverflow (by decide) (by decide) ?_
  rw [hinput, hthreshold]
  push_cast at hexp ⊢
  exact hexp.le

example : (CorrectlyRounded.exp eightyNine).toNatBits = 0x7f800000 := by decide +kernel

/-! ## Signs at the least subnormal -/

/-- Binary32 `-2⁻¹⁴⁹`, the negative least subnormal. -/
abbrev negLeastSubnormal32 : Model .binary32 := Model.ofNatBits 0x80000001
/-- Binary32 `2⁻¹⁴⁹`, the least subnormal. -/
abbrev leastSubnormal32 : Model .binary32 := Model.ofNatBits 0x00000001
/-- Bfloat16 `-2⁻¹³³`, the negative least subnormal. -/
abbrev negLeastSubnormal16 : Model .bfloat16 := Model.ofNatBits 0x8001
/-- Bfloat16 `2⁻¹³³`, the least subnormal. -/
abbrev leastSubnormal16 : Model .bfloat16 := Model.ofNatBits 0x0001

/-- `expMinus1` of the negative least subnormal of binary32 is negative. -/
theorem expMinus1_lt_zero_binary32 :
    Model.toReal (CorrectlyRounded.expMinus1 negLeastSubnormal32) < 0 :=
  CorrectlyRounded.toReal_expMinus1_lt_zero (by decide) (by decide) (by
    rw [Model.Algebraic.toReal_of_toRat?_eq_some (q := -(2⁻¹ ^ 149)) (by decide +kernel)]
    norm_num)

/-- `expMinus1` of the negative least subnormal of bfloat16 is negative. -/
theorem expMinus1_lt_zero_bfloat16 :
    Model.toReal (CorrectlyRounded.expMinus1 negLeastSubnormal16) < 0 :=
  CorrectlyRounded.toReal_expMinus1_lt_zero (by decide) (by decide) (by
    rw [Model.Algebraic.toReal_of_toRat?_eq_some (q := -(2⁻¹ ^ 133)) (by decide +kernel)]
    norm_num)

/-- `logPlus1` of the least subnormal is positive in binary32 and bfloat16. -/
theorem logPlus1_pos_leastSubnormal :
    0 < Model.toReal (CorrectlyRounded.logPlus1 leastSubnormal32) ∧
      0 < Model.toReal (CorrectlyRounded.logPlus1 leastSubnormal16) :=
  ⟨CorrectlyRounded.toReal_logPlus1_pos (by decide) (by decide) (by
      rw [Model.Algebraic.toReal_of_toRat?_eq_some (q := 2⁻¹ ^ 149) (by decide +kernel)]
      norm_num),
    CorrectlyRounded.toReal_logPlus1_pos (by decide) (by decide) (by
      rw [Model.Algebraic.toReal_of_toRat?_eq_some (q := 2⁻¹ ^ 133) (by decide +kernel)]
      norm_num)⟩

/-- Both functions return the least subnormal of the sign of their input. -/
example : (CorrectlyRounded.expMinus1 negLeastSubnormal32).toNatBits = 0x80000001 ∧
    (CorrectlyRounded.expMinus1 negLeastSubnormal16).toNatBits = 0x8001 ∧
    (CorrectlyRounded.logPlus1 leastSubnormal32).toNatBits = 0x00000001 ∧
    (CorrectlyRounded.logPlus1 leastSubnormal16).toNatBits = 0x0001 := by
  decide +kernel

/-! ## The domain -/

/-- Binary32 `-1`. -/
abbrev minusOne32 : Model .binary32 := Model.ofNatBits 0xbf800000

/-- The logarithm of `-1` is not finite. -/
example : Model.isFinite (CorrectlyRounded.log minusOne32) = false :=
  Bool.eq_false_iff.mpr fun hfinite => by
    have := CorrectlyRounded.toReal_pos_of_isFinite_log (by decide) (by decide) hfinite
    rw [Model.Algebraic.toReal_of_toRat?_eq_some (q := -1) (by decide +kernel)] at this
    norm_num at this

example : (CorrectlyRounded.log minusOne32).toNatBits = 0x7fc00000 := by decide +kernel

/-! ## Opting in to the correctly rounded `MathFunctions` -/

open FloatLib.Numerics

/-- The default instances keep the approximation kernels. -/
example (x : Binary32) : MathFunctions.exp x = ExecFloat.Binary.exp x := rfl

example (x : Binary32) : MathFunctions.log x = ExecFloat.Binary.log x := rfl

example (x : Model .binary32) : MathFunctions.exp x = Model.exp x := rfl

/-- Passed by name, the dictionary has the correctly rounded `exp` and `log`. -/
example (x : Binary32) :
    MathFunctions.exp (self := ExecFloat.Binary.CorrectlyRounded.mathFunctions) x =
      ExecFloat.Binary.CorrectlyRounded.exp x :=
  ExecFloat.Binary.CorrectlyRounded.mathFunctions_exp_of_isIEEE x

example (x : Model .binary32) :
    MathFunctions.log (self := CorrectlyRounded.mathFunctions) x = CorrectlyRounded.log x :=
  CorrectlyRounded.mathFunctions_log_of_isIEEE rfl x

/-- A descriptor other than IEEE keeps the approximations in the dictionary too. -/
example (x : Model (.finite 4 3)) :
    MathFunctions.exp (self := CorrectlyRounded.mathFunctions) x = Model.exp x := rfl

section Scope

open scoped FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath

/-- Inside the scope, the instances are the dictionaries. -/
example (x : Binary32) : MathFunctions.exp x = ExecFloat.Binary.CorrectlyRounded.exp x :=
  ExecFloat.Binary.CorrectlyRounded.mathFunctions_exp_of_isIEEE x

example (x : Binary32) : MathFunctions.log x = ExecFloat.Binary.CorrectlyRounded.log x :=
  ExecFloat.Binary.CorrectlyRounded.mathFunctions_log_of_isIEEE x

example (x : Model .binary32) : MathFunctions.exp x = CorrectlyRounded.exp x :=
  CorrectlyRounded.mathFunctions_exp_of_isIEEE rfl x

/-- `exp 1` in binary32 is the nearest-even `0x402df854`. -/
example : ExecFloat.Binary.toNatBits (MathFunctions.exp (1 : Binary32)) = 0x402df854 := by
  decide +kernel

end Scope

/-- A client dictionary over `MathFunctions`, as a library's scalar class would be. -/
class ClientScalar (α : Type) extends MathFunctions α where
  /-- A constant the client adds. -/
  two : α

section Client

attribute [local instance high] ExecFloat.Binary.CorrectlyRounded.mathFunctions

/-- With the dictionary as a high-priority instance, the client's parent is the dictionary. -/
instance : ClientScalar Binary32 where
  two := 2

example (x : Binary32) :
    MathFunctions.exp (self := ClientScalar.toMathFunctions) x =
      ExecFloat.Binary.CorrectlyRounded.exp x :=
  ExecFloat.Binary.CorrectlyRounded.mathFunctions_exp_of_isIEEE x

/-- Direct calls use the same dictionary. -/
example (x : Binary32) : MathFunctions.log x = ExecFloat.Binary.CorrectlyRounded.log x :=
  ExecFloat.Binary.CorrectlyRounded.mathFunctions_log_of_isIEEE x

end Client

end FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded
