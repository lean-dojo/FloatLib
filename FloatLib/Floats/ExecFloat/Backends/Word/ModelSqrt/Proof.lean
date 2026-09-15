/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.ModelSqrt.Runtime
public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Proof
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Correctness of native-backed unpacked floating-point square root

The executable implementation lives in `ModelSqrt.Runtime`. This module proves exact agreement
with Lean's logical unpacked-float operation and registers the verified compiler substitution.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeModelSqrt

/-- The native-backed core is exactly Lean's logical unpacked square-root core. -/
theorem sqrtCore_eq (spec : Float.Model.Format) (mantissa : Nat) (exponent : Int) :
    sqrtCore spec mantissa exponent =
      Float.Model.UnpackedFloat.sqrtCore spec mantissa exponent := by
  simp [sqrtCore, Float.Model.UnpackedFloat.sqrtCore,
    FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrtNat_eq_sqrt]

/-- The native-backed operation is exactly Lean's logical unpacked floating-point square root. -/
theorem sqrt_eq (spec : Float.Model.Format) (value : Float.Model.UnpackedFloat) :
    sqrt spec value = Float.Model.UnpackedFloat.sqrt spec value := by
  cases value with
  | notANumber => rfl
  | infinity sign =>
      cases sign <;> rfl
  | zero sign => rfl
  | finite sign mantissa exponent mantissa_pos =>
      cases sign
      · rfl
      · simp [sqrt, Float.Model.UnpackedFloat.sqrt, sqrtCore_eq]

/-- Compile Lean's logical unpacked square root through the proved native-backed implementation. -/
@[csimp] theorem unpackedSqrt_eq_sqrt :
    Float.Model.UnpackedFloat.sqrt = sqrt := by
  funext spec value
  exact (sqrt_eq spec value).symm

end Model.NativeModelSqrt
end FloatLib.Floats.Formats.BinaryInterchange
