/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Logarithmic.Exact.Runtime
public import FloatLib.Numerics.Operation.Proof.Finite

/-!
# Real semantics and correctness of exact logarithmic numbers

The exact codes from `Exact.Runtime` denote zero or signed integral powers of the radix. This
module defines their real interpretation and numerical system, then connects the executable
rational decoder to that interpretation and proves multiplication refinement.

The proof views add only erased propositions to the existing code. The configured family uses
these results to expose exact logarithmic multiplication through `ExecFloat`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Logarithmic

open FloatLib.Numerics

namespace Code

/-- Real value of a logarithmic code. -/
noncomputable def toReal {radix : Radix} : Code radix → ℝ
  | .zero => 0
  | .value negative exponent =>
      let magnitude := radix.toReal ^ exponent
      if negative then -magnitude else magnitude

end Code

/-- Real semantics of exact logarithmic codes. -/
noncomputable def numericalSystem (radix : Radix) : NumericalSystem :=
  NumericalSystem.ofFinite (fun value : Code radix ↦ value.toReal)

/-- A logarithmic code with an erased proof of its complete denotation. -/
abbrev At (radix : Radix) (value : NumericalValue ℝ) :=
  (numericalSystem radix).At value

/-- A logarithmic code with an erased proof of its real value. -/
abbrev AtFinite (radix : Radix) (value : ℝ) :=
  (numericalSystem radix).AtFinite value

end FloatLib.Floats.Formats.Logarithmic

/-! ## Arithmetic refinement -/

namespace FloatLib.Floats.Formats.Logarithmic

open FloatLib.Numerics

namespace Code

/-- The distinguished logarithmic zero code decodes to real zero. -/
@[simp] theorem toReal_zero (radix : Radix) : toReal (Code.zero : Code radix) = 0 :=
  rfl

/-- The distinguished logarithmic zero code decodes to rational zero. -/
@[simp] theorem toRat_zero (radix : Radix) : toRat (Code.zero : Code radix) = 0 :=
  rfl

/-- The executable rational decoder agrees with the exact real semantics. -/
@[simp, norm_cast] theorem cast_toRat {radix : Radix} (value : Code radix) :
    (value.toRat : ℝ) = value.toReal := by
  cases value with
  | zero => simp [toRat, toReal]
  | value negative exponent =>
      cases negative <;>
        simp [toRat, toReal, Radix.toReal, Rat.cast_zpow]

/-- Decoding logarithmic multiplication gives exact real multiplication. -/
@[simp] theorem toReal_mul {radix : Radix} (left right : Code radix) :
    toReal (mul left right) = toReal left * toReal right := by
  cases left with
  | zero => simp [mul]
  | value leftSign leftExponent =>
      cases right with
      | zero => simp [mul]
      | value rightSign rightExponent =>
          cases leftSign <;> cases rightSign <;>
            simp [mul, toReal, zpow_add₀ radix.ne_zero]

/-- Logarithmic multiplication is exact in the executable rational domain as well. -/
@[simp] theorem toRat_mul {radix : Radix} (left right : Code radix) :
    toRat (mul left right) = toRat left * toRat right := by
  apply Rat.cast_injective (α := ℝ)
  simp

end Code

/-- Representation in the logarithmic system is equality of decoded real values. -/
@[simp] theorem numericalSystem_represents_iff {radix : Radix}
    (code : Code radix) (value : ℝ) :
    (numericalSystem radix).Represents code value ↔ code.toReal = value := by
  simp [NumericalSystem.Represents, numericalSystem]

/-- Logarithmic multiplication exactly refines multiplication over the reals. -/
theorem mul_refines {radix : Radix} :
    Operation.Finite2 (numericalSystem radix) (numericalSystem radix)
      (numericalSystem radix) Code.mul (fun left right : ℝ => left * right) := by
  exact Operation.Finite2.ofFinite Code.toReal_mul

end FloatLib.Floats.Formats.Logarithmic
