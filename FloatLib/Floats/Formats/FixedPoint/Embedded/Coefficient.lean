/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Precision
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Exact
public import FloatLib.Tactic.CompilerOptimize

/-!
# N1169 arithmetic on stored coefficients

WG14 N1169 (2006 TR 18037 draft), §4.1.6.1–2 and Annex G item 2. Exact common-grid operations cancel
their common scale before rounding. The equalities below preserve saturation,
undefined overflow and every admitted rounding or precision policy at every width.
The shared clamp and integer range test implement the resulting coefficient step.
The kernel costs use eight-bit stored operands and include the result observation;
they select implementations, rather than asserting a uniform timing bound.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics FloatLib.Floats.ExecFloat

/-- Dividing out the scale is the entire rational part of ordinary conversion. -/
theorem convert_eq_finish (format : Format) (rounding : Rounding)
    (overflow : Overflow) (value : ℚ) :
    convert format rounding overflow value =
      format.finish overflow (rounding.run (value / format.quantizer.scale)) := rfl

/-- An exact scaled integer needs no rounding, for every adjacent rounder. -/
theorem convert_coefficient (format : Format) (rounding : Rounding)
    (overflow : Overflow) (coefficient : Int) :
    convert format rounding overflow ((coefficient : ℚ) * format.quantizer.scale) =
      format.finish overflow coefficient := by
  rw [convert_eq_finish, mul_div_cancel_right₀ _ (ne_of_gt format.quantizer.scale_pos),
    rounding.run_intCast]

/-- Decoding is multiplication by the format's common positive scale. -/
theorem decode_eq_mul_scale {format : Format} (value : format.Code) :
    Format.decode value = (bitsfx value : ℚ) * format.quantizer.scale := by
  change format.quantizer.scale * ((value.1 - 0 : Int) : ℚ) =
    (value.1 : ℚ) * format.quantizer.scale
  rw [Int.sub_zero, mul_comm]

/-- Same-grid addition is exact integer addition followed by the common overflow step. -/
@[kernel_optimize (cost := 473)]
theorem convert_add_decode {format : Format} (rounding : Rounding)
    (overflow : Overflow) (x y : format.Code) :
    convert format rounding overflow (Format.decode x + Format.decode y) =
      format.finish overflow (bitsfx x + bitsfx y) := by
  rw [decode_eq_mul_scale, decode_eq_mul_scale, ← add_mul, ← Int.cast_add]
  exact convert_coefficient _ _ _ _

/-- Same-grid subtraction is exact integer subtraction with the same overflow behavior. -/
@[kernel_optimize (cost := 473)]
theorem convert_sub_decode {format : Format} (rounding : Rounding)
    (overflow : Overflow) (x y : format.Code) :
    convert format rounding overflow (Format.decode x - Format.decode y) =
      format.finish overflow (bitsfx x - bitsfx y) := by
  rw [decode_eq_mul_scale, decode_eq_mul_scale, ← sub_mul, ← Int.cast_sub]
  exact convert_coefficient _ _ _ _

/-- Exact negation on the stored coefficient, including the negative endpoint. -/
def Unary.negateCoefficient {format : Format} (_rounding : Rounding)
    (overflow : Overflow) (value : format.Code) : Option format.Code :=
  format.finish overflow (-bitsfx value)

/-- Coefficient negation refines the N1169 unary-minus specification at every precision.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.6.1.2.
-/
@[kernel_optimize (cost := 432)]
theorem Unary.neg_eq_coefficient {format : Format} (rounding : Rounding)
    (overflow : Overflow) (value : format.Code) :
    Unary.«-» rounding overflow value = Unary.negateCoefficient rounding overflow value := by
  unfold Unary.«-» Unary.negateCoefficient
  rw [decode_eq_mul_scale, ← neg_mul, ← Int.cast_neg]
  exact convert_coefficient _ _ _ _

/-- Compile unary minus using its proved integer-coefficient implementation. -/
compiled_as Unary.«-» := Unary.negateCoefficient by Unary.neg_eq_coefficient

/-- Direct compiled certificate for N1169 unary minus, independent of width and rounder.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.6.1.2.
-/
@[compiler_optimize direct]
def Unary.negDirect : Backend.Certified (@Unary.«-») where
  estimate := { name := "fixed coefficient negation", kind := .generic, steadyCost := 1 }
  run := @Unary.negateCoefficient
  run_eq_spec := by
    funext format rounding overflow value
    exact (Unary.neg_eq_coefficient rounding overflow value).symm

/-- Increment and decrement change the coefficient by exactly one integral unit. -/
def Unary.updateCoefficient {format : Format} (increment : Bool) (_rounding : Rounding)
    (overflow : Overflow) (value : format.Code) : Option format.Code :=
  format.finish overflow
    (bitsfx value + if increment then (2 : Int) ^ format.fractionalBits
      else -(2 : Int) ^ format.fractionalBits)

/-- N1169 prefix and postfix updates cancel the common scale before conversion.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.6.1.1.
-/
@[kernel_optimize (cost := 464)]
theorem Unary.update_eq_coefficient {format : Format} (increment : Bool)
    (rounding : Rounding) (overflow : Overflow) (value : format.Code) :
    Unary.update increment rounding overflow value =
      Unary.updateCoefficient increment rounding overflow value := by
  unfold Unary.update Unary.updateCoefficient
  rw [decode_eq_mul_scale]
  have hone : (((2 : Int) ^ format.fractionalBits : Int) : ℚ) *
      format.quantizer.scale = 1 := by
    simp [Format.quantizer]
  cases increment
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← hone, ← neg_mul, ← add_mul, ← Int.cast_neg, ← Int.cast_add]
    exact convert_coefficient _ _ _ _
  · simp only [↓reduceIte]
    rw [← hone, ← add_mul, ← Int.cast_add]
    exact convert_coefficient _ _ _ _

/-- Compile both update directions through one certified coefficient operation. -/
compiled_as Unary.update := Unary.updateCoefficient by Unary.update_eq_coefficient

/-- Direct compiled certificate for both N1169 update directions at every precision.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.6.1.1.
-/
@[compiler_optimize direct]
def Unary.updateDirect : Backend.Certified (@Unary.update) where
  estimate := { name := "fixed coefficient update", kind := .generic, steadyCost := 1 }
  run := @Unary.updateCoefficient
  run_eq_spec := by
    funext format increment rounding overflow value
    exact (Unary.update_eq_coefficient increment rounding overflow value).symm

/-- Coefficient shifts retain the C count constraint and the chosen right-shift rounding. -/
def shiftCoefficient {format : Format} (left : Bool) (rounding : Rounding)
    (overflow : Overflow) (value : format.Code) (count : Int) : Option format.Code :=
  if 0 ≤ count ∧ count < (format.width : Int) then
    format.finish overflow
      (if left then bitsfx value * (2 : Int) ^ count.toNat
        else rounding.run ((bitsfx value : ℚ) / (2 : ℚ) ^ count.toNat))
  else none

/-- N1169 shifts divide out the common scale before applying rounding and overflow.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.2.
-/
@[kernel_optimize (cost := 915)]
theorem shift_eq_coefficient {format : Format} (left : Bool) (rounding : Rounding)
    (overflow : Overflow) (value : format.Code) (count : Int) :
    shift left rounding overflow value count =
      shiftCoefficient left rounding overflow value count := by
  unfold shift shiftCoefficient
  split
  · dsimp only
    cases left
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [convert_eq_finish, decode_eq_mul_scale]
      congr 2
      rw [mul_div_right_comm, mul_div_cancel_right₀ _ (ne_of_gt format.quantizer.scale_pos)]
    · simp only [↓reduceIte]
      rw [decode_eq_mul_scale, mul_right_comm]
      have hcast : (bitsfx value : ℚ) * (2 : ℚ) ^ count.toNat =
          ((bitsfx value * (2 : Int) ^ count.toNat : Int) : ℚ) := by
        push_cast
        rfl
      rw [hcast, convert_coefficient]
  · rfl

/-- Compile both shift directions through the same width-independent coefficient path. -/
compiled_as shift := shiftCoefficient by shift_eq_coefficient

/-- Direct compiled certificate for N1169 shifts, including invalid counts.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.2.
-/
@[compiler_optimize direct]
def shiftDirect : Backend.Certified (@shift) where
  estimate := { name := "fixed coefficient shift", kind := .generic, steadyCost := 1 }
  run := @shiftCoefficient
  run_eq_spec := by
    funext format left rounding overflow value count
    exact (shift_eq_coefficient left rounding overflow value count).symm

/-- N1169's optional precision choices cannot change addition or subtraction.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.3 and 4.1.6.2.1.
-/
theorem ArithmeticPolicy.choose_add_sub (policy : ArithmeticPolicy) (format : Format)
    (operation : Arithmetic) (x y : ℚ) (h : operation = .add ∨ operation = .sub) :
    policy.choose format operation x y = .ordinary := by
  have allowed := policy.allowed format operation x y
  cases choice : policy.choose format operation x y with
  | ordinary => rfl
  | neighbor upper =>
    simp only [choice, ArithmeticChoice.Allowed] at allowed
    rcases h with rfl | rfl <;> simp at allowed
  | unitProduct =>
    simp only [choice, ArithmeticChoice.Allowed] at allowed
    rcases h with rfl | rfl <;> simp at allowed

/-- Every admitted addition policy takes the same direct coefficient result. -/
@[kernel_optimize (cost := 473)]
theorem Arithmetic.applyWith_add_codes (policy : ArithmeticPolicy) {format : Format}
    (rounding : Rounding) (overflow : Overflow) (x y : format.Code) :
    Arithmetic.add.applyWith policy format rounding overflow (Format.decode x) (Format.decode y) =
      format.finish overflow (bitsfx x + bitsfx y) := by
  simp only [Arithmetic.applyWith, Arithmetic.exact, Option.bind_some,
    policy.choose_add_sub _ _ _ _ (Or.inl rfl), ArithmeticChoice.apply]
  exact convert_add_decode _ _ _ _

/-- Every admitted subtraction policy takes the same direct coefficient result. -/
@[kernel_optimize (cost := 473)]
theorem Arithmetic.applyWith_sub_codes (policy : ArithmeticPolicy) {format : Format}
    (rounding : Rounding) (overflow : Overflow) (x y : format.Code) :
    Arithmetic.sub.applyWith policy format rounding overflow (Format.decode x) (Format.decode y) =
      format.finish overflow (bitsfx x - bitsfx y) := by
  simp only [Arithmetic.applyWith, Arithmetic.exact, Option.bind_some,
    policy.choose_add_sub _ _ _ _ (Or.inr rfl), ArithmeticChoice.apply]
  exact convert_sub_decode _ _ _ _

end FloatLib.Floats.Formats.FixedPoint.Embedded
