/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Standard
public import FloatLib.Tactic.FloatDecide

/-! WG14 N1169 (2006 TR 18037 draft), §4.1.6: coefficient refinement and endpoint clients at
arbitrary widths. -/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.EmbeddedCoefficient

open FloatLib.Numerics FloatLib.Floats.Formats.FixedPoint.Embedded

example (format : Format) (rounding : Rounding) (overflow : Overflow) (coefficient : Int) :
    convert format rounding overflow ((coefficient : ℚ) * format.quantizer.scale) =
      format.finish overflow coefficient :=
  convert_coefficient format rounding overflow coefficient

example (policy : ArithmeticPolicy) (format : Format) (rounding : Rounding)
    (overflow : Overflow) (x y : format.Code) :
    Arithmetic.add.applyWith policy format rounding overflow (Format.decode x) (Format.decode y) =
      format.finish overflow (bitsfx x + bitsfx y) :=
  Arithmetic.applyWith_add_codes policy rounding overflow x y

example (policy : ArithmeticPolicy) (format : Format) (rounding : Rounding)
    (overflow : Overflow) (x y : format.Code) :
    Arithmetic.sub.applyWith policy format rounding overflow (Format.decode x) (Format.decode y) =
      format.finish overflow (bitsfx x - bitsfx y) :=
  Arithmetic.applyWith_sub_codes policy rounding overflow x y

example : @Unary.negDirect.run = @Unary.«-» := Unary.negDirect.run_eq_spec
example : @Unary.updateDirect.run = @Unary.update := Unary.updateDirect.run_eq_spec
example : @shiftDirect.run = @shift := shiftDirect.run_eq_spec

private def fract : Format := _Fract true 3
private def lower : fract.Code := ⟨-8, by decide⟩
private def zero : fract.Code := ⟨0, by decide⟩
private def negative : fract.Code := ⟨-3, by decide⟩

example : (Unary.«-» .floor .SAT lower).map bitsfx = some 7 := by float_decide
example : Unary.«-» .floor .DEFAULT lower = none := by float_decide
example : (Prefix.«++» .ceil .SAT zero).map bitsfx = some 7 := by float_decide
example : Prefix.«++» .ceil .DEFAULT zero = none := by float_decide
example : (Prefix.«--» .floor .DEFAULT zero).map bitsfx = some (-8) := by float_decide
example : (Binary.«>>» .floor .DEFAULT negative 1).map bitsfx = some (-2) := by float_decide
example : (Binary.«>>» .ceil .DEFAULT negative 1).map bitsfx = some (-1) := by float_decide
example : (Binary.«<<» .floor .SAT negative 2).map bitsfx = some (-8) := by float_decide
example : Binary.«<<» .floor .DEFAULT negative 4 = none := by float_decide
example : Binary.«>>» .floor .SAT negative (-1) = none := by float_decide

end FloatLibTests.Conformance.Formats.EmbeddedCoefficient
