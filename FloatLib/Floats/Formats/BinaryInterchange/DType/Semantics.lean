/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DType.Cast
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Constants
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof
public import FloatLib.Numerics.Representations.FixedInt.Semantics.Basic
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.RoundToIntegral

/-!
# Mathematical semantics of executable scalar conversions

Executable integer, Boolean, and arbitrary-format float conversions have exact mathematical
contracts. Integer-to-float conversion performs one explicitly directed destination rounding.
Float-to-integer conversion uses the central unbounded-integer rounding operation, then rejects
results outside the signed destination range.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecDType

open FloatLib.Numerics
open FloatLib.Numerics.Representations
open Model (toReal isFinite)
open FixedInt (toInt)

/-- `intToFloat` is exactly the value component of its status-bearing operation. -/
@[simp] theorem intToFloat_eq_value {fmt : FloatFormat} {width : Nat}
    (x : FixedInt width) (rounding : Model.IEEERoundingMode) :
    intToFloat fmt x rounding = (intToFloatWithStatus fmt x rounding).value :=
  rfl

/-- A finite nearest-even conversion to a conventional IEEE format agrees with real rounding. -/
theorem intToFloat_nearestEven_eq_round {fmt : FloatFormat} {width : Nat}
    (x : FixedInt width)
    (hfmt : fmt.isIEEE = true)
    (hfin : isFinite (intToFloat fmt x .nearestEven) = true) :
    toReal (intToFloat fmt x .nearestEven) =
      Model.roundAt fmt (FixedInt.toInt x : ℝ) := by
  let n := FixedInt.toInt x
  simp only [intToFloat] at hfin ⊢
  simp only [intToFloatWithStatus]
  change isFinite
      (Model.roundDyadicWithRounding fmt .nearestEven
        ({ negative := decide (n < 0), significand := n.natAbs, exponent := 0 } :
          Numerics.Dyadic)) = true at hfin
  change toReal
      (Model.roundDyadicWithRounding fmt .nearestEven
        ({ negative := decide (n < 0), significand := n.natAbs, exponent := 0 } :
          Numerics.Dyadic)) = Model.roundAt fmt (n : ℝ)
  simp only [Model.roundDyadicWithRounding] at hfin ⊢
  rw [Model.toReal_roundDyadic_eq_roundAt fmt hfmt _ hfin]
  congr 1
  cases n <;> simp [Numerics.Dyadic.toReal]

/--
A finite float-to-integer conversion succeeds with the selected rounded integer when that
integer lies in the signed destination range.
-/
theorem floatToInt_of_exactValue_eq_finite_of_inRange
    {fmt : FloatFormat} {width : Nat} (x : Model fmt)
    (rounding : Model.IEEERoundingMode) (exact : Numerics.Dyadic)
    (hvalue : Model.exactValue x = .finite exact)
    (hrange : FixedInt.InRange width (Model.roundDyadicToInt rounding exact)) :
    floatToInt (width := width) x rounding =
      .success
        (FixedInt.ofInt (Model.roundDyadicToInt rounding exact))
        { inexact := !Model.dyadicIsIntegral exact } := by
  simp [floatToInt, hvalue, hrange]

/-- A finite rounded integer outside the signed destination range is rejected. -/
theorem floatToInt_of_exactValue_eq_finite_of_not_inRange
    {fmt : FloatFormat} {width : Nat} (x : Model fmt)
    (rounding : Model.IEEERoundingMode) (exact : Numerics.Dyadic)
    (hvalue : Model.exactValue x = .finite exact)
    (hrange : ¬FixedInt.InRange width (Model.roundDyadicToInt rounding exact)) :
    floatToInt (width := width) x rounding = .failure .outOfRange := by
  simp [floatToInt, hvalue, hrange]

/-- Float-to-integer conversion rejects infinity and retains its sign in the failure. -/
theorem floatToInt_of_exactValue_eq_infinity
    {fmt : FloatFormat} {width : Nat} (x : Model fmt)
    (rounding : Model.IEEERoundingMode) (negative : Bool)
    (hvalue : Model.exactValue x = .infinity negative) :
    floatToInt (width := width) x rounding =
      .failure (.infinity .source negative) := by
  simp [floatToInt, hvalue]

/-- Float-to-integer conversion rejects a NaN and retains its payload in the failure. -/
theorem floatToInt_of_exactValue_eq_nan
    {fmt : FloatFormat} {width : Nat} (x : Model fmt)
    (rounding : Model.IEEERoundingMode)
    (negative signaling : Bool) (payload : Nat)
    (hvalue : Model.exactValue x = .nan negative signaling payload) :
    floatToInt (width := width) x rounding =
      .failure (.exceptional .source (.nan (some payload))) := by
  simp [floatToInt, hvalue]

/-- Successful finite conversion stores the selected integer exactly at positive width. -/
theorem toInt_of_floatToInt_finite
    {width : Nat} (rounding : Model.IEEERoundingMode)
    (exact : Numerics.Dyadic)
    (hwidth : 0 < width)
    (hrange : FixedInt.InRange width (Model.roundDyadicToInt rounding exact)) :
    (FixedInt.ofInt
      (width := width) (Model.roundDyadicToInt rounding exact)).toInt =
        Model.roundDyadicToInt rounding exact := by
  exact FixedInt.toInt_ofInt_eq_self hwidth hrange

/-- Toward-zero conversion uses floor for nonnegative inputs and ceiling for negative inputs. -/
theorem floatToInt_towardZero_of_exactValue_eq_finite_of_inRange
    {fmt : FloatFormat} {width : Nat} (x : Model fmt)
    (exact : Numerics.Dyadic)
    (hvalue : Model.exactValue x = .finite exact)
    (hrange : FixedInt.InRange width
      (if 0 ≤ exact.toReal then ⌊exact.toReal⌋ else ⌈exact.toReal⌉)) :
    floatToInt (width := width) x .towardZero =
      .success
        (FixedInt.ofInt
          (if 0 ≤ exact.toReal then ⌊exact.toReal⌋ else ⌈exact.toReal⌉))
        { inexact := !Model.dyadicIsIntegral exact } := by
  rw [← Model.roundDyadicToInt_towardZero] at hrange ⊢
  exact floatToInt_of_exactValue_eq_finite_of_inRange
    x .towardZero exact hvalue hrange

/-- Boolean `true` converts to the real value one in every format. -/
theorem boolToFloat_true (fmt : FloatFormat) :
    toReal (boolToFloat fmt true) = 1 := by
  simp [boolToFloat]

/-- Boolean `false` converts to the real value zero in every format. -/
theorem boolToFloat_false (fmt : FloatFormat) :
    toReal (boolToFloat fmt false) = 0 := by
  simpa [boolToFloat, Model.zero] using Model.toReal_zero fmt false

/-- A Boolean mask selects either its operand or positive zero. -/
theorem maskFloat_eq_if {fmt : FloatFormat} (m : Bool) (x : Model fmt) :
    toReal (maskFloat fmt m x) = if m then toReal x else 0 := by
  cases m
  · simpa [maskFloat, Model.zero] using Model.toReal_zero fmt false
  · simp [maskFloat]


end ExecDType
end FloatLib.Floats.Formats.BinaryInterchange
