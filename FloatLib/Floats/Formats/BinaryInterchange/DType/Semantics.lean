/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Constants
public import FloatLib.Floats.Formats.BinaryInterchange.DType.Cast
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof
public import FloatLib.Numerics.Representations.FixedInt.Semantics.Basic

import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.RoundToIntegral.Real

/-!
# Mathematical semantics of executable scalar conversions

Executable integer, Boolean, and arbitrary-format float conversions have exact mathematical
contracts. Integer-to-float conversion performs one destination rounding in the given direction.
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

/-- The value of a conversion with `status := true` is the conversion without it. -/
@[simp] theorem value_convertFromInt {fmt : FloatFormat} {width : Nat}
    (x : FixedInt width) (mode : Model.IEEERoundingMode) :
    (convertFromInt fmt x (mode := mode) (status := true)).value = convertFromInt fmt
      x (mode := mode) :=
  rfl

/-- A finite nearest-even conversion to a conventional IEEE format agrees with real rounding. -/
theorem convertFromInt_nearest_eq_round {fmt : FloatFormat} {width : Nat}
    (x : FixedInt width)
    (hfmt : fmt.isIEEE = true)
    (hfin : isFinite (convertFromInt fmt x .nearest) = true) :
    toReal (convertFromInt fmt x .nearest) =
      Model.roundAt fmt (FixedInt.toInt x : ℝ) := by
  let n := FixedInt.toInt x
  simp only [convertFromInt] at hfin ⊢
  simp only [Internal.Status.convertFromInt]
  change isFinite
      (Model.Internal.Directed.roundDyadic fmt .nearest
        ({ negative := decide (n < 0), significand := n.natAbs, exponent := 0 } :
          Numerics.Dyadic)) = true at hfin
  change toReal
      (Model.Internal.Directed.roundDyadic fmt .nearest
        ({ negative := decide (n < 0), significand := n.natAbs, exponent := 0 } :
          Numerics.Dyadic)) = Model.roundAt fmt (n : ℝ)
  simp only [Model.Internal.Directed.roundDyadic] at hfin ⊢
  rw [Model.toReal_roundDyadic_eq_roundAt fmt hfmt _ hfin]
  congr 1
  cases n <;> simp [Numerics.Dyadic.toReal]

/--
A finite float-to-integer conversion succeeds with the selected rounded integer when that
integer lies in the signed destination range.
-/
theorem convertToIntegerExact_of_exactValue_eq_finite_of_inRange
    {fmt : FloatFormat} {width : Nat} (x : Model fmt)
    (mode : Model.IEEERoundingMode) (exact : Numerics.Dyadic)
    (hvalue : Model.exactValue x = .finite exact)
    (hrange : FixedInt.InRange width (Model.roundDyadicToInt mode exact)) :
    convertToIntegerExact (width := width) x mode =
      .success
        (FixedInt.ofInt (Model.roundDyadicToInt mode exact))
        { inexact := !Model.dyadicIsIntegral exact } := by
  simp [convertToIntegerExact, hvalue, hrange]

/-- A finite rounded integer outside the signed destination range is rejected. -/
theorem convertToIntegerExact_of_exactValue_eq_finite_of_not_inRange
    {fmt : FloatFormat} {width : Nat} (x : Model fmt)
    (mode : Model.IEEERoundingMode) (exact : Numerics.Dyadic)
    (hvalue : Model.exactValue x = .finite exact)
    (hrange : ¬FixedInt.InRange width (Model.roundDyadicToInt mode exact)) :
    convertToIntegerExact (width := width) x mode = .failure .outOfRange := by
  simp [convertToIntegerExact, hvalue, hrange]

/-- Float-to-integer conversion rejects infinity and retains its sign in the failure. -/
theorem convertToIntegerExact_of_exactValue_eq_infinity
    {fmt : FloatFormat} {width : Nat} (x : Model fmt)
    (mode : Model.IEEERoundingMode) (negative : Bool)
    (hvalue : Model.exactValue x = .infinity negative) :
    convertToIntegerExact (width := width) x mode =
      .failure (.infinity .source negative) := by
  simp [convertToIntegerExact, hvalue]

/-- NaN conversion failures retain the source sign, signaling class, and payload. -/
theorem convertToIntegerExact_of_exactValue_eq_nan
    {fmt : FloatFormat} {width : Nat} (x : Model fmt)
    (mode : Model.IEEERoundingMode)
    (negative signaling : Bool) (payload : Nat)
    (hvalue : Model.exactValue x = .nan negative signaling payload) :
    convertToIntegerExact (width := width) x mode =
      .failure (.exceptional .source
        (.nan (some (Model.payloadOfNaNField signaling payload fmt.encoding)) negative
          signaling)) := by
  simp [convertToIntegerExact, hvalue]

/--
A successful conversion of a finite input stores its rounded integer unchanged. The result's signed
value is `Model.roundDyadicToInt mode exact`, at every width.
-/
theorem toInt_of_convertToIntegerExact_finite
    {fmt : FloatFormat} {width : Nat} {x : Model fmt}
    {mode : Model.IEEERoundingMode} {exact : Numerics.Dyadic}
    {result : FixedInt width} {status : FloatLib.Floats.ExecFloat.ConversionStatus}
    (hvalue : Model.exactValue x = .finite exact)
    (hsuccess : convertToIntegerExact (width := width) x mode = .success result status) :
    result.toInt = Model.roundDyadicToInt mode exact := by
  by_cases hrange : FixedInt.InRange width (Model.roundDyadicToInt mode exact)
  · rw [convertToIntegerExact_of_exactValue_eq_finite_of_inRange x mode exact hvalue
    hrange] at hsuccess
    cases hsuccess
    exact FixedInt.toInt_ofInt_eq_self hrange
  · rw [convertToIntegerExact_of_exactValue_eq_finite_of_not_inRange x mode exact
    hvalue hrange] at hsuccess
    cases hsuccess

/--
`convertToInteger` succeeds where `convertToIntegerExact` does, with the same integer and
without the inexact signal.
-/
theorem convertToInteger_of_convertToIntegerExact_eq_success
    {fmt : FloatFormat} {width : Nat} {x : Model fmt} {mode : Model.IEEERoundingMode}
    {result : FixedInt width} {status : FloatLib.Floats.ExecFloat.ConversionStatus}
    (hsuccess : convertToIntegerExact (width := width) x mode = .success result status) :
    convertToInteger (width := width) x mode =
      .success result { status with inexact := false } := by
  simp [convertToInteger, hsuccess]

/-- `convertToInteger` fails where `convertToIntegerExact` does, for the same reason. -/
theorem convertToInteger_of_convertToIntegerExact_eq_failure
    {fmt : FloatFormat} {width : Nat} {x : Model fmt} {mode : Model.IEEERoundingMode}
    {reason : FloatLib.Floats.ExecFloat.ConversionFailure}
    (hfailure : convertToIntegerExact (width := width) x mode = .failure reason) :
    convertToInteger (width := width) x mode = .failure reason := by
  simp [convertToInteger, hfailure]

/-- Toward-zero conversion uses floor for nonnegative inputs and ceiling for negative inputs. -/
theorem convertToIntegerExact_towardZero_of_exactValue_eq_finite_of_inRange
    {fmt : FloatFormat} {width : Nat} (x : Model fmt)
    (exact : Numerics.Dyadic)
    (hvalue : Model.exactValue x = .finite exact)
    (hrange : FixedInt.InRange width
      (if 0 ≤ exact.toReal then ⌊exact.toReal⌋ else ⌈exact.toReal⌉)) :
    convertToIntegerExact (width := width) x .towardZero =
      .success
        (FixedInt.ofInt
          (if 0 ≤ exact.toReal then ⌊exact.toReal⌋ else ⌈exact.toReal⌉))
        { inexact := !Model.dyadicIsIntegral exact } := by
  rw [← Model.roundDyadicToInt_towardZero] at hrange ⊢
  exact convertToIntegerExact_of_exactValue_eq_finite_of_inRange
    x .towardZero exact hvalue hrange

/-- Boolean `true` converts to the real value one in every format. -/
theorem boolToFloat_true (fmt : FloatFormat) :
    toReal (boolToFloat fmt true) = 1 := by
  simp [boolToFloat]

/-- Boolean `false` converts to the real value zero in every format. -/
theorem boolToFloat_false (fmt : FloatFormat) :
    toReal (boolToFloat fmt false) = 0 := by
  simp [boolToFloat]

/--
On real values a Boolean mask keeps its operand's value or gives zero. The equation is about
`toReal`, which sends NaN and infinities to `0` and identifies the two zeros, so for those operands
it holds whatever word is selected. The words themselves are `x` or `posZero fmt` by the definition
of `maskFloat`.
-/
theorem maskFloat_eq_if {fmt : FloatFormat} (m : Bool) (x : Model fmt) :
    toReal (maskFloat fmt m x) = if m then toReal x else 0 := by
  cases m
  · simp [maskFloat]
  · simp [maskFloat]


end ExecDType
end FloatLib.Floats.Formats.BinaryInterchange
