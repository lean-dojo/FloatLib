/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Interval
public import FloatLib.Floats.Formats.Posit.Configured.Interval

/-!
# Decimal and posit interval execution

Kernel-checked examples exercise both decimal codecs, a custom decimal layout, configured
posit storage, inexact inputs, arithmetic, underflow brackets, and explicit overflow failure.
No host floating-point approximation is used to compare the endpoints.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.NonBinaryIntervals

open FloatLib Numerics Floats.Formats

private def decoded? {α : Type} (R : OutwardRounding α ℚ) (result : Option (Interval α)) :
    Option (ℚ × ℚ) := do
  let I ← result
  let lo ← R.decode I.lo
  let hi ← R.decode I.hi
  pure (lo, hi)

private def calculate? {α : Type} (R : OutwardRounding α ℚ)
    (op : Interval α → Interval α → Option (Interval α)) (x y : ℚ) :
    Option (Interval α) := do
  let I ← R.enclose? x
  let J ← R.enclose? y
  op I J

private def divideAcrossZero? {α : Type} (R : OutwardRounding α ℚ) :
    Option (Interval α) := do
  let negative ← R.enclose? (-1)
  let positive ← R.enclose? 1
  Interval.div? R positive ⟨negative.lo, positive.hi⟩

private def tinyDecimal : DecimalInterchange.Format := ⟨0, 1, 2, by decide⟩

private def decimalR := DecimalInterchange.intervalRounding tinyDecimal .bid

example : decoded? decimalR (decimalR.enclose? (1 / 3)) = some (3 / 10, 2 / 5) := by
  decide +kernel

example : decoded? decimalR (decimalR.enclose? (-1 / 3)) = some (-2 / 5, -3 / 10) := by
  decide +kernel

example : decoded? decimalR (calculate? decimalR (Interval.add? decimalR) (1 / 10) (1 / 5)) =
    some (3 / 10, 3 / 10) := by decide +kernel

example : decoded? decimalR (calculate? decimalR (Interval.mul? decimalR) (-2) 3) =
    some (-6, -6) := by decide +kernel

example : decoded? decimalR (calculate? decimalR (Interval.div? decimalR) 1 3) =
    some (3 / 10, 2 / 5) := by decide +kernel

example : decimalR.enclose? 10000 = none := by decide +kernel
example : decimalR.enclose? (-10000) = none := by decide +kernel
example : divideAcrossZero? decimalR = none := by decide +kernel

example :
    let nan := DecimalInterchange.Encoding.bid.codec.encode tinyDecimal (.nan false false 0)
    Interval.add? decimalR (Interval.point nan) (Interval.point nan) = none := by
  decide +kernel

example :
    let R := DecimalInterchange.intervalRounding tinyDecimal .dpd
    decoded? R (R.enclose? (1 / 3)) = some (3 / 10, 2 / 5) := by
  decide +kernel

example :
    let R := DecimalInterchange.intervalRounding .decimal32 .bid
    decoded? R (R.enclose? (1 / 3)) = some (3333333 / 10000000, 1666667 / 5000000) := by
  decide +kernel

private def positFormat : Posit.Format := ⟨8, by decide⟩

private def positR := Posit.intervalRounding positFormat

example : decoded? positR (positR.enclose? 1) = some (1, 1) := by decide +kernel
example : decoded? positR (positR.enclose? (-1)) = some (-1, -1) := by decide +kernel
example : (positR.enclose? (1 / 3)).isSome = true := by decide +kernel
example : (positR.enclose? (-1 / 3)).isSome = true := by decide +kernel

example : decoded? positR (calculate? positR (Interval.add? positR) 1 2) =
    some (3, 3) := by decide +kernel

example : decoded? positR (calculate? positR (Interval.mul? positR) (-2) 3) =
    some (-6, -6) := by decide +kernel

example : decoded? positR (calculate? positR (Interval.div? positR) 1 2) =
    some (1 / 2, 1 / 2) := by decide +kernel

example : decoded? positR (positR.enclose? (1 / 33554432)) =
    some (0, 1 / 16777216) := by decide +kernel

example : positR.enclose? 33554432 = none := by decide +kernel
example : positR.enclose? (-33554432) = none := by decide +kernel
example : divideAcrossZero? positR = none := by decide +kernel

example : Interval.mul? positR (Interval.point (Posit.Model.nar positFormat))
    (Interval.point (Posit.Model.zero positFormat)) = none := by decide +kernel

private def configuredR : OutwardRounding (Floats.ExecFloat.Posit 8) ℚ :=
  Floats.ExecFloat.Posit.intervalRounding

example : decoded? configuredR (configuredR.enclose? (1 / 3)) =
    decoded? positR (positR.enclose? (1 / 3)) := by decide +kernel

example : decoded? configuredR (calculate? configuredR (Interval.add? configuredR) 1 2) =
    some (3, 3) := by decide +kernel

example : configuredR.enclose? 33554432 = none := by decide +kernel
example : divideAcrossZero? configuredR = none := by decide +kernel

example :
    let R : OutwardRounding (Floats.ExecFloat.Posit 32) ℚ :=
      Floats.ExecFloat.Posit.intervalRounding
    decoded? R (R.enclose? 1) = some (1, 1) := by decide +kernel

example :
    let R : OutwardRounding (Floats.ExecFloat.Posit 128) ℚ :=
      Floats.ExecFloat.Posit.intervalRounding
    decoded? R (R.enclose? 1) = some (1, 1) := by decide +kernel

example :
    let R : OutwardRounding (Floats.ExecFloat.Posit 129) ℚ :=
      Floats.ExecFloat.Posit.intervalRounding
    decoded? R (R.enclose? 1) = some (1, 1) := by decide +kernel

end FloatLibTests.Conformance.Formats.NonBinaryIntervals
