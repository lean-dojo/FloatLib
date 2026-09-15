/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation

/-!
# Regression checks for `Model` proof automation

These examples are acceptance tests for the user-facing proof workflow. They ensure `grind`,
`binary_interchange_spec`, and `numerics` can move from executable operations to exact or
error-bounded statements using local finiteness hypotheses.

The custom format is intentional: a proof tactic that works only because binary32 or binary64 has
a special theorem should fail here. Concrete standard formats remain in the suite to catch
instance and literal elaboration regressions.
-/

@[expose] public section

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Conformance.BinaryInterchange.ExecFloatAutomation

open FloatLib.Floats.Formats.BinaryInterchange.Model

@[floatFormat] abbrev customFormat : FloatFormat :=
  FloatFormat.ieee 4 5

example (x y : Model customFormat) :
    add x y = Spec.add x y := by
  grind

example (x y z w : Model customFormat) :
    fma (add x y) z w = Spec.fma (Spec.add x y) z w := by
  binary_interchange_spec

example (x y : Model customFormat)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (add x y) = true) :
    toReal (add x y) = roundAt customFormat (toReal x + toReal y) := by
  numerics

example (x y : Model FloatFormat.binary64)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (sub x y) = true) :
    toReal (sub x y) = roundAt FloatFormat.binary64 (toReal x - toReal y) := by
  numerics

example (x : Model FloatFormat.binary16)
    (hx : isFinite x = true)
    (hout : isFinite (cast FloatFormat.binary16 customFormat x) = true) :
    toReal (cast FloatFormat.binary16 customFormat x) =
      roundAt customFormat (toReal x) := by
  numerics

example (x : Model customFormat) (hx : isFinite x = true) :
    toReal (neg x) = -toReal x := by
  numerics

example (x y : Model FloatFormat.binary32)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (add x y) = true) :
    |toReal (add x y) - (toReal x + toReal y)| ≤
      epsilonAt FloatFormat.binary32 (toReal x + toReal y) := by
  numerics

example (x y : Model FloatFormat.binary64)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (mul x y) = true) :
    |toReal (mul x y) - toReal x * toReal y| ≤
      epsilonAt FloatFormat.binary64 (toReal x * toReal y) := by
  numerics

example (x y z : Model customFormat)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hout : isFinite (fma x y z) = true) :
    toReal (fma x y z) =
      roundAt customFormat (toReal x * toReal y + toReal z) := by
  numerics

example (x y : Model customFormat)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (sub x y) = true) :
    toReal x - toReal y ∈ Set.Icc
      (toReal (sub x y) - epsilonAt customFormat (toReal x - toReal y))
      (toReal (sub x y) + epsilonAt customFormat (toReal x - toReal y)) := by
  numerics

example (x : Model customFormat) (hx : isFinite x = true) :
    Represents x (toReal x) := by
  numerics

example : Represents (posOne customFormat) (1 : ℝ) := by
  numerics

example :
    Represents (ofNatBits (fmt := FloatFormat.binary32) 0x3F800000) (1 : ℝ) := by
  numerics

example :
    Represents (ofNatBits (fmt := customFormat) 0xE0) (1 : ℝ) := by
  numerics

example (x y : Model customFormat)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (add x y) = true) :
    Represents (add x y) (roundAt customFormat (toReal x + toReal y)) := by
  numerics

example (x y : Model customFormat) (a b : ℝ)
    (hx : Represents x a) (hy : Represents y b)
    (hout : isFinite (add x y) = true) :
    Represents (add x y) (roundAt customFormat (a + b)) := by
  numerics

example (x y z : Model customFormat) (a b c : ℝ)
    (hx : Represents x a) (hy : Represents y b) (hz : Represents z c)
    (hadd : isFinite (add x y) = true)
    (hout : isFinite (mul (add x y) z) = true) :
    Represents (mul (add x y) z)
      (roundAt customFormat (roundAt customFormat (a + b) * c)) := by
  numerics

example (x y z w : Model customFormat) (a b c d : ℝ)
    (hx : Represents x a) (hy : Represents y b)
    (hz : Represents z c) (hw : Represents w d)
    (hfma : isFinite (fma x y z) = true)
    (hout : isFinite (add (fma x y z) w) = true) :
    Represents (add (fma x y z) w)
      (roundAt customFormat (roundAt customFormat (a * b + c) + d)) := by
  numerics

example (x : Model FloatFormat.binary16) (a : ℝ)
    (hx : Represents x a)
    (hout : isFinite (cast FloatFormat.binary16 customFormat x) = true) :
    Represents (cast FloatFormat.binary16 customFormat x) (roundAt customFormat a) := by
  numerics

example : At customFormat 1 :=
  numerics_refine (ofNatBits (fmt := customFormat) 0xE0)

example : AtValue customFormat (.finite 1) :=
  numerics_refine (ofNatBits (fmt := customFormat) 0xE0)

example : AtValue customFormat (.infinity false) :=
  numerics_refine (posInf customFormat)

example : AtValue customFormat (.infinity true) :=
  numerics_refine (negInf customFormat)

example :
    AtValue customFormat
      (.exceptional (.nan (some 16))) :=
  numerics_refine (canonicalNaN customFormat)

example :
    AtExact customFormat (.finite { negative := false, significand := 0, exponent := 0 }) :=
  numerics_refine (posZero customFormat)

example :
    AtExact customFormat (.finite { negative := true, significand := 0, exponent := 0 }) :=
  numerics_refine (negZero customFormat)

example : AtExact customFormat (.infinity false) :=
  numerics_refine (posInf customFormat)

example : AtExact customFormat (.infinity true) :=
  numerics_refine (negInf customFormat)

example : AtExact customFormat (.nan false false 16) :=
  numerics_refine (canonicalNaN customFormat)

example : AtExact customFormat (.nan true true 1) :=
  numerics_refine (ofFields customFormat true 15 1)

example :
    OutcomeAt customFormat (.infinity false) { divideByZero := true } :=
  numerics_refine (divWithStatus (posOne customFormat) (posZero customFormat))

example :
    OutcomeAt customFormat (.nan false false 16) { invalid := true } :=
  numerics_refine (divWithStatus (posZero customFormat) (posZero customFormat))

example (x : At customFormat (3 : ℝ)) :
    toReal x.1 = 3 := by
  numerics

example (x : At customFormat (3 : ℝ)) :
    toEReal x.1 = ((3 : ℝ) : EReal) := by
  numerics

end FloatLibTests.Conformance.BinaryInterchange.ExecFloatAutomation
