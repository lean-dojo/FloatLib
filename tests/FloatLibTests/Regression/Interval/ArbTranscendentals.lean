/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibTests.Arb.ModelTranscendentals
public import FloatLibTests.Accounting
public import FloatLibTests.Regression.BinaryInterchange.Harness

/-!
# Arb-backed arbitrary-format regression checks

These opt-in IO checks cross the external python-flint trust boundary. They exercise every unary
wrapper over binary16, bfloat16, binary32, and a custom format, then check adaptive scalar rounding
and its explicit failure policy.
-/

@[expose] public section

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.Interval.ArbTranscendentals

open Model
open Model.Interval
open FloatLibTests.Accounting

def customFormat : FloatFormat :=
  FloatFormat.ieee 4 5

def intervalOfRats (fmt : FloatFormat) (lower upper : Rat) : Model.Interval fmt :=
  { lo := Model.roundRatQDown fmt lower
    hi := Model.roundRatQUp fmt upper }

def intervalIsFiniteOrdered {fmt : FloatFormat} (X : Model.Interval fmt) : Bool :=
  Model.isFinite X.lo &&
    Model.isFinite X.hi &&
    Model.Interval.leB X.lo X.hi

def containsValue {fmt : FloatFormat} (X : Model.Interval fmt)
    (x : Model fmt) : Bool :=
  Model.Interval.leB X.lo x && Model.Interval.leB x X.hi

def runCheck (name : String) (check : IO Bool) : IO Nat := do
  try
    let passed ← check
    IO.println s!"{name}: {if passed then "ok" else "FAIL"}"
    pure <| failureCount passed
  catch error =>
    IO.eprintln s!"{name}: ERROR: {error}"
    pure 1

def runIntervalSuite (name : String) (fmt : FloatFormat) : IO Nat := do
  let symmetric := intervalOfRats fmt (-1) 1
  let positive := intervalOfRats fmt (1 / 2) 2
  let nonnegative := intervalOfRats fmt 0 2
  let zero := Model.posZero fmt
  let half := Model.roundRatQ fmt (1 / 2)
  let one := Model.posOne fmt
  let three := Model.roundRatQ fmt 3
  let four := Model.roundRatQ fmt 4
  let mut failures := 0
  failures := failures + (← runCheck s!"{name}.exp.interval" do
    let result ← expArb symmetric (precBits := 128) (digits := 80)
    pure <| intervalIsFiniteOrdered result && containsValue result one)
  failures := failures + (← runCheck s!"{name}.log.interval" do
    let result ← logArb positive (precBits := 128) (digits := 80)
    pure <| intervalIsFiniteOrdered result && containsValue result zero)
  failures := failures + (← runCheck s!"{name}.sinh.interval" do
    let result ← sinhArb symmetric (precBits := 128) (digits := 80)
    pure <| intervalIsFiniteOrdered result && containsValue result zero)
  failures := failures + (← runCheck s!"{name}.cosh.interval" do
    let result ← coshArb symmetric (precBits := 128) (digits := 80)
    pure <| intervalIsFiniteOrdered result && containsValue result one)
  failures := failures + (← runCheck s!"{name}.tanh.interval" do
    let result ← tanhArb symmetric (precBits := 128) (digits := 80)
    pure <| intervalIsFiniteOrdered result && containsValue result zero)
  failures := failures + (← runCheck s!"{name}.sin.interval" do
    let result ← sinArb symmetric (precBits := 128) (digits := 80)
    pure <| intervalIsFiniteOrdered result && containsValue result zero)
  failures := failures + (← runCheck s!"{name}.cos.interval" do
    let result ← cosArb symmetric (precBits := 128) (digits := 80)
    pure <| intervalIsFiniteOrdered result && containsValue result one)
  failures := failures + (← runCheck s!"{name}.sqrt.interval" do
    let result ← sqrtArb nonnegative (precBits := 128) (digits := 80)
    pure <| intervalIsFiniteOrdered result && containsValue result one)
  failures := failures + (← runCheck s!"{name}.sigmoid.interval" do
    let result ← sigmoidArb symmetric (precBits := 128) (digits := 80)
    pure <| intervalIsFiniteOrdered result && containsValue result half)
  failures := failures + (← runCheck s!"{name}.pi.interval" do
    let result ← piArb fmt (precBits := 128) (digits := 80)
    pure <| intervalIsFiniteOrdered result &&
      Model.Interval.leB three result.lo &&
      Model.Interval.leB result.hi four)
  pure failures

def runScalarWrapperSuite : IO Nat := do
  let fmt := FloatFormat.binary16
  let one := Model.posOne fmt
  let two := Model.roundRatQ fmt 2
  let config : ArbRoundingConfig :=
    { initialPrecBits := 128
      initialDigits := 80
      maxAttempts := 4 }
  let mut failures := 0
  failures := failures + (← runCheck "binary16.exp.scalar" do
    pure <| Model.isFinite (← expArbWithRounding one .nearestEven config))
  failures := failures + (← runCheck "binary16.log.scalar" do
    pure <| Model.isFinite (← logArbWithRounding two .nearestEven config))
  failures := failures + (← runCheck "binary16.sinh.scalar" do
    pure <| Model.isFinite (← sinhArbWithRounding one .nearestEven config))
  failures := failures + (← runCheck "binary16.cosh.scalar" do
    pure <| Model.isFinite (← coshArbWithRounding one .nearestEven config))
  failures := failures + (← runCheck "binary16.tanh.scalar" do
    pure <| Model.isFinite (← tanhArbWithRounding one .nearestEven config))
  failures := failures + (← runCheck "binary16.sin.scalar" do
    pure <| Model.isFinite (← sinArbWithRounding one .nearestEven config))
  failures := failures + (← runCheck "binary16.cos.scalar" do
    pure <| Model.isFinite (← cosArbWithRounding one .nearestEven config))
  failures := failures + (← runCheck "binary16.sqrt.scalar" do
    pure <| Model.isFinite (← sqrtArbWithRounding two .nearestEven config))
  failures := failures + (← runCheck "binary16.sigmoid.scalar" do
    pure <| Model.isFinite (← sigmoidArbWithRounding one .nearestEven config))
  failures := failures + (← runCheck "binary16.pi.scalar" do
    pure <| Model.isFinite (← piArbWithRounding fmt .nearestEven config))
  pure failures

def runRoundingModeSuite (name : String) (fmt : FloatFormat) : IO Nat :=
  runCheck s!"{name}.pi.roundingModes" do
    let config : ArbRoundingConfig :=
      { initialPrecBits := 128
        initialDigits := 80
        maxAttempts := 4 }
    let nearest ← piArbWithRounding fmt .nearestEven config
    let towardZero ← piArbWithRounding fmt .towardZero config
    let upward ← piArbWithRounding fmt .towardPositiveInfinity config
    let downward ← piArbWithRounding fmt .towardNegativeInfinity config
    pure <|
      Model.isFinite nearest &&
      Model.isFinite towardZero &&
      Model.isFinite upward &&
      Model.isFinite downward &&
      BinaryInterchange.Harness.sameBits towardZero downward &&
      Model.Interval.leB downward nearest &&
      Model.Interval.leB nearest upward

def zeroAttemptRejected : IO Bool := do
  try
    discard <|
      piArbWithRounding FloatFormat.binary16 .nearestEven
        { initialPrecBits := 32, initialDigits := 20, maxAttempts := 0 }
    pure false
  catch _ =>
    pure true

def run : IO Nat := do
  let mut failures := 0
  failures := failures + (← runIntervalSuite "binary16" FloatFormat.binary16)
  failures := failures + (← runIntervalSuite "bfloat16" FloatFormat.bfloat16)
  failures := failures + (← runIntervalSuite "binary32" FloatFormat.binary32)
  failures := failures + (← runIntervalSuite "custom-e4m5" customFormat)
  failures := failures + (← runScalarWrapperSuite)
  failures := failures + (← runRoundingModeSuite "binary16" FloatFormat.binary16)
  failures := failures + (← runRoundingModeSuite "bfloat16" FloatFormat.bfloat16)
  failures := failures + (← runRoundingModeSuite "binary32" FloatFormat.binary32)
  failures := failures + (← runRoundingModeSuite "custom-e4m5" customFormat)
  failures := failures + (← runCheck "zeroAttemptRejected" zeroAttemptRejected)
  pure failures

end FloatLibTests.Regression.Interval.ArbTranscendentals
