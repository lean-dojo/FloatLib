/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Form
public import FloatLib.Kernels.Execution.Instances -- shake: keep
public import FloatLib.Floats.Formats.FixedPoint.Configured.Plan

/-!
# Literal and dispatch instances for exact fixed point

A natural-number literal lands on the grid with no rounding. A decimal or scientific literal takes
one rational rounding step, ties to even, so `2.5` with no fractional digits becomes `2`.
Same-scale addition and subtraction dispatch to their certified direct kernels.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.FixedPoint

open FloatLib.Numerics

variable {radix : Radix} {fractionalDigits : Nat}

instance : Neg (ExecFloat.FixedPoint radix fractionalDigits) where
  neg := FixedPoint.neg

/-- Natural literals land on the configured fixed-point grid with no rounding. -/
instance (value : Nat) :
    OfNat (ExecFloat.FixedPoint radix fractionalDigits) value where
  ofNat :=
    ofCoefficient ((value * scale radix fractionalDigits : Nat) : Int)

/--
Decimal and scientific literals are rounded once from an exact rational to nearest, ties to even.
-/
instance : OfScientific (ExecFloat.FixedPoint radix fractionalDigits) where
  ofScientific mantissa exponentSign decimalExponent :=
    ofRat
      (OfScientific.ofScientific mantissa exponentSign decimalExponent : Rat)

/--
Same-scale fixed-point addition participates in ordinary `ExecFloat` dispatch: the planner
selects among the exact baseline and every candidate tagged `@[compiler_optimize]` for
`FixedPoint.add`.
-/
@[always_inline] instance
    [planning : Backend.PolicyFor (Family radix fractionalDigits)]
    [portfolio : Backend.Portfolio
      (FixedPoint.add (radix := radix) (fractionalDigits := fractionalDigits))] :
    ExecFloat.Add (Family radix fractionalDigits) :=
  ExecFloat.Capability.ofTagged .add portfolio Plan.addCertified FixedPoint.add rfl

/--
Same-scale fixed-point subtraction participates in ordinary `ExecFloat` dispatch, with the
candidates tagged for `FixedPoint.sub`.
-/
@[always_inline] instance
    [planning : Backend.PolicyFor (Family radix fractionalDigits)]
    [portfolio : Backend.Portfolio
      (FixedPoint.sub (radix := radix) (fractionalDigits := fractionalDigits))] :
    ExecFloat.Sub (Family radix fractionalDigits) :=
  ExecFloat.Capability.ofTagged .sub portfolio Plan.subCertified FixedPoint.sub rfl

/--
Lean's kernel evaluates same-scale addition as the sum of the two integer coefficients: the
reference operation is the kernel operation.
-/
instance [Backend.PolicyFor (Family radix fractionalDigits)]
    [Backend.Portfolio (FixedPoint.add (radix := radix) (fractionalDigits := fractionalDigits))] :
    KernelPath.DirectReference (Family radix fractionalDigits) .add where

/-- Lean's kernel evaluates same-scale subtraction as the difference of the coefficients. -/
instance [Backend.PolicyFor (Family radix fractionalDigits)]
    [Backend.Portfolio (FixedPoint.sub (radix := radix) (fractionalDigits := fractionalDigits))] :
    KernelPath.DirectReference (Family radix fractionalDigits) .sub where

end FloatLib.Floats.ExecFloat.FixedPoint
