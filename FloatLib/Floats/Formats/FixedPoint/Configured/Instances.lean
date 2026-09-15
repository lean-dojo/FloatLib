/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Instances -- shake: keep
public import FloatLib.Floats.Formats.FixedPoint.Configured.Plan
public import FloatLib.Floats.ExecFloat.Core.Capability

/-!
# Literal and dispatch instances for exact fixed point

Literals use exact integer embedding or one rational ties-to-even rounding step. Same-scale
addition and subtraction dispatch to their certified direct kernels.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.FixedPoint

open FloatLib.Numerics

variable {radix : Radix} {fractionalDigits : Nat}

instance : Neg (ExecFloat.FixedPoint radix fractionalDigits) where
  neg := FixedPoint.neg

/-- Natural literals are embedded exactly into the configured fixed-point grid. -/
instance (value : Nat) :
    OfNat (ExecFloat.FixedPoint radix fractionalDigits) value where
  ofNat :=
    ofCoefficient ((value * scale radix fractionalDigits : Nat) : Int)

/--
Decimal and scientific literals are rounded once from an exact rational to nearest, ties to even.
-/
instance : OfScientific (ExecFloat.FixedPoint radix fractionalDigits) where
  ofScientific mantissa exponentSign decimalExponent :=
    roundRat
      (OfScientific.ofScientific mantissa exponentSign decimalExponent : Rat)

/-- Same-scale fixed-point addition participates in ordinary `ExecFloat` dispatch. -/
@[always_inline] instance
    [planning : Backend.PolicyFor (Family radix fractionalDigits)] :
    ExecFloat.Add (Family radix fractionalDigits) :=
  ExecFloat.Capability.ofDirectKernel
    .add FixedPoint.add Plan.addCertified FixedPoint.add rfl

/-- Same-scale fixed-point subtraction participates in ordinary `ExecFloat` dispatch. -/
@[always_inline] instance
    [planning : Backend.PolicyFor (Family radix fractionalDigits)] :
    ExecFloat.Sub (Family radix fractionalDigits) :=
  ExecFloat.Capability.ofDirectKernel
    .sub FixedPoint.sub Plan.subCertified FixedPoint.sub rfl

end FloatLib.Floats.ExecFloat.FixedPoint
