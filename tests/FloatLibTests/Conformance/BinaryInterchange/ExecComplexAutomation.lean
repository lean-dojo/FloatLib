/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Automation

/-!
# Regression checks for complex numerical automation

The examples ensure complex values use the common operation contracts while retaining their
explicit componentwise and six-rounding-site semantics.
-/

@[expose] public section

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Conformance.BinaryInterchange.ExecComplexAutomation

open ExecComplex

abbrev customFormat : FloatFormat :=
  FloatFormat.ieee 5 7

example {value : ℂ} (z : At customFormat value) :
    At customFormat (-value) :=
  numerics_refine (ExecComplex.neg z.1)

example {value : ℂ} (z : At customFormat value) :
    At customFormat (starRingEnd ℂ value) :=
  numerics_refine (ExecComplex.conj z.1)

example {left right : ℂ}
    (x : At customFormat left) (y : At customFormat right)
    (hout : isFinite (ExecComplex.add x.1 y.1) = true) :
    At customFormat (roundedAdd customFormat left right) :=
  numerics_refine (ExecComplex.add x.1 y.1)

example {left right : ℂ}
    (x : At customFormat left) (y : At customFormat right)
    (hout : isFinite (ExecComplex.sub x.1 y.1) = true) :
    At customFormat (roundedSub customFormat left right) :=
  numerics_refine (ExecComplex.sub x.1 y.1)

example {left right : ℂ}
    (x : At customFormat left) (y : At customFormat right)
    (hfinite : MulFinite x.1 y.1) :
    At customFormat (roundedMul customFormat left right) :=
  numerics_refine (ExecComplex.mul x.1 y.1)

end FloatLibTests.Conformance.BinaryInterchange.ExecComplexAutomation
