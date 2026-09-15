/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Finite

/-!
# Exact finite-operation automation checks

These examples exercise exact dyadic representation and checked finite arithmetic through the
same `Model fmt` carrier.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.ExactAutomation

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model
open FloatLib.Numerics

example {fmt : FloatFormat} {value : FloatLib.Numerics.Dyadic}
    (x : ExactAtFinite fmt value) :
    ExactAtFinite fmt (Model.negDyadic fmt value) :=
  numerics_refine (Model.neg x.1)

example {fmt : FloatFormat} {leftValue rightValue : FloatLib.Numerics.Dyadic}
    (left : ExactAtFinite fmt leftValue) (right : ExactAtFinite fmt rightValue) :
    Option.map (exactNumericalSystem fmt).denote
        (Model.mulFinite? fmt QuantizationPolicy.nearestEven 0 left.1 right.1) =
      some (Model.quantizedValue fmt QuantizationPolicy.nearestEven 0
        (Model.mulDyadic leftValue rightValue)) := by
  numerics

example {fmt : FloatFormat} {leftValue rightValue : FloatLib.Numerics.Dyadic}
    (left : ExactAtFinite fmt leftValue) (right : ExactAtFinite fmt rightValue) :
    (exactNumericalSystem fmt).At
      (Model.quantizedValue fmt QuantizationPolicy.nearestEven 0
        (FloatLib.Floats.Formats.BinaryInterchange.Model.addDyadic leftValue rightValue)) :=
  Operation.Checked2.applyAt
    (Model.addFinite_refines fmt QuantizationPolicy.nearestEven 0) left right

example :
    Model.toDyadic? (Model.ofNatBits (fmt := FloatFormat.e2m1) 7) =
      some { negative := false, significand := 3, exponent := 1 } := by
  numerics_reduce

end FloatLibTests.Conformance.BinaryInterchange.ExactAutomation
