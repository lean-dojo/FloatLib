/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.ExtendedRat.Runtime

/-!
# Ordered reductions of extended-rational products

The state, step and final observation are independent parameters. The exact instance
uses the shared closed arithmetic and a positive-zero identity.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Numerics

/-- OCP MX v1.0, §6.1: the intermediate state and operations of an ordered reduction. -/
structure Reduction where
  /-- Storage for an intermediate sum. -/
  State : Type
  /-- State before consuming any products. -/
  initial : State
  /-- Consume one exact extended-rational product. -/
  step : State → NumericalValue Rat → State
  /-- Decode the final state for the output conversion. -/
  finish : State → NumericalValue Rat

namespace Reduction

/-- Fold exact products in their specified order, retaining the implementation's state. -/
def fold (reduction : Reduction) (values : List (NumericalValue Rat)) : reduction.State :=
  values.foldl reduction.step reduction.initial

/-- Decode the final state after the specified ordered fold. -/
def run (reduction : Reduction) (values : List (NumericalValue Rat)) : NumericalValue Rat :=
  reduction.finish (reduction.fold values)

/-- Exact intermediates, with closed extended-rational addition and a positive-zero identity. -/
def exact : Reduction where
  State := NumericalValue Rat
  initial := .finite 0
  step := P3109.Arithmetic.Add
  finish := id

end Reduction

end FloatLib.Floats.Formats.Block
