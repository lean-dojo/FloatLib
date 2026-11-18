/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Backends
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime

/-!
# Rational enclosures of closed expressions

A closed expression, with rational constants and no inputs, denotes one real number.
`Expr.gridEnclosure?` evaluates it with the binary-grid backend and returns rational endpoints,
or `none` when an operation rejects its input. `Expr.gridEnclosureWith?` does the same for an
expression whose inputs are reals known by rational enclosures. `ClosedProof` proves that the
endpoints enclose the real value.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- The interval of the grid of `precision` fractional bits around a rational interval. -/
def gridOfRational (precision : Nat) (interval : RationalInterval) : Interval Int :=
  ⟨(BinaryGrid.enclose precision interval.lo).lo, (BinaryGrid.enclose precision interval.hi).hi⟩

/--
Enclose the real value of an expression between rationals, evaluating on the grid of
`precision` fractional bits with elementary functions of the given `degree`. The variable `i`
stands for a real in the `i`th interval of `inputs`.
-/
def Expr.gridEnclosureWith? (e : Expr) (inputs : List RationalInterval)
    (precision degree : Nat) : Option RationalInterval :=
  (e.eval? (Backend.binaryGrid { precision := precision, degree := degree })
    (fun i => inputs[i]?.map (gridOfRational precision))).map
      (Enclosure.BinaryGrid.toRationalInterval precision)

/--
Enclose the real value of a closed expression between rationals, evaluating on the grid of
`precision` fractional bits with elementary functions of the given `degree`.
-/
def Expr.gridEnclosure? (e : Expr) (precision degree : Nat) : Option RationalInterval :=
  e.gridEnclosureWith? [] precision degree

end FloatLib.Numerics.Interval
