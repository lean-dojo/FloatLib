/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Runtime

/-!
# Sums of magnitudes and of squares

IEEE 754-2019 §9.4 recommends the reductions `sum`, `dot`, `sumSquare` and `sumAbs` on vectors of
one format. The clause number is the one in the 754 working group's list of changes from 754-2008
(<https://grouper.ieee.org/groups/msc/ANSI_IEEE-Std-754-2019/background/>), and the operation
names and special cases are those of their C binding, ISO/IEC TS 18661-4 (WG14 draft N1797,
7.12.13a and F.10.10a), which names them `reduc_sum`, `reduc_sumprod`, `reduc_sumsq` and
`reduc_sumabs`. `Model.sum` and `Model.dot` are the first two. This module adds the other two.

The standard lets an implementation associate in any order and evaluate in any wider format.
`sumAbs` and `sumSquare` take the limit of that freedom, as `sum` and `dot` do: every finite
operand is decoded without error, the magnitudes or the squares are added in the exact dyadic
domain, and the result is rounded once into `destination`, in any rounding direction. Source and
destination formats may differ. The reductions that round at every step, in a chosen order and
accumulator format, are `Numerics.ReductionTree` and `Model.mulAcc`.

Their special cases differ from those of `sum` and `dot` in one point (N1797 F.10.10a.2 and
F.10.10a.3): the result is `+∞` if any operand is an infinity, and only otherwise a NaN if an
operand is a NaN. A signaling NaN operand still gives a quiet NaN and raises `invalid`, as
IEEE 754-2019 §6.2 requires of every operation that computes. So both reductions first look for
the operand that decides: `Reduction.Internal.decidingInfinity?`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
The infinite operand that decides a sum of magnitudes or of squares: the first infinity, when no
operand is a signaling NaN.
-/
def Reduction.Internal.decidingInfinity? {source : FloatFormat}
    (values : Array (Model source)) : Option (Model source) :=
  if values.any isSignaling then none else values.find? isInfinite

/--
IEEE 754-2019 §9.4 `sumAbs` (C `reduc_sumabs`, N1797 7.12.13a.2 and F.10.10a.2): the sum of the
magnitudes of an array, formed without error and rounded once into `destination` in `mode`
(nearest-even by default). An infinite operand gives `+∞` even beside a quiet NaN, a signaling
NaN gives a quiet NaN and `invalid`, and the empty sum is `+0`. With `status := true` the result
is the `IEEEOutcome` carrying the exception flags and the ternary value of the one rounding.
-/
@[macro_inline] def sumAbs (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode := .nearest)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome destination
    | false => Model destination :=
  match Reduction.Internal.decidingInfinity? values with
  | some infinity => sum destination #[abs infinity] mode status
  | none => sum destination (values.map abs) mode status

/--
IEEE 754-2019 §9.4 `sumSquare` (C `reduc_sumsq`, N1797 7.12.13a.3 and F.10.10a.3): the sum of the
squares of an array, formed without error and rounded once into `destination` in `mode`
(nearest-even by default). An infinite operand gives `+∞` even beside a quiet NaN, a signaling
NaN gives a quiet NaN and `invalid`, and the empty sum is `+0`. With `status := true` the result
is the `IEEEOutcome` carrying the exception flags and the ternary value of the one rounding.
-/
@[macro_inline] def sumSquare (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode := .nearest)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome destination
    | false => Model destination :=
  match Reduction.Internal.decidingInfinity? values with
  | some infinity => sum destination #[abs infinity] mode status
  | none =>
      match status with
      | true =>
          (Reduction.Internal.dotState values values rfl :
            Reduction.Internal.State destination).finish mode
      | false =>
          (Reduction.Internal.dotState values values rfl :
            Reduction.Internal.State destination).finishValue mode

end Model
end FloatLib.Floats.Formats.BinaryInterchange
