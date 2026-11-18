/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy

/-!
# Executable nearest-even rounding refinement

The IEEE compatibility theorem follows from the descriptor-general policy theorem:
finite IEEE output excludes overflow and its encoding never saturates.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats FloatLib.Floats.Formats.Flocq FloatLib.Numerics

/--
Executable dyadic rounding refines the rounded-real semantics for conventional IEEE descriptors.

The finiteness hypothesis excludes the one case that has no value in `ℝ`: IEEE overflow to
infinity. Custom widths are allowed when they satisfy the IEEE-descriptor condition.
-/
theorem toReal_roundDyadic_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (d : Numerics.Dyadic)
    (hfin : isFinite (roundDyadic fmt d) = true) :
    toReal (roundDyadic fmt d) = roundAt fmt d.toReal := by
  simpa [((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1] using
    toReal_roundDyadic_policy fmt d hfin

end FloatLib.Floats.Formats.BinaryInterchange.Model
