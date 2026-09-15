/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Low-level rational rounding primitives

Format-independent executable quotient operations support nearest-even and directed rational
rounding. The quotient layer stays below `Model.Arithmetic`, allowing native arithmetic kernels
to reuse their proofs without creating an import cycle through the public dispatcher.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Ceiling of a natural quotient, totalized to zero at a zero denominator. -/
@[inline] def quotCeil (numerator denominator : Nat) : Nat :=
  if denominator == 0 then
    0
  else
    let quotient := numerator / denominator
    let remainder := numerator % denominator
    if remainder == 0 then quotient else quotient + 1

/-- Round a nonnegative quotient to an integer, selecting floor or ceiling. -/
@[inline] def roundQuotDirected (roundUp : Bool) (numerator denominator : Nat) : Nat :=
  if roundUp then quotCeil numerator denominator else numerator / denominator

end Model
end FloatLib.Floats.Formats.BinaryInterchange
