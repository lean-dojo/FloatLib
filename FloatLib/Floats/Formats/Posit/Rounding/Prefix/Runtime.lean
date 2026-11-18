/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Init -- Standard source linters.

/-!
# Shared finite-prefix execution helpers

Division, square root, and the other non-dyadic operations produce a finite integer prefix of the
result and a remainder that tells whether any nonzero digits follow. `jamRemainder` folds that
remainder into the low bit of the prefix, the sticky bit, in the same way for every format.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.StickyPrefix

/-- Keep the prefix when the remainder is zero, and otherwise set its low bit. -/
@[inline] def jamRemainder (value remainder : Nat) : Nat :=
  if remainder == 0 then value else value ||| 1

end FloatLib.Floats.Formats.Posit.Model.StickyPrefix
