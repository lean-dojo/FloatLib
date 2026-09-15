/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Shared finite-prefix execution helpers

Division, square root, and other non-dyadic operations generate a finite integer prefix plus an
exact indication that more nonzero digits follow. This module contains the format-independent
operation that turns that indication into a sticky low bit.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.StickyPrefix

/-- Preserve an exact prefix; set its low bit when the remainder is nonzero. -/
@[inline] def jamRemainder (value remainder : Nat) : Nat :=
  if remainder == 0 then value else value ||| 1

end FloatLib.Floats.Formats.Posit.Model.StickyPrefix
