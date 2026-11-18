/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
-- architecture: allow-proof-imports
The adaptive search carries an erased proof that a separating interval exists.
-/

module

public import FloatLib.Numerics.Exact.Softplus.Enclosure

/-!
# Exact Softplus comparison

Compare `log(1 + exp(argument))` with any rational boundary. The function
exceeds both zero and its argument. Above those immediate bounds, the
adaptive search compares two decaying exponentials with one.
-/

@[expose] public section

namespace FloatLib.Numerics.Softplus

/-- Exact comparison of Softplus with a rational boundary, with unbounded adaptive refinement. -/
def compare (argument boundary : ℚ) : Ordering :=
  if hpositive : 0 < boundary then
    if habove : argument < boundary then
      Enclosure.Comparison.compare (fun level => interval argument boundary (2 ^ level)) 1
        (exists_separating argument boundary hpositive habove)
    else .gt
  else .gt

end FloatLib.Numerics.Softplus
