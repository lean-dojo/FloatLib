/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Total bounded integer bisection

The predicate supplies the comparison domain; the search uses only natural indices.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
Shared bounded bisection over an unsigned code interval.

`accept code` states that `code` is still on the lower side of the target boundary. Separating
the search from the comparison domain lets the exact-rational specification and certified
integer implementations follow literally the same control flow.
-/
@[inline] def bisect (accept : Nat → Bool) :
    Nat → Nat → Nat → Nat
  | 0, lower, _ => lower
  | fuel + 1, lower, upper =>
      if lower + 1 < upper then
        let middle := (lower + upper) / 2
        if accept middle then
          bisect accept fuel middle upper
        else
          bisect accept fuel lower middle
      else
        lower

end FloatLib.Numerics
