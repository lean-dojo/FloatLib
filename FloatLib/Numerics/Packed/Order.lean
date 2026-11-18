/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Basic

/-!
# Many comparisons with one subtraction

`lanesLe w n u v` decides `u[k] ≤ v[k]` for all `n` lanes of two rows at once. Both rows hold
natural numbers below `2 ^ (w - 1)`, so the top bit of every lane is free. Setting that bit in
every lane of `v` and subtracting `u` leaves it set exactly in the lanes where `u[k] ≤ v[k]`: a
lane with `u[k] > v[k]` borrows from its own top bit and from no other lane. One conjunction with
the row of top bits and one comparison read all the answers.

The program checks the range of both rows itself (`guard`), so `lanesLe_sound` in
`FloatLib.Numerics.Packed.OrderProof` has no side condition on the data.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

/--
Whether lane `k` of `u` is at most lane `k` of `v` for every `k < n` (`lanesLe_sound`), for two
rows of `n` lanes of `w` bits with every lane below `2 ^ (w - 1)`, which is checked as well.
-/
def lanesLe (w n u v : Nat) : Bool :=
  Bool.and (guard w (Nat.sub w 1) n u (signed := false))
    (Bool.and (guard w (Nat.sub w 1) n v (signed := false))
      (Nat.beq (Nat.land (Nat.sub (Nat.add v (bias w n)) u) (bias w n)) (bias w n)))

end FloatLib.Numerics.Packed
