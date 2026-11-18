/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Seq
public import FloatLib.Numerics.Packed.Basic

/-!
# The dot product of two packed rows

The product of two rows is the row of their Cauchy product (Kronecker). If one of the rows is
packed in the opposite order, the lane `n - 1` of the product holds the dot product of the two
lists: for `x 0, …, x (n - 1)` packed with `x 0` in the highest lane and `w 0, …, w (n - 1)`
packed with `w 0` in lane zero,

  `(∑ x i * B ^ (n - 1 - i)) * (∑ w j * B ^ j)` has the coefficient `∑ x i * w i` at `B ^ (n - 1)`.

So a dot product of two lists of `n` natural numbers is one multiplication of two numbers of
`n` lanes, one shift and one mask (`dot`), provided coefficients cannot carry between lanes.
Packing still traverses the input. A row used in several products can be packed once and reused.

* `packRev w l` packs a list of naturals with its first member in the highest lane, and
  `packFwd w l` with its first member in lane zero. Both walk the list once and build the row 64
  lanes at a time, so the kernel copies the growing row once per 64 members and not once per
  member. Use them for rows that the kernel derives from other data, and `packed_row` for given
  data.
* `dot w n a b` is the lane `n - 1` of `a * b`. The row `b` may have more than `n` lanes: the
  lanes above `n - 1` of `b` do not reach the lane `n - 1` of the product, so one packed row of
  weights serves every shorter list.

`FloatLib.Numerics.Packed.DotProof` proves that the lanes of the two packed rows are the lists
(`lanes_packRev`, `lanes_packFwd`) and that `dot` of them is the dot product when the lanes have
room (`dot_eq`). Besides the unsigned `guard` checks, the theorem requires positive first length
`n`, second length `m ≥ n`, inputs below `2 ^ w`, and
`n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ w` for the guard widths `gx`, `gy`.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

open FloatLib.Numerics.Kernel

/-- The steps of `packRev`: `outer` holds the whole chunks so far, `inner` the `cnt` lanes of
the chunk at hand. -/
noncomputable def packGo (w : Nat) (l : List Nat) : Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun outer inner cnt => Nat.add (Nat.shiftLeft outer (Nat.mul cnt w)) inner)
    (fun x _ rest outer inner cnt =>
      strict (Nat.add (Nat.shiftLeft inner w) x) fun inner' =>
        Bool.casesOn (motive := fun _ => Nat) (Nat.beq cnt 63)
          (rest outer inner' (Nat.succ cnt))
          (strict (Nat.add (Nat.shiftLeft outer (Nat.mul 64 w)) inner') fun outer' =>
            rest outer' 0 0))
    l

/-- The unsigned row of a list with its first member in the highest lane:
`∑ l[i] * 2 ^ (w * (n - 1 - i))`, built 64 lanes at a time (`packRev_eq`). -/
noncomputable def packRev (w : Nat) (l : List Nat) : Nat := packGo w l 0 0 0

/-- The unsigned row of a list with its first member in lane zero: `∑ l[i] * 2 ^ (w * i)`
(`packFwd_eq`). -/
noncomputable def packFwd (w : Nat) (l : List Nat) : Nat := packRev w (Seq.reverse l)

/-- The lane `n - 1` of the product `a * b`: the dot product of a list of `n` members with the
first `n` members of another, for `a` packed by `packRev` and `b` packed by `packFwd`
(`dot_eq`). -/
def dot (w n a b : Nat) : Nat := lane w (Nat.sub n 1) (Nat.mul a b)

end FloatLib.Numerics.Packed
