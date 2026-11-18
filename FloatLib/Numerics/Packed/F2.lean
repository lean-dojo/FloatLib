/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Basic

/-!
# Matrices over the field of two elements, one row per lane

A row of a matrix over `𝔽₂` is a natural number whose bit `k` is the entry in column `k`, and the
sum of two rows is their exclusive disjunction. The product of a row `b` with a matrix `M`, given
by its rows, is the sum of the rows of `M` that the bits of `b` select (`rowMul`), which costs
one interpreted step per entry when done row by row.

`mul w n B M` computes the products of all `n` rows of a matrix at once. The matrix `B` is one
number with a row in each lane of `w` bits. For each row `m` of `M`, in turn, it reads the bit of
that column in every lane with one shift and one mask, multiplies the resulting row of zeros and
ones by `m`, which places `m` in the selected lanes, and adds that to the result with one
exclusive disjunction. That is one step per row of `M` instead of one per entry.

`isInverse w n B M` checks with it that `B * M` is the identity of size `n`: lane `i` of the
product must be `2 ^ i`. It also checks the shape (`square`): `M` has exactly `n` rows, each below
`2 ^ n`, and `n ≤ w`, which makes the lanes independent (`fits`: at most `w` rows, each below
`2 ^ w`). The bits of a lane of `B` from position `n` on are not read, since `M` has `n` rows.
`FloatLib.Numerics.Packed.F2Proof` proves `lane_mul`, `isInverse_sound` and `isInverse_square`.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed.F2

/-- The row `b` times the matrix with rows `M`, over `𝔽₂`: the sum of the rows that the bits of
`b` select. -/
def rowMul : Nat → List Nat → Nat
  | _, [] => 0
  | b, m :: M => Nat.xor (Nat.mul m (Nat.land b 1)) (rowMul (Nat.shiftRight b 1) M)

/--
The products of all rows of `B` with the matrix `M`, over `𝔽₂` (`lane_mul`): lane `i` of the
result is `rowMul` of lane `i` of `B`, for `i < n`.
-/
noncomputable def mul (w n B : Nat) (M : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun m _ step k acc =>
      step (Nat.succ k)
        (Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight B k) (ones w n)) m)))
    M 0 0

/-- Whether `M` has at most `w` rows and each of them is below `2 ^ w`. -/
noncomputable def fits (w : Nat) (M : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.ble k w)
    (fun m _ step k => Bool.and (Nat.beq (Nat.shiftRight m w) 0) (step (Nat.succ k)))
    M 0

/-- Whether lane `i` of `R` is `2 ^ i` for every `i < n`. -/
noncomputable def unitLanes (w R n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ok => Bool.and (Nat.beq (lane w i R) (Nat.shiftLeft 1 i)) ok) n

/-- Whether `M` has exactly `n` rows and each of them is below `2 ^ n`: the rows of an `n` by
`n` matrix (`square_iff`). -/
noncomputable def square (n : Nat) (M : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k n)
    (fun m _ step k => Bool.and (Nat.beq (Nat.shiftRight m n) 0) (step (Nat.succ k)))
    M 0

/--
Whether `M` is an `n` by `n` matrix over `𝔽₂`, given by its rows, and `B * M` is the identity
matrix of size `n` (`isInverse_sound`, `isInverse_square`), with the rows of `B` in the lanes of
`w ≥ n` bits of one number. A matrix `M` of another shape is rejected.
-/
noncomputable def isInverse (w n B : Nat) (M : List Nat) : Bool :=
  Bool.and (Nat.ble n w) (Bool.and (square n M) (unitLanes w (mul w n B M) n))

end FloatLib.Numerics.Packed.F2
