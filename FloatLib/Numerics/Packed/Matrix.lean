/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Basic

/-!
# Matrix products on packed rows

Let `A` have `n` rows and `B` have `p` columns, with `m` columns of `A` and `m` rows of `B`. The
product `A * B` is the sum over `k < m` of the outer products of column `k` of `A` with row `k`
of `B`. On packed rows an outer product is one multiplication: with column `k` of `A` in lanes of
`w` bits and row `k` of `B` in lanes of `w * n` bits, the product of the two integers has
`A[i][k] * B[k][j]` in lane `i + n * j`. So `m` multiplications and `m` additions of large integers
give all `n * p` entries of the product, where entry-by-entry arithmetic takes `n * m * p` steps of
the kernel.

`matMulCheck w gA gB n p cols rows prod` checks a product that is given: that `A` has as many
columns as `B` has rows, the range of every entry of `A` and `B` (`guard`), the headroom that keeps
every entry of the product inside its lane, and the equality of the integer of `prod` with the sum
of the `m` products. `FloatLib.Numerics.Packed.MatrixProof` proves `length_eq_of_matMulCheck` and
`entries_matMul`: after a passing check the inner dimensions agree and the entries of `prod` are
those of `colRowProduct`, the matrix product in the same layout. A column is `n` lanes and a row
`p` lanes by its layout, so the three dimensions of a passing check are those of a product.

## Main definitions

* `outer`, `sumRows`, `colRowProduct`: the specification on lists of integers.
* `outerSum`, `guardAll`, `count`, `matMulCheck`: the kernel programs.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

open FloatLib.Numerics.Kernel

/-- The outer product of a column `xs` and a row `ys`, as one row: the entries `x * y`, column
after column of the result. Entry `i + xs.length * j` is `xs[i] * ys[j]`. -/
def outer (xs ys : List Int) : List Int := (ys.map fun y => smul y xs).flatten

/-- The lanewise sum of a list of rows. -/
def sumRows : List (List Int) → List Int
  | [] => []
  | row :: rows => add row (sumRows rows)

/-- The product of the matrix with columns `cols` and the matrix with rows `rows`, as one row:
the sum of the outer products of column `k` with row `k`. With `n` entries per column, entry
`i + n * j` is `∑ k, cols[k][i] * rows[k][j]`. The sum stops at the shorter list, so it is the
matrix product only when there are as many columns as rows, which `matMulCheck` tests. -/
def colRowProduct (cols rows : List (List Int)) : List Int :=
  sumRows (List.zipWith outer cols rows)

/-- The number of rows of a list, counted with one kernel step per row. -/
noncomputable def count (us : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ k => Nat.succ k) us

/-- Whether every row of `us` passes `guard w g n`. -/
noncomputable def guardAll (w g n : Nat) (us : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun u _ ok => Bool.and (guard w g n u) ok) us

/-- The integer `∑ k, toInt w n cols[k] * toInt v p rows[k]`, one product per pair. -/
noncomputable def outerSum (w n v p : Nat) (cols rows : List Nat) : Int :=
  List.rec (motive := fun _ => List Nat → Int) (fun _ => Int.ofNat 0)
    (fun c _ step rows =>
      List.rec (motive := fun _ => Int) (Int.ofNat 0)
        (fun r rest _ =>
          Z.add (Z.mul (Z.subNat c (bias w n)) (Z.subNat r (bias v p))) (step rest))
        rows)
    cols rows

/--
Whether the biased row `prod` of `n * p` lanes of `w` bits holds the product of the matrix whose
columns are the rows `cols` (`n` lanes of `w` bits, entries in `[-2 ^ gA, 2 ^ gA)`) with the
matrix whose rows are `rows` (`p` lanes of `w * n` bits, entries in `[-2 ^ gB, 2 ^ gB)`). The
first test is the inner dimension: as many columns as rows. The fourth is the headroom: as many
terms as there are columns, each below `2 ^ gA * 2 ^ gB`, stay below `2 ^ (w - 1)`.
-/
noncomputable def matMulCheck (w gA gB n p : Nat) (cols rows : List Nat) (prod : Nat) : Bool :=
  Bool.and (Nat.beq (count cols) (count rows))
    (Bool.and (guardAll w gA n cols)
      (Bool.and (guardAll (Nat.mul w n) gB p rows)
        (Bool.and
          (Nat.ble (Nat.succ (Nat.mul (count cols) (Nat.mul (pow2 gA) (pow2 gB))))
            (pow2 (Nat.sub w 1)))
          (Int.beq' (Z.subNat prod (bias w (Nat.mul n p)))
            (outerSum w n (Nat.mul w n) p cols rows)))))

end FloatLib.Numerics.Packed
