/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.Accumulation

/-!
# Mixed-precision matrix multiplication

Each output entry is a left-to-right `dotSequential` reduction under one `SitePolicy`. Products
round in the product format, additions round in the accumulator format, and the completed entry
is cast to the output format.

Matrices are row-major arrays: `M[i][j]` is row `i`, column `j`. `matmul` checks that both inputs
are rectangular and that the left row width equals the number of right rows. An empty matrix has
zero columns because this representation carries no width without a row.

For an `m × k` matrix times a `k × n` matrix, the implementation extracts the right-hand columns
once and computes `m * n` sequential dots of length `k`. `MatmulProof` proves that every successful
output has this shape and these entries, then applies the dot-product error bound entrywise.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Row-major matrix of `Model`s: outer array = rows, inner array = entries in that row.
-/
abbrev Matrix (fmt : FloatFormat) := Array (Array (Model fmt))

/-- Shape failures rejected before matrix multiplication begins. -/
inductive MatrixShapeError where
  /-- Rows of the left input do not all have the first row's width. -/
  | raggedLeft (expectedColumns : Nat)
  /-- Rows of the right input do not all have the first row's width. -/
  | raggedRight (expectedColumns : Nat)
  /-- The left row width differs from the number of right rows. -/
  | innerDimensionMismatch (leftColumns rightRows : Nat)
  /-- A checked row and column nevertheless reached the dot kernel with different lengths. -/
  | dotLengthMismatch (rowLength columnLength : Nat)
  deriving Repr, DecidableEq

/-- Column count from the first row; `0` if there are no rows. -/
@[inline] def ncols {fmt : FloatFormat} (M : Matrix fmt) : Nat :=
  if h : 0 < M.size then M[0].size else 0

/--
Extract column `j` as a length-`M.size` vector (one entry per row).

**Precondition (unchecked):** every row has length `> j`.
-/
def column {fmt : FloatFormat} (M : Matrix fmt) (j : Nat) : Array (Model fmt) :=
  M.map fun row => row[j]!

/--
Mixed-precision matmul under site policy `p`:

```text
C[i][j] = dotSequential p (row i of A) (column j of B)
```

- `A`, `B` entries are in `p.storage`.
- Each inner product uses `p.product` / `p.accumulator` as in `dotSequential`.
- Entries of `C` are in `p.output`.

On success, `C` has `A.size` rows and `ncols B` columns. Both inputs must be rectangular and the
left row width must equal `B.size`; otherwise the corresponding `MatrixShapeError` is returned.
-/
def matmul (p : SitePolicy) (A B : Matrix p.storage) :
    Except MatrixShapeError (Matrix p.output) :=
  let m := A.size
  let k := ncols A
  let n := ncols B
  if A.any (fun row => row.size != k) then
    .error (.raggedLeft k)
  else if B.any (fun row => row.size != n) then
    .error (.raggedRight n)
  else if k != B.size then
    .error (.innerDimensionMismatch k B.size)
  else
    let cols : Array (Array (Model p.storage)) :=
      Array.ofFn (n := n) fun j => column B j.val
    do
      let mut result := #[]
      for i in [:m] do
        let rowA : Array (Model p.storage) := A[i]!
        let mut outputRow := #[]
        for colB in cols do
          match dotSequential p rowA colB with
          | .ok value =>
              outputRow := outputRow.push value
          | .error (.lengthMismatch rowLength columnLength) =>
              throw (.dotLengthMismatch rowLength columnLength)
        result := result.push outputRow
      pure result

/-- Matmul with one format in every site role. -/
@[inline] def matmulUniform (fmt : FloatFormat) (A B : Matrix fmt) :
    Except MatrixShapeError (Matrix fmt) :=
  matmul (SitePolicy.uniform fmt) A B

end Model
end FloatLib.Floats.Formats.BinaryInterchange
