/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Util.Packed
public meta import Lean.Elab.Command
public import FloatLib.Numerics.Packed.Basic

/-!
# Packed row literals

`packed_row` defines a natural-number constant whose value is the row of the given entries, as a
raw literal:

```lean
packed_row h (width := 64) := [3, -1, 4, -1, 5]
packed_row c (width := 16) (signed := false) := [1, 2, 6, 20, 70]
packed_row g (width := 300) from "g.txt"
```

The first form takes the entries in the source. The second reads them from a text file in the
directory of the source file: plain decimal integers, ASCII digits after an optional `-`, separated
by white space or commas, with `#` starting a comment that runs to the end of the line. Any other
token, such as `1_000` or `+5`, is an error. Either way the command checks that every entry `x`
fits,
`-2 ^ (w - 1) ≤ x < 2 ^ (w - 1)`, and lane `k` of the constant then holds `xs[k] + 2 ^ (w - 1)`.
So `entries 64 5 h = [3, -1, 4, -1, 5]` holds by `decide +kernel`. With `(signed := false)` the
entries are natural numbers below `2 ^ w`, stored as they are, and
`lanes 16 5 c = [1, 2, 6, 20, 70]`.

The constant is data for kernel checks. It is irreducible and has no compiled code, so a
definition that computes with it is `noncomputable`, and a check about it is closed with
`decide +kernel`, which never evaluates it in the elaborator. Importing a module that holds a large
row costs no more than importing an empty one, because an `.olean` file stores the literal's limbs
as they are.

## Main definitions

* `packed_row`: the command, in both forms.
* `parseEntries` and `readEntries`: the integers of a rows file, for `packed_row ... from` and
  for the certificate files of `interval`.
* `commonDen` and `numerators`: rationals as one integer row over their least common denominator.
* `rowLanes`, `packSlice` and `addRow`: the lanes of a row, the number they make, and the step that
  adds it to the environment as an irreducible raw literal.
* `kernelWhnf`, `natValue`, `intValue`, `ratValue` and `listValues`: closed data read by kernel
  reduction, which needs no compiled code, for the commands and tactics that build rows from
  definitions, `packed_values` and the coefficient route of `interval`.

## Implementation notes

Large data entered as a numeral, or as a list of integer numerals, is slow before the kernel ever
sees it: decoding a numeral costs time quadratic in its number of digits, and elaborating a plain
list of `Int` numerals costs time quadratic in its length. `packed_row` reads each entry from its
own digits, in blocks of eighteen joined by halving, packs the lanes by halving as well, and adds
the value to the environment as one raw literal. In our measurements on Lean v4.36.0, a plain list
of 301 integers of 400 bits took about 3 s to elaborate, while `packed_row` took under 0.1 s for 601
such entries in the source and about one second for 4,001 entries of about 1,000 bits read from a
file. Lake does not track the data file, so touch the source file after changing it.

Joining by halving matters more than it looks. Reading `d` digits left to right costs `d`
multiplications of a growing number by ten, which is quadratic, while splitting the string in
halves and joining with one multiplication by `10 ^ (d / 2)` lets GMP's fast multiplication do
the work at every level.

## References

* *The Lean Language Reference*, section *Natural Numbers*, on the kernel's natural-number
  literals and the arbitrary-precision library behind them,
  <https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/>.

## Tags

packed row, literal, kernel reduction
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

/-- One signed integer entry of a `packed_row` literal. -/
syntax packedEntry := "-"? num

/-- The sign option of `packed_row`: `(signed := false)` stores natural entries as they are. -/
syntax packedSigned := " (" &"signed" " := " ident ")"

/-- `packed_row r (width := w) := [x₀, x₁, …]` defines `r : Nat`, the biased row that holds
`xs[k] + 2 ^ (w - 1)` in lane `k` of width `w`, or `xs[k]` with `(signed := false)`. -/
syntax (name := packedRow) (docComment)? "packed_row " ident " (" &"width" " := " num ")"
    (packedSigned)? " := " "[" packedEntry,* "]" : command

/-- `packed_row r (width := w) from "file"` defines `r : Nat` from the entries in a text file next
to the source file, separated by white space or commas, with `#` comments. -/
syntax (name := packedRowFile) (docComment)? "packed_row " ident " (" &"width" " := " num ")"
    (packedSigned)? " from " str : command

end FloatLib.Numerics.Packed

public meta section

namespace FloatLib.Numerics.Packed

open Lean Elab Command Meta

/-- The integer written by one `packedEntry`. -/
def entryOfSyntax : TSyntax ``packedEntry → CommandElabM Int
  | `(packedEntry| - $n:num) => pure (-(n.getNat : Int))
  | `(packedEntry| $n:num) => pure n.getNat
  | _ => throwUnsupportedSyntax

/-- Whether a `packed_row` command asks for signed lanes, which is the default. -/
def signedOfSyntax : Option (TSyntax ``packedSigned) → CommandElabM Bool
  | none => pure true
  | some stx => match stx with
    | `(packedSigned| (signed := $b:ident)) =>
        match b.getId with
        | `true => pure true
        | `false => pure false
        | _ => throwErrorAt b "expected `true` or `false`"
    | _ => throwUnsupportedSyntax

/-- Elaborate both forms of `packed_row`: read the entries, check that each fits its lane, pack the
lanes, and add the result as an irreducible constant without compiled code. -/
@[command_elab packedRow, command_elab packedRowFile]
def elabPackedRow : CommandElab := fun stx => do
  let (doc?, id, w, signed, values) ← match stx with
    | `($[$doc?:docComment]? packed_row $id:ident (width := $w:num) $[$sg?:packedSigned]?
          := [$xs,*]) =>
        pure (doc?, id, w.getNat, ← signedOfSyntax sg?, ← xs.getElems.mapM entryOfSyntax)
    | `($[$doc?:docComment]? packed_row $id:ident (width := $w:num) $[$sg?:packedSigned]?
          from $path:str) => do
        match ← readEntries path.getString with
        | .ok xs => pure (doc?, id, w.getNat, ← signedOfSyntax sg?, xs)
        | .error e => throwErrorAt path "{e}"
    | _ => throwUnsupportedSyntax
  if w = 0 then
    throwErrorAt id "the lane width must be positive"
  let lanes ← match rowLanes w signed values with
    | .ok lanes => pure lanes
    | .error e => throwErrorAt id "{e}"
  let kind := if signed then "signed" else "unsigned"
  addRow ((← getCurrNamespace) ++ id.getId) w lanes (match doc? with
    | some doc => doc.getDocString
    | none => s!"A packed row of {values.size} {kind} entries in lanes of width {w}.") stx id

end FloatLib.Numerics.Packed
