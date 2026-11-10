/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Basic
public meta import Lean.Compiler.NoncomputableAttr
public meta import Lean.Elab.Command

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
token, such as `1_000` or `+5`, is an error. Either way the command checks that every entry `x` fits,
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
the value to the environment as one raw literal. In our measurements on Lean 4.35, a plain list of
301 integers of 400 bits took 1.9 s to elaborate, while `packed_row` took under 0.1 s for 601 such
entries in the source and about a quarter of a second for 4,001 entries of about 1,000 bits read
from a file. Lake does not track the data file, so touch the source file after changing it.

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

/-- `∑ k < len, lanes[lo + k] * 2 ^ (w * k)`, splitting the lanes in halves. -/
def packSlice (w : Nat) (lanes : Array Nat) (lo len : Nat) : Nat :=
  if _ : len ≤ 1 then
    if len = 0 then 0 else lanes[lo]!
  else
    let half := len / 2
    packSlice w lanes lo half ||| (packSlice w lanes (lo + half) (len - half) <<< (w * half))
termination_by len
decreasing_by all_goals omega

/-- The value of a nonempty string of ASCII decimal digits, read in blocks of at most eighteen
digits that are joined by halving, so that a long entry costs about one multiplication per level.
Any other character, such as a `_` separator, gives `none`. -/
partial def natOfDigits (s : String.Slice) : Option Nat :=
  if s.isEmpty || !s.all Char.isDigit then none else digits s
where
  /-- The halving reader. Every character is an ASCII digit, so bytes count digits and both
  halves are shorter than `s`. -/
  digits (s : String.Slice) : Option Nat :=
    let n := s.utf8ByteSize
    if n ≤ 18 then s.toNat? else
      let low := n / 2
      match digits (s.take (n - low)), digits (s.drop (n - low)) with
      | some a, some b => some (a * 10 ^ low + b)
      | _, _ => none

/-- A decimal integer with an optional leading minus sign. -/
def intOfToken (s : String) : Option Int :=
  if s.startsWith "-" then
    (natOfDigits (s.drop 1)).map fun n => -(n : Int)
  else
    (natOfDigits s.toSlice).map fun n => (n : Int)

/-- The entries of a rows file: decimal integers, ASCII digits after an optional `-`, separated by
white space or commas, with `#` starting a comment that runs to the end of the line. The pieces are cut with `String.splitOn`,
which is much faster here than `String.replace`. -/
def parseEntries (text : String) : Except String (Array Int) := do
  let mut out := #[]
  for line in text.splitOn "\n" do
    let mut pieces := [(line.splitOn "#").headD ""]
    for sep in [" ", ",", "\t", "\r"] do
      pieces := pieces.flatMap (·.splitOn sep)
    for token in pieces do
      if token.isEmpty then continue
      match intOfToken token with
      | some x => out := out.push x
      | none => throw s!"not an integer: {token}"
  return out

/-- Kernel reduction of a closed term to weak head normal form. It needs no compiled code and runs
the kernel's fast paths on natural-number literals, so commands and tactics read the data of a
certificate with it: `packed_values` reads decoded values and `interval` reads coefficients. -/
def kernelWhnf (e : Expr) : MetaM Expr := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok e => pure e
  | .error ex => throwKernelException ex

/-- The value of a closed natural-number term, by kernel reduction. -/
def natValue (e : Expr) : MetaM Nat := do
  match ← kernelWhnf e with
  | .lit (.natVal n) => pure n
  | e => throwError "could not evaluate the natural number {e}"

/-- The value of a closed integer term, by kernel reduction. -/
def intValue (e : Expr) : MetaM Int := do
  let e ← kernelWhnf e
  match e.getAppFnArgs with
  | (``Int.ofNat, #[t]) => return (← natValue t)
  | (``Int.negSucc, #[t]) => return -((← natValue t : Int) + 1)
  | _ => throwError "could not evaluate the integer {e}"

/-- The value of a closed rational term, by kernel reduction. -/
def ratValue (e : Expr) : MetaM Rat := do
  let e ← kernelWhnf e
  match e.getAppFnArgs with
  | (``Rat.mk', #[num, den, _, _]) => return mkRat (← intValue num) (← natValue den)
  | _ => throwError "could not evaluate the rational {e}"

/-- The elements of a closed list term, by kernel reduction of its spine. -/
partial def listValues (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  let e ← kernelWhnf e
  match e.getAppFnArgs with
  | (``List.nil, _) => return acc
  | (``List.cons, #[_, hd, tl]) => listValues tl (acc.push hd)
  | _ => throwError "could not evaluate the list {e}"

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

/-- The entries of the rows file `path`, in the directory of the source file being elaborated,
in the format of `parseEntries`. -/
def readEntries {m : Type → Type} [Monad m] [MonadLog m] [MonadLiftT IO m] (path : String) :
    m (Except String (Array Int)) := do
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  return parseEntries (← IO.FS.readFile (dir / path))

/-- The least common denominator of several rows of rationals. -/
def commonDen (rows : Array (Array Rat)) : Nat :=
  rows.foldl (fun d r => r.foldl (fun d q => Nat.lcm d q.den) d) 1

/-- The numerators of a row of rationals over the denominator `d`, a common multiple of their
denominators: the integers `q * d`. -/
def numerators (d : Nat) (r : Array Rat) : Array Int :=
  r.map fun q => q.num * ((d / q.den : Nat) : Int)

/-- The lanes of a row of width `w`: `x + 2 ^ (w - 1)` for each signed entry `x`, or `x` itself
with `signed := false`, or the message for the first entry that does not fit. -/
def rowLanes (w : Nat) (signed : Bool) (values : Array Int) : Except String (Array Nat) := do
  let offset : Int := if signed then 2 ^ (w - 1) else 0
  let mut lanes := Array.mkEmpty values.size
  for h : i in [0:values.size] do
    let x := values[i]
    unless 0 ≤ x + offset && x + offset < 2 ^ w do
      let kind := if signed then "a signed" else "an unsigned"
      throw s!"entry {i} is {x}, which does not fit {kind} lane of width {w}"
    lanes := lanes.push (x + offset).toNat
  return lanes

/-- Add `declName : Nat` with the lanes as one raw literal, irreducible and without compiled code,
and the docstring `doc`. `packed_row` and the value commands built on it share this step. -/
def addRow (declName : Name) (w : Nat) (lanes : Array Nat) (doc : String) (stx : Syntax)
    (id : Syntax) : CommandElabM Unit := do
  if (← getEnv).contains declName then
    throwErrorAt id "{declName} is already declared"
  let value := packSlice w lanes 0 lanes.size
  liftCoreM <| addDecl (.defnDecl {
    name := declName, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit value
    hints := .opaque, safety := .safe }) (forceExpose := true)
  modifyEnv (addNoncomputable · declName)
  setReducibilityStatus declName .irreducible
  addDocStringCore declName doc
  addDeclarationRangesFromSyntax declName stx id

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
