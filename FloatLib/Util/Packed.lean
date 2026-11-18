/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Util.KernelReduction
public meta import Lean.Compiler.NoncomputableAttr

public import FloatLib.Numerics.Packed.Basic

/-!
# Packed literal construction

Shared readers, common-denominator conversion, lane packing, and declaration construction
for commands that consume exact packed data.
-/

@[expose] public meta section

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
white space or commas, with `#` starting a comment that runs to the end of the line. The pieces
are cut with `String.splitOn`,
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

end FloatLib.Numerics.Packed
