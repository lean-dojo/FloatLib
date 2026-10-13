/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.ExecFloat.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Runtime

/-!
# IEEE results with flags for listed operands

Reads one line of encoded operands per case, evaluates one IEEE operation in one rounding
direction with `ExecFloat.Binary.*WithStatus`, and prints the encoded result and the five
exception flags (inexact 1, underflow 2, overflow 4, divide by zero 8, invalid 16). Unary and
binary operations ignore the operands they do not use.

The formats are the IEEE-style binary layouts `e<w>m<f>` with an exponent field of `w` bits, `f`
fraction bits, and the conventional bias.
-/

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibBenchmarks.Public.OracleList

def statusBits (status : Model.IEEEStatus) : Nat :=
  (if status.inexact then 1 else 0) +
  (if status.underflow then 2 else 0) +
  (if status.overflow then 4 else 0) +
  (if status.divideByZero then 8 else 0) +
  (if status.invalid then 16 else 0)

def parseRounding? : String → Option Model.IEEERoundingMode
  | "near_even" => some .nearestEven
  | "minMag" => some .towardZero
  | "min" => some .towardNegativeInfinity
  | "max" => some .towardPositiveInfinity
  | _ => none

/-- One operation of one format on three encoded operands, as value bits and flags. -/
abbrev Evaluator := Nat → Nat → Nat → Model.IEEERoundingMode → Nat × Nat

/-- The evaluator of the named operation on the configured binary format `T`. -/
macro "evaluator%" T:term "," name:term : term =>
  `(let dec : Nat → $T := ExecFloat.Binary.ofNatBits
    let enc : $T × Model.IEEEStatus → Nat × Nat :=
      fun o => (ExecFloat.Binary.toNatBits o.1, statusBits o.2)
    match ($name : String) with
    | "add" => some fun a b _ m => enc (ExecFloat.Binary.addWithStatus (dec a) (dec b) m)
    | "sub" => some fun a b _ m => enc (ExecFloat.Binary.subWithStatus (dec a) (dec b) m)
    | "mul" => some fun a b _ m => enc (ExecFloat.Binary.mulWithStatus (dec a) (dec b) m)
    | "div" => some fun a b _ m => enc (ExecFloat.Binary.divWithStatus (dec a) (dec b) m)
    | "sqrt" => some fun a _ _ m => enc (ExecFloat.Binary.sqrtWithStatus (dec a) m)
    | "fma" => some fun a b c m =>
        enc (ExecFloat.Binary.fmaWithStatus (dec a) (dec b) (dec c) m)
    | _ => (none : Option Evaluator))

def evaluator? (format name : String) : Option Evaluator :=
  match format with
  | "e5m10" => evaluator% ExecFloat.Binary 5 10, name
  | "e8m7" => evaluator% ExecFloat.Binary 8 7, name
  | "e8m23" => evaluator% ExecFloat.Binary 8 23, name
  | "e8m21" => evaluator% ExecFloat.Binary 8 21, name
  | "e11m52" => evaluator% ExecFloat.Binary 11 52, name
  | "e11m50" => evaluator% ExecFloat.Binary 11 50, name
  | "e4m3" => evaluator% ExecFloat.Binary 4 3, name
  | "e5m2" => evaluator% ExecFloat.Binary 5 2, name
  | _ => none

def run (f : Evaluator) (mode : Model.IEEERoundingMode) (path : System.FilePath) : IO Unit := do
  let text ← IO.FS.readFile path
  let out ← IO.getStdout
  for line in text.splitOn "\n" do
    let ws := (line.splitOn " ").filter (· ≠ "") |>.map String.toNat!
    if ws.isEmpty then continue
    let (v, flags) := f ws[0]! (ws.getD 1 0) (ws.getD 2 0) mode
    out.putStrLn s!"{v} {flags}"

end FloatLibBenchmarks.Public.OracleList

open FloatLibBenchmarks.Public.OracleList in
public def main (args : List String) : IO UInt32 := do
  let usage := "usage: execFloatOracleList FORMAT add|sub|mul|div|sqrt|fma MODE FILE\n" ++
    "FORMAT is e5m10, e8m7, e8m23, e8m21, e11m52, e11m50, e4m3, or e5m2; " ++
    "MODE is near_even, minMag, min, or max"
  match args with
  | [format, name, modeText, path] =>
      match evaluator? format name, parseRounding? modeText with
      | some f, some mode => run f mode path; return 0
      | _, _ => IO.eprintln usage; return 1
  | _ => IO.eprintln usage; return 1
