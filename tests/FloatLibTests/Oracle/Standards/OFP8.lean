module

import FloatLib.Floats.Formats.OCP.FP8.Conversion
import Lean.Data.Json

/-!
OFP8 revision 1.0, §§5.1–5.2.1: complete binary16 and bfloat16 source
encodings, plus externally supplied binary32 boundary words. The JSON is
test input only; it is neither a certificate nor a trusted numerical claim.
-/

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics

def resultWord {format : FloatFormat}
    (outcome : ExecFloat.ConversionOutcome (Model format)) : String :=
  match outcome with
  | .success value _ => toString (Model.toNatBits value)
  | .failure _ => "failure"

def emit (name : String) (source : FloatFormat) (word : Nat) : IO Unit := do
  let stdout ← IO.getStdout
  let value : Model source := Model.ofNatBits word
  let mut fields := [name, toString word]
  for destination in [FloatFormat.e4m3, FloatFormat.e5m2] do
    for overflow in [OverflowMode.saturate, OverflowMode.native] do
      fields := fields ++ [resultWord (Formats.OCP.FP8.convert destination overflow value)]
  stdout.putStrLn (String.intercalate "," fields)

def emitFormat (name : String) (format : FloatFormat) : IO Unit := do
  let stdout ← IO.getStdout
  for word in [:256] do
    let value : Model format := Model.ofNatBits word
    let exact := match Model.toRat? value with
      | some rational => toString rational
      | none => if Model.isNaN value then "nan" else "inf"
    stdout.putStrLn (String.intercalate ","
      ["decode", name, toString word, toString (Model.signBit value), exact])

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main (args : List String) : IO Unit := do
  let path ← match args with
    | [path] => pure path
    | _ => throw (IO.userError "usage: ofp8Standard BINARY32_WORDS.json")
  let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let words ← IO.ofExcept (Lean.fromJson? parsed : Except String (Array Nat))
  emitFormat "e4m3" FloatFormat.e4m3
  emitFormat "e5m2" FloatFormat.e5m2
  for (name, source) in [("binary16", FloatFormat.binary16),
      ("bfloat16", FloatFormat.bfloat16)] do
    for word in [:65536] do
      emit name source word
  for word in words do
    emit "binary32" FloatFormat.binary32 word
