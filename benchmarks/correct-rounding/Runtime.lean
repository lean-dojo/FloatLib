/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import Lean
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.CorrectlyRounded.Runtime

/-!
# Runtime checks on exact, externally supplied bit patterns

This executable reads JSON, evaluates FloatLib's total correctly rounded model functions, and
compares result bits with an independent reference. It produces finite test evidence, not a
theorem about imported data. NaNs compare by classification; zeros compare by their sign bit.
The configured functions are wrappers around these same model functions.
-/

open Lean FloatLib.Floats.Formats.BinaryInterchange

private structure Case where
  id : String
  width : Nat
  operation : String
  bits : Nat
  expected : Nat
  deriving FromJson

private def evaluate {format : FloatFormat} (operation : String)
    (input : Model format) : Except String (Model format) :=
  match operation with
  | "exp" => .ok (Model.Transcendentals.CorrectlyRounded.exp input)
  | "log" => .ok (Model.Transcendentals.CorrectlyRounded.log input)
  | "expm1" => .ok (Model.Transcendentals.CorrectlyRounded.expm1 input)
  | "log1p" => .ok (Model.Transcendentals.CorrectlyRounded.logp1 input)
  | _ => .error s!"No correctly rounded unary API: {operation}"

private def check (item : Case) : IO Json := do
  let format ← match item.width with
    | 32 => pure FloatFormat.binary32
    | 64 => pure FloatFormat.binary64
    | _ => throw (IO.userError "Only binary32 and binary64 are admitted")
  unless item.bits < 2 ^ item.width && item.expected < 2 ^ item.width do
    throw (IO.userError "Input or reference bit pattern exceeds the format")
  let input := Model.ofNatBits (fmt := format) item.bits
  let expected := Model.ofNatBits (fmt := format) item.expected
  let start ← IO.monoNanosNow
  let actual ← IO.ofExcept (evaluate item.operation input)
  -- An IO reference forces evaluation before the end timestamp.
  let evaluated ← IO.mkRef actual.toNatBits
  let elapsed := (← IO.monoNanosNow) - start
  let bits ← evaluated.get
  let agrees :=
    if Model.isNaN actual && Model.isNaN expected then true
    else bits == item.expected
  return Json.mkObj [
    ("id", toJson item.id), ("status", toJson (if agrees then "matched" else "mismatch")),
    ("actual", toJson bits), ("expected", toJson item.expected),
    ("elapsed_ns", toJson elapsed)]

def main (args : List String) : IO UInt32 := do
  let [inputPath, outputPath] := args
    | throw (IO.userError "Usage: Runtime.lean PLAN.json OUTPUT.jsonl")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile inputPath))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array Case))
  let output ← IO.FS.Handle.mk outputPath .append
  for item in cases do
    if let some activePath ← IO.getEnv "FLOATLIB_SUITE_ACTIVE" then
      IO.FS.writeFile activePath item.id
    let row ← check item
    output.putStrLn row.compress
    output.flush
  return 0
