module

import FloatLib.Floats.Formats.FixedPoint.Embedded.Standard
import Lean.Data.Json

/-! N1169 complete constants and translation choices, driven by exact JSON.

WG14 N1169 (2006 TR 18037 draft), §4.1.5. -/

open FloatLib.Floats.Formats.FixedPoint.Embedded

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main (arguments : List String) : IO Unit := do
  let path ← match arguments.head? with
    | some path => pure path
    | none => throw (IO.userError "expected JSON corpus path")
  let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let inputs ← IO.ofExcept (Lean.fromJson? parsed : Except String (Array String))
  let stdout ← IO.getStdout
  for index in [:inputs.size] do
    match Constant.parse inputs[index]! with
    | none => stdout.putStrLn s!"A,{index},NA"
    | some literal =>
      stdout.putStrLn (String.intercalate "," ["A", toString index,
        toString literal.type.signed.toNat, toString (if literal.type.kind = .fract then 0 else 1),
        toString literal.type.length.ordinal, toString literal.value.num,
        toString literal.value.den, toString literal.hexadecimal.toNat])
      for fractional in [:6] do
        for integral in [:3] do
          let layout : Layout := ⟨fun _ _ _ ↦ fractional, fun _ _ ↦ integral⟩
          for mode in [:3] do
            let policy := if mode == 0 then Constant.Policy.even else if mode == 1 then
              Constant.Policy.neighbor .floor .even false else
              Constant.Policy.neighbor .ceil .even true
            let result := (Constant.translate layout policy literal).map bitsfx
            stdout.putStrLn (String.intercalate "," [
              "R", toString index, toString fractional, toString integral, toString mode,
              result.map toString |>.getD "NA"])
