module

import FloatLib.Floats.Formats.FixedPoint.Embedded.Standard
import Lean.Data.Json

/-! N1169 C-locale text observations; the input corpus is external exact JSON.

WG14 N1169 (2006 TR 18037 draft), §4.2, C clauses 7.18a.6.8 and 7.19.6.2. -/

open FloatLib.Floats.Formats.FixedPoint.Embedded

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main (arguments : List String) : IO Unit := do
  let path ← match arguments.head? with
    | some path => pure path
    | none => throw (IO.userError "expected JSON corpus path")
  let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let inputs ← IO.ofExcept (Lean.fromJson? parsed : Except String (Array String))
  let maximum := (arguments[1]?.bind String.toNat?).getD 6
  let stdout ← IO.getStdout
  for index in [:inputs.size] do
    let text := inputs[index]!
    match Text.scan text with
    | none => stdout.putStrLn s!"A,{index},NA,NA,0"
    | some (endptr, value) =>
      stdout.putStrLn s!"A,{index},{value.num},{value.den},{endptr}"
    for width in [1:maximum + 1] do
      for signed in [false, true] do
        let precision := width - if signed then 1 else 0
        for fractional in [:precision + 1] do
          let format : Format := ⟨signed, precision - fractional, fractional, false⟩
          for mode in [:3] do
            let rounding := if mode == 0 then Rounding.floor else if mode == 1 then
              Rounding.ceil else NearestRounding.even.toRounding
            let result := Text.convert format rounding text
            stdout.putStrLn (String.intercalate "," [
              "R", toString index, toString signed.toNat, toString format.integralBits,
              toString fractional, toString mode, toString (bitsfx result.value),
              toString result.endptr, toString result.rangeError.toNat])
