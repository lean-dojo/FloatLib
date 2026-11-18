module

import FloatLib.Floats.Formats.FixedPoint.Embedded.Standard
import Lean.Data.Json

/-! N1169 formatted conversions driven by exact JSON; no C stream is opened.

WG14 N1169 (2006 TR 18037 draft), §4.2, C clauses 7.18a.6.8 and 7.19.6.2. -/

open FloatLib.Floats.Formats.FixedPoint.Embedded

structure Corpus where
  items : Array String
  texts : Array String
  precisions : Array (Option Int)
  fieldWidths : Array Int
  scanWidths : Array Nat
  flagMasks : Array Nat
  maximumWidth : Nat
  deriving Lean.FromJson

def rounder (mode : Nat) : Rounding :=
  if mode == 0 then .floor else if mode == 1 then .ceil else NearestRounding.even.toRounding

def statusNumber : Formatted.ScanStatus → Nat
  | .success => 0
  | .matchingFailure => 1
  | .inputFailure => 2
  | .undefined => 3

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main (arguments : List String) : IO Unit := do
  let path ← match arguments.head? with
    | some path => pure path
    | none => throw (IO.userError "expected JSON corpus path")
  let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let corpus ← IO.ofExcept (Lean.fromJson? parsed : Except String Corpus)
  let stdout ← IO.getStdout
  for index in [:corpus.items.size] do
    let result := (Formatted.item corpus.items[index]!.toList).isSome
    stdout.putStrLn s!"A,{index},{result.toNat}"
  for width in [1:corpus.maximumWidth + 1] do
    for signed in [false, true] do
      let precision := width - if signed then 1 else 0
      for fractional in [:precision + 1] do
        let format : Format := ⟨signed, precision - fractional, fractional, false⟩
        for word in [:2 ^ width] do
          let value := format.ofBits ⟨word % 2 ^ format.width, Nat.mod_lt _ (by positivity)⟩
          for mode in [:3] do
            for p in [:corpus.precisions.size] do
              for w in [:corpus.fieldWidths.size] do
                for mask in corpus.flagMasks do
                  let options : Formatted.PrintOptions :=
                    ⟨corpus.fieldWidths[w]!, corpus.precisions[p]!, mask.testBit 0,
                      mask.testBit 1, mask.testBit 2, mask.testBit 3, mask.testBit 4⟩
                  let text := Formatted.formatValue (rounder mode) options value
                  stdout.putStrLn (String.intercalate "," [
                    "P", toString width, toString signed.toNat, toString fractional,
                    toString word, toString mode, toString p, toString w, toString mask, text])
  for index in [:corpus.texts.size] do
    for limit in corpus.scanWidths do
      let fieldWidth : Option ℕ+ := if h : 0 < limit then some ⟨limit, h⟩ else none
      for width in [1:corpus.maximumWidth + 1] do
        for signed in [false, true] do
          let precision := width - if signed then 1 else 0
          for fractional in [:precision + 1] do
            let format : Format := ⟨signed, precision - fractional, fractional, false⟩
            for mode in [:3] do
              let result := Formatted.scan format (rounder mode) fieldWidth corpus.texts[index]!
              stdout.putStrLn (String.intercalate "," [
                "S", toString index, toString limit, toString width, toString signed.toNat,
                toString fractional, toString mode, toString result.consumed,
                toString (statusNumber result.status), result.value.map (toString ∘ bitsfx)
                  |>.getD "NA"])
