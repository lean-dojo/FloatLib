module

import FloatLib.Floats.Formats.P3109

/-!
P3109 interim report v4.1 §§4.12.1 and 4.13.1: compiled observations for an independent oracle.
This program emits exact values, class names and total-order results. It introduces
no theorem from its output. The Python checker compares them with gfloat.
-/

open FloatLib.Floats FloatLib.Numerics
open Formats.P3109
open ExecFloat.P3109

def exactString (value : NumericalValue Rat) : String :=
  match value with
  | .finite value => s!"{value.num}/{value.den}"
  | .infinity negative => if negative then "-inf" else "inf"
  | .exceptional _ => "nan"

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main : IO Unit := do
  let stdout ← IO.getStdout
  for width in [3:9] do
    for precision in [1:width + 1] do
      for signedness in [Signedness.signed, .unsigned] do
        for domain in [Domain.finite, .extended] do
          if let some format := Format.ofParameters? width precision signedness domain then
            let name := s!"{width},{precision},{reprStr signedness},{reprStr domain}"
            for code in [:format.modulus] do
              let value : ExecFloat.P3109 format := ofNatBits code
              stdout.putStrLn
                s!"value,{name},{code},{reprStr (Class value)},{exactString value.toClosedRat}"
            if width ≤ 5 then
              for left in [:format.modulus] do
                for right in [:format.modulus] do
                  let order := TotalOrder (ofNatBits left : ExecFloat.P3109 format)
                    (ofNatBits right : ExecFloat.P3109 format)
                  stdout.putStrLn s!"order,{name},{left},{right},{order}"
