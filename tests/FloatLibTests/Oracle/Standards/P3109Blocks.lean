module

import FloatLib.Floats.Formats.P3109

/-!
Compiled chapter 5 observations for the independent gfloat checker.
All source words at signed widths 3–5 and a separate 3-bit right descriptor
are enumerated. Output contains codes, never imported proof claims.
-/

open FloatLib.Floats FloatLib.Numerics
open Formats.P3109

set_option compiler.extract_closed false

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main : IO Unit := do
  let stdout ← IO.getStdout
  let rightFormat := Format.signed 3 2 .extended
  for width in [3:6] do
    for precision in [1:width] do
      for domain in [Domain.finite, .extended] do
        if let some format := Format.ofParameters? width precision .signed domain then
          let destination := Arithmetic.Destination.p3109 format
          for a in [:format.modulus] do
            let x : ExecFloat.P3109 format := ExecFloat.P3109.ofNatBits a
            for b in [:rightFormat.modulus] do
              let y : ExecFloat.P3109 rightFormat := ExecFloat.P3109.ofNatBits b
              for scale in [0, 1, -2] do
                let left : Block Rat (ExecFloat.P3109 format) 1 := ⟨scale, #v[x]⟩
                let right : Block Rat (ExecFloat.P3109 rightFormat) 1 := ⟨2, #v[y]⟩
                let third : Block Rat Rat 1 := ⟨1, #v[(1 / 2 : Rat)]⟩
                let results :=
                  [ ("Add", (Block.BlockAdd destination {} left right (2 : Rat)).values[0],
                      Arithmetic.Mixed.ScaledAdd destination scale x (2 : Rat) y)
                  , ("Multiply", (Block.BlockMultiply destination {} left right
                      (2 : Rat)).values[0],
                      Arithmetic.Mixed.ScaledMultiply destination scale x (2 : Rat) y)
                  , ("Divide", (Block.BlockDivide destination {} left right (2 : Rat)).values[0],
                      Arithmetic.Mixed.ScaledDivide destination scale x (2 : Rat) y)
                  , ("FMA", (Block.BlockFMA destination {} left right third (2 : Rat)).values[0],
                      Arithmetic.Mixed.ScaledFMA destination scale x (2 : Rat) y
                        (1 : Rat) (1 / 2 : Rat)) ]
                for (op, block, scaled) in results do
                  stdout.putStrLn s!"{width},{precision},{reprStr domain},{a},{b},{scale},{op},\
                      {ExecFloat.P3109.toNatBits block},{ExecFloat.P3109.toNatBits scaled}"
