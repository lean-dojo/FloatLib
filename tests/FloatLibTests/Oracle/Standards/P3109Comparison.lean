module

import FloatLib.Floats.Formats.P3109.Projection.Comparison.Runtime
import FloatLib.Floats.Formats.P3109.Projection.Rational.Runtime

/-!
P3109 interim report v4.1 §§4.7–4.8: exact rational boundary observations. Every policy is
checked against the existing rational rounder, then emitted for an independent
Fraction checker. Random-word widths zero through three are exhaustive.
-/

open FloatLib.Numerics FloatLib.Floats.Formats.P3109

def modes : Array RoundingMode := Id.run do
  let mut result := #[.towardZero, .up, .down, .nearestAway, .nearest, .toOdd]
  for width in [:4] do
    for word in [:2 ^ width] do
      let random := RandomBits.ofNat width word
      result := result ++ #[.stochasticA random, .stochasticB random, .stochasticC random]
  return result

def observe (stdout : IO.FS.Stream) (format : Format) (target : Rat) : IO Unit := do
  let mut row := s!"R,{target.num},{target.den}"
  for mode in modes do
    for saturation in [SaturationMode.finite, .propagate, .none] do
      let policy : ProjectionPolicy := { rounding := mode, saturation }
      let actual := (ComparisonRounding.code format policy (cmp target)).toNat
      let old := (format.projectRatCode policy (.finite target)).toNat
      if actual != old then
        throw (IO.userError s!"comparison/rational mismatch: {reprStr format}, {target}, \
            {reprStr policy}, {actual}, {old}")
      row := row ++ s!",{actual}"
  stdout.putStrLn row

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main : IO Unit := do
  let stdout ← IO.getStdout
  for width in [3:7] do
    for precision in [1:width + 1] do
      for signedness in [Signedness.signed, .unsigned] do
        for domain in [Domain.finite, .extended] do
          if let some format := Format.ofParameters? width precision signedness domain then
            stdout.putStrLn s!"F,{width},{precision},{signedness == .signed},{domain == .extended}"
            for code in [:format.maxFiniteBits + 2] do
              let lower := (format.decodePositiveFinite code).toRat
              let unit : Rat := 2 ^ format.decodeQuantum code
              for part in [:18] do
                let target := lower + (part : Rat) / 16 * unit
                observe stdout format target
                observe stdout format (-target)
            for multiple in [4, 17, 1024] do
              let target := (multiple : Rat) * format.maxFinite.toRat
              observe stdout format target
              observe stdout format (-target)
