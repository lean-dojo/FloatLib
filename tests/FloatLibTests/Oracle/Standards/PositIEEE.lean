module

import FloatLib.Floats.Formats.Posit
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Instances
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Codecs
import FloatLib.Numerics.Executable.Conversion.Runtime

/-!
Posit Standard (2022), §6.5: exact generic conversions across all binary16 and
bfloat16 encodings and small IEEE descriptors. Output tests use all six
deterministic rounding modes; away-from-zero is a labelled FloatLib extension.
-/

open FloatLib.Floats FloatLib.Numerics
open Formats.BinaryInterchange

set_option compiler.extract_closed false

abbrev BinaryValue (format : FloatFormat) :=
  ExecFloat (Configured.Family format (Configured.Code (.wide : Configured.StoragePlan format))
    .wide)

local instance (format : FloatFormat) :
    ExecFloat.ModelCodec (.wide : Configured.StoragePlan format) (Model format)
      (Configured.Code (.wide : Configured.StoragePlan format)) :=
  Configured.canonicalCodec format .wide

def emit (fields : List String) : IO Unit := do
  (← IO.getStdout).putStrLn (String.intercalate "," fields)

def fromBinary (source : FloatFormat) (bits : Nat) (hp : 2 ≤ bits) : IO Unit := do
  for word in [:2 ^ source.bitWidth] do
    let x : BinaryValue source :=
      ExecFloat.Binary.ofNatBits (format := source) (plan := .wide) word
    let result := x.cast (target := ExecFloat.Posit bits hp)
    let output := match result with
      | .success y _ => toString (ExecFloat.Posit.toNatBits y)
      | .failure _ => "failure"
    emit ["F", toString source.expWidth, toString source.fracWidth,
      toString bits, toString word, output]

def toBinary (target : FloatFormat) (bits : Nat) (hp : 2 ≤ bits) : IO Unit := do
  for word in [:2 ^ bits] do
    let x : ExecFloat.Posit bits hp := ExecFloat.Posit.ofNatBits word
    for (name, mode) in [("nearest", RoundingMode.nearest), ("nearestAway", .nearestAway),
        ("towardZero", .towardZero), ("up", .up), ("down", .down), ("away", .away)] do
      let result := x.cast (target := BinaryValue target) (mode := mode)
      let output := match result with
        | .success y _ =>
            toString (ExecFloat.Binary.toNatBits (format := target) (plan := .wide) y)
        | .failure _ => "failure"
      emit ["T", toString target.expWidth, toString target.fracWidth,
        toString bits, toString word, name, output]

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main : IO Unit := do
  let mut formats := []
  for exponent in [2:5] do
    if he : 2 ≤ exponent then
      for fraction in [1:5] do
        if hf : 0 < fraction then
          formats := formats ++ [FloatFormat.ieee exponent fraction he hf]
  for source in formats ++ [FloatFormat.binary16, FloatFormat.bfloat16] do
    for bits in [2:9] do
      if hp : 2 ≤ bits then fromBinary source bits hp
  for target in formats ++ [FloatFormat.binary16, FloatFormat.bfloat16,
      FloatFormat.binary32, FloatFormat.binary64, FloatFormat.binary128,
      FloatFormat.binary256] do
    for bits in [2:9] do
      if hp : 2 ≤ bits then toBinary target bits hp
