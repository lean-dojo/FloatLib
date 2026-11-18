module

import FloatLib.Floats.Formats.Posit

/-!
Posit Standard (2022), §§6.1, 6.3–6.4: exhaustive small-width conversion
observations for the independent rational decoder and rounding oracle.
-/

open FloatLib.Floats FloatLib.Numerics.Representations

set_option compiler.extract_closed false

def emit (fields : List String) : IO Unit := do
  (← IO.getStdout).putStrLn (String.intercalate "," fields)

def precision (source : Nat) (hs : 2 ≤ source)
    (target : Nat) (ht : 2 ≤ target) : IO Unit := do
  for word in [:2 ^ source] do
    let x : ExecFloat.Posit source hs := ExecFloat.Posit.ofNatBits word
    let y : ExecFloat.Posit target ht := ExecFloat.Posit.pₘToₙ x
    emit ["C", toString source, toString target, toString word,
      toString (ExecFloat.Posit.toNatBits y)]

def integers (bits : Nat) (hp : 2 ≤ bits)
    (width : Nat) (hi : 0 < width) : IO Unit := do
  for word in [:2 ^ width] do
    let signed : ExecFloat.Posit bits hp :=
      ExecFloat.Posit.ofFixedInt (FixedInt.ofNatBits (width := width) word) hi
    let unsigned : ExecFloat.Posit bits hp :=
      ExecFloat.Posit.ofUnsigned (BitVec.ofNat width word) hi
    emit ["F", toString bits, toString width, toString word,
      toString (ExecFloat.Posit.toNatBits signed), toString (ExecFloat.Posit.toNatBits unsigned)]
  for word in [:2 ^ bits] do
    let x : ExecFloat.Posit bits hp := ExecFloat.Posit.ofNatBits word
    emit ["T", toString bits, toString width, toString word,
      toString ((ExecFloat.Posit.toFixedInt width x hi).toNatBits),
      toString ((ExecFloat.Posit.toUnsigned width x hi).toNat)]

def decimal (bits : Nat) (hp : 2 ≤ bits) : IO Unit := do
  for word in [:2 ^ bits] do
    let x : ExecFloat.Posit bits hp := ExecFloat.Posit.ofNatBits word
    let text := ExecFloat.Posit.display x
    let parsed : Except Formats.Posit.Model.ParseError (ExecFloat.Posit bits hp) :=
      ExecFloat.Posit.parse text
    let result := match parsed with
      | .ok y => toString (ExecFloat.Posit.toNatBits y)
      | .error _ => "error"
    emit ["D", toString bits, toString word, text, result]

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main : IO Unit := do
  for source in [2:11] do
    if hs : 2 ≤ source then
      for target in [2:11] do
        if ht : 2 ≤ target then
          precision source hs target ht
  for bits in [2:9] do
    if hp : 2 ≤ bits then
      for width in [1:13] do
        if hi : 0 < width then integers bits hp width hi
      decimal bits hp
