module

import FloatLib.Floats.Formats.Posit

/-!
Exhaustive public Posit Standard (2022) observations for widths 2 through 8.
The Python checker independently evaluates SoftPosit's es=2 pX2 operations
and the standard's complete signed-word comparisons.

Posit Standard (2022), §§5 and 6, specifies the observed operations.
-/

open FloatLib.Floats

set_option compiler.extract_closed false

/-- Construct the selected operation closures once per descriptor, before enumerating words. -/
@[noinline] def binaryOperations (bits : Nat) (valid : 2 ≤ bits) :
    List (ExecFloat.Posit bits valid → ExecFloat.Posit bits valid →
      ExecFloat.Posit bits valid) :=
  [ExecFloat.Posit.addition, ExecFloat.Posit.subtraction,
    ExecFloat.Posit.multiplication, ExecFloat.Posit.division]

/-- Unary operation closures share the same descriptor setup. -/
@[noinline] def unaryOperations (bits : Nat) (valid : 2 ≤ bits) :
    List (ExecFloat.Posit bits valid → ExecFloat.Posit bits valid) :=
  [ExecFloat.Posit.negate, ExecFloat.Posit.nearestInt, ExecFloat.Posit.sqrt]

/-- Keep the selected FMA capability outside the enumeration loop. -/
@[noinline] def fusedOperations (bits : Nat) (valid : 2 ≤ bits) :
    List (ExecFloat.Posit bits valid → ExecFloat.Posit bits valid →
      ExecFloat.Posit bits valid → ExecFloat.Posit bits valid) :=
  [ExecFloat.fma]

def emitWidth (bits : Nat) (valid : 2 ≤ bits) : IO Unit := do
  let stdout ← IO.getStdout
  let value (word : Nat) : ExecFloat.Posit bits valid := ExecFloat.Posit.ofNatBits word
  let binary := binaryOperations bits valid
  let unary := unaryOperations bits valid
  let fused := fusedOperations bits valid
  let third := value 1
  for a in [:2 ^ bits] do
    let x := value a
    stdout.putStrLn <| String.intercalate ","
      (["U", toString bits, toString a] ++
        unary.map (fun f => toString (ExecFloat.Posit.toNatBits (f x))))
    for b in [:2 ^ bits] do
      let y := value b
      let arithmetic := binary.map (fun f => f x y) ++ fused.map (fun f => f x y third)
      let comparisons := [ExecFloat.Posit.compareEqual x y, ExecFloat.Posit.compareNotEqual x y,
        ExecFloat.Posit.compareGreater x y, ExecFloat.Posit.compareGreaterEqual x y,
        ExecFloat.Posit.compareLess x y, ExecFloat.Posit.compareLessEqual x y]
      stdout.putStrLn <| String.intercalate ","
        (["B", toString bits, toString a, toString b] ++
          arithmetic.map (fun z => toString (ExecFloat.Posit.toNatBits z)) ++
          comparisons.map (fun z => if z then "1" else "0"))

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main : IO Unit := do
  for bits in [2:9] do
    if valid : 2 ≤ bits then
      emitWidth bits valid
