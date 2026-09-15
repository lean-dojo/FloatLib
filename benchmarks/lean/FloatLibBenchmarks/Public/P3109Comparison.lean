import FloatLib.Floats.Formats.P3109.Arithmetic.Runtime
import FloatLibBenchmarks.Support.P3109Protocol

/-! # FloatLib adapter for the matched P3109 arithmetic comparison -/

open FloatLib.Floats
open FloatLib.Floats.Formats.P3109

private def select (format : Format) :
    String → Option (ExecFloat.P3109 format → ExecFloat.P3109 format →
      ExecFloat.P3109 format → Nat)
  | "add" => some fun x y _ => (ExecFloat.P3109.add x y).toNatBits
  | "mul" => some fun x y _ => (ExecFloat.P3109.mul x y).toNatBits
  | "div" => some fun x y _ => (ExecFloat.P3109.div x y).toNatBits
  | "fma" => some fun x y z => (ExecFloat.P3109.fma x y z).toNatBits
  | _ => none

public def main (args : List String) : IO Unit := do
  let format ← match args[0]?.getD "" with
    | "Binary4p2sf" => pure (Format.signed 4 2 .finite)
    | "Binary8p4se" => pure (Format.signed 8 4 .extended)
    | "Binary8p3se" => pure (Format.signed 8 3 .extended)
    | _ => throw <| IO.userError "unknown format"
  P3109Comparison.run format.modulus
    (ExecFloat.P3109.ofNatBits (format := format)) (select format) (args.drop 1)
