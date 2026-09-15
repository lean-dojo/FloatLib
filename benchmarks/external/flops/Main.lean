import Flops.P3109.Exec.Runtime
import P3109Protocol

/-! # FLoPS adapter for the matched P3109 arithmetic comparison -/

open p3109_format.Exec

private def select (format : p3109_format) :
    String → Option (Bits format → Bits format → Bits format → Nat)
  | "add" => some fun x y _ => code (add x y .RNE .SatNone)
  | "mul" => some fun x y _ => code (multiply x y .RNE .SatNone)
  | "div" => some fun x y _ => code (divide x y .RNE .SatNone)
  | "fma" => some fun x y z => code (fma x y z .RNE .SatNone)
  | _ => none

def main (args : List String) : IO Unit := do
  let format ← match args[0]?.getD "" with
    | "Binary4p2sf" =>
      pure (⟨4, 2, .signed, .finite, by decide, by decide⟩ : p3109_format)
    | "Binary8p4se" =>
      pure (⟨8, 4, .signed, .extended, by decide, by decide⟩ : p3109_format)
    | "Binary8p3se" =>
      pure (⟨8, 3, .signed, .extended, by decide, by decide⟩ : p3109_format)
    | _ => throw <| IO.userError "unknown format"
  P3109Comparison.run (2 ^ format.K)
    (fun n => (⟨n % 2 ^ format.K, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Bits format))
    (select format) (args.drop 1)
