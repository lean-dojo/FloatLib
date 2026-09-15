import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
import FloatLibBenchmarks.Support.ConversionProtocol

/-! # Descriptor cast adapter for the TensorLib scalar conversion comparison -/

open FloatLib.Floats.Formats.BinaryInterchange

def main (args : List String) : IO Unit := do
  let format ← match args[0]?.getD "" with
    | "binary16" => pure FloatFormat.binary16
    | "bfloat16" => pure FloatFormat.bfloat16
    | "e4m3fn" => pure FloatFormat.e4m3fn
    | "e5m2" => pure FloatFormat.e5m2
    | _ => throw <| IO.userError "unknown format"
  let (src, dst) ← match args[1]?.getD "" with
    | "encode" => pure (FloatFormat.binary32, format)
    | "decode" => pure (format, FloatFormat.binary32)
    | _ => throw <| IO.userError "direction must be encode or decode"
  ConversionComparison.run
    (fun word => Model.ofNatBits (fmt := src) word.toNat)
    (fun value => (Model.cast src dst value).toBits.toNat.toUInt32)
    (args.drop 2)
