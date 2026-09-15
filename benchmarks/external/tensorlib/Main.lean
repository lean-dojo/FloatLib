import TensorLib.Float
import ConversionProtocol

/-! # Adapter calling TensorLib's unmodified scalar format conversions -/

def main (args : List String) : IO Unit := do
  let rest := args.drop 2
  match args[0]?.getD "", args[1]?.getD "" with
  | "binary16", "encode" =>
    ConversionComparison.run Float32.ofBits (fun x => x.toFloat16Bits.toUInt32) rest
  | "bfloat16", "encode" =>
    ConversionComparison.run Float32.ofBits (fun x => x.toBFloat16Bits.toUInt32) rest
  | "e4m3fn", "encode" =>
    ConversionComparison.run Float32.ofBits (fun x => x.toFloat8E4M3Bits.toUInt32) rest
  | "e5m2", "encode" =>
    ConversionComparison.run Float32.ofBits (fun x => x.toFloat8E5M2Bits.toUInt32) rest
  | "binary16", "decode" =>
    ConversionComparison.run UInt32.toUInt16 (fun x => x.toFloat32FromFloat16.toBits) rest
  | "bfloat16", "decode" =>
    ConversionComparison.run UInt32.toUInt16 (fun x => x.toFloat32FromBFloat16.toBits) rest
  | "e4m3fn", "decode" =>
    ConversionComparison.run UInt32.toUInt8 (fun x => x.toFloat32FromFloat8E4M3.toBits) rest
  | "e5m2", "decode" =>
    ConversionComparison.run UInt32.toUInt8 (fun x => x.toFloat32FromFloat8E5M2.toBits) rest
  | "binary32", "echo" =>
    ConversionComparison.run Float32.ofBits Float32.toBits rest
  | _, _ => throw <| IO.userError "unknown format or direction"
