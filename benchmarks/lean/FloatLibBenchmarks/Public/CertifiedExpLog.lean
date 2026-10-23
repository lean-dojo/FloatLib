/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals

/-!
# Certified binary exponential and logarithm on encoded inputs

Reads one encoded binary16, bfloat16, binary32, or binary64 word per line, calls
`ExecFloat.Binary.exp` or `log` with `certify := true`, or `expMinus1` or `logPlus1`, with the
default budget, and prints the encoded result (or `none` for a failure) and then the elapsed
nanoseconds. The `range` mode evaluates a block of consecutive binary32 encodings and writes the
results as binary words.
-/

open FloatLib.Floats

namespace FloatLibBenchmarks.Public.CertifiedExpLog

/-- The four certified functions of one binary format, with their encodings. -/
structure Functions (T : Type) where
  exp : T → Option T
  log : T → Option T
  expMinus1 : T → Option T
  logPlus1 : T → Option T
  ofBits : Nat → T
  toBits : T → Nat

/-- Fill `Functions` from the configured binary instance of one format. -/
macro "functions%" : term =>
  `({ exp := fun x => (ExecFloat.Binary.exp x (certify := true)).toOption,
      log := fun x => (ExecFloat.Binary.log x (certify := true)).toOption,
      expMinus1 := fun x => (ExecFloat.Binary.expMinus1 x).toOption,
      logPlus1 := fun x => (ExecFloat.Binary.logPlus1 x).toOption,
      ofBits := ExecFloat.Binary.ofNatBits, toBits := ExecFloat.Binary.toNatBits })

def single : Functions Binary32 := functions%
def double : Functions Binary64 := functions%
def half : Functions Binary16 := functions%
def brain : Functions BFloat16 := functions%

/-- The function named `exp`, `log`, `expm1`, or `log1p`. -/
def Functions.pick {T : Type} (F : Functions T) : String → Option (T → Option T)
  | "exp" => some F.exp
  | "log" => some F.log
  | "expm1" => some F.expMinus1
  | "log1p" => some F.logPlus1
  | _ => none

def readWords (path : System.FilePath) : IO (Array Nat) := do
  let text ← IO.FS.readFile path
  return ((text.splitOn "\n").filter (· ≠ "")).toArray.map String.toNat!

/-- Evaluate one function on every word of the input file and print results, then the time. -/
def run {T : Type} (F : Functions T) (f : T → Option T) (words : Array Nat) : IO Unit := do
  let xs : Array T := words.map F.ofBits
  let t0 ← IO.monoNanosNow
  let outs := xs.map fun x => match f x with
    | some v => toString (F.toBits v)
    | none => "none"
  let outs ← IO.lazyPure fun _ => outs
  let t1 ← IO.monoNanosNow
  for o in outs do IO.println o
  IO.println s!"nanos,{t1 - t0}"

/-- Evaluate `count` consecutive binary32 encodings from `start` and write little-endian results,
with `0xFFFFFFFF` (a NaN encoding, never a certified result) for `none`. -/
def rangeS (f : Binary32 → Option Binary32) (start count : Nat) (out : System.FilePath) :
    IO Unit := do
  let mut buf := ByteArray.emptyWithCapacity (4 * count)
  for i in [0:count] do
    let v : UInt32 := match f (ExecFloat.Binary.ofNatBits (start + i)) with
      | some y => (ExecFloat.Binary.toNatBits y).toUInt32
      | none => 0xFFFFFFFF
    buf := ((buf.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8 |>.push (v >>> 24).toUInt8
  IO.FS.writeBinFile out buf

end FloatLibBenchmarks.Public.CertifiedExpLog

open FloatLibBenchmarks.Public.CertifiedExpLog in
public def main (args : List String) : IO UInt32 := do
  let usage := "usage: execFloatCertifiedExpLog exp|log|expm1|log1p 16|bf16|32|64 WORDS\n" ++
    "       execFloatCertifiedExpLog range exp|log|expm1|log1p START COUNT OUT"
  match args with
  | ["range", fn, start, count, out] =>
      match single.pick fn with
      | some f => rangeS f start.toNat! count.toNat! out; return 0
      | none => IO.eprintln usage; return 1
  | [fn, width, path] =>
      let words ← readWords path
      let ran ← match width with
        | "16" => (half.pick fn).mapM (run half · words)
        | "bf16" => (brain.pick fn).mapM (run brain · words)
        | "32" => (single.pick fn).mapM (run single · words)
        | "64" => (double.pick fn).mapM (run double · words)
        | _ => pure none
      if ran.isSome then return 0 else IO.eprintln usage; return 1
  | _ =>
      IO.eprintln usage
      return 1
