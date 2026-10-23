/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.Sweep
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
import FloatLibBenchmarks.Support.Posit

/-!
# Public arithmetic timing on listed operands

Reads one line of space-separated decimal encodings per case and times an ordinary public
operation (`ExecFloat.add`, `sub`, `mul`, `div`, `sqrt`, `fma`) of a configured binary or posit
format. The format spelling selects the carrier, with `limbs-` selecting `ExecFloat.BinaryLimbs`
storage, and the operation runs its planner-selected certified kernel. Binary operations round to
nearest-even, and posit operations use the prescribed posit rounding rule. Every loop is
monomorphic in its format and operation. Each trial evaluates every case once. The program prints
the time per call of every trial and an XOR of the low 64 encoded result bits (the low 32 bits for
`BinaryLimbs`), which keeps the work live. Other programs time C libraries on the same operand
file.
-/

open FloatLib.Floats
open FloatLibBenchmarks.Public.Sweep (resultBits)

namespace FloatLibBenchmarks.Public.TimeList

/-- Read up to three decimal operand encodings per line, rejecting malformed cases. -/
def readCases (path : System.FilePath) : IO (Array (Nat × Nat × Nat)) := do
  let text ← IO.FS.readFile path
  let mut out := #[]
  for line in text.splitOn "\n" do
    let fields := (line.splitOn " ").filter (· ≠ "")
    if fields.isEmpty then continue
    if fields.length > 3 then
      throw <| IO.userError "each case must have at most three operand encodings"
    let ws ← fields.mapM fun field =>
      match field.toNat? with
      | some value => pure value
      | none => throw <| IO.userError s!"invalid decimal operand encoding: {field}"
    out := out.push (ws[0]!, ws.getD 1 0, ws.getD 2 0)
  return out

syntax "time_workload " ident " : " term " using " term : command

/-- A monomorphic loop over all cases: `xs`, `ys`, `zs` have equal sizes. -/
macro_rules
  | `(time_workload $name:ident : $type:term using $operation:term) =>
      `(@[noinline] def $name (xs ys zs : Array $type) : Nat → UInt64 → UInt64
          | 0, acc => acc
          | n + 1, acc =>
            let result : $type := $operation xs[n]! ys[n]! zs[n]!
            $name xs ys zs n (acc ^^^ resultBits result))

syntax "time_posit_workload " ident " : " term " using " term : command
syntax "time_limbs_workload " ident " : " term " using " term : command

macro_rules
  | `(time_posit_workload $name:ident : $type:term using $operation:term) =>
      `(@[noinline] def $name (xs ys zs : Array $type) : Nat → UInt64 → UInt64
          | 0, acc => acc
          | n + 1, acc =>
            let result : $type := $operation xs[n]! ys[n]! zs[n]!
            $name xs ys zs n (acc ^^^ FloatLibBenchmarks.Support.Posit.resultBits result))

macro_rules
  | `(time_limbs_workload $name:ident : $type:term using $operation:term) =>
      `(@[noinline] def $name (xs ys zs : Array $type) : Nat → UInt64 → UInt64
          | 0, acc => acc
          | n + 1, acc =>
            let result : $type := $operation xs[n]! ys[n]! zs[n]!
            $name xs ys zs n (acc ^^^ (result.raw.1.limb 0).toUInt64))

time_workload addHalf : Binary16 using (fun x y _ => ExecFloat.add x y)
time_workload subHalf : Binary16 using (fun x y _ => ExecFloat.sub x y)
time_workload mulHalf : Binary16 using (fun x y _ => ExecFloat.mul x y)
time_workload divHalf : Binary16 using (fun x y _ => ExecFloat.div x y)
time_workload sqrtHalf : Binary16 using (fun x _ _ => ExecFloat.sqrt x)
time_workload fmaHalf : Binary16 using (fun x y z => ExecFloat.fma x y z)
time_workload addBrain : BFloat16 using (fun x y _ => ExecFloat.add x y)
time_workload subBrain : BFloat16 using (fun x y _ => ExecFloat.sub x y)
time_workload mulBrain : BFloat16 using (fun x y _ => ExecFloat.mul x y)
time_workload divBrain : BFloat16 using (fun x y _ => ExecFloat.div x y)
time_workload sqrtBrain : BFloat16 using (fun x _ _ => ExecFloat.sqrt x)
time_workload fmaBrain : BFloat16 using (fun x y z => ExecFloat.fma x y z)
time_workload addSingle : Binary32 using (fun x y _ => ExecFloat.add x y)
time_workload subSingle : Binary32 using (fun x y _ => ExecFloat.sub x y)
time_workload mulSingle : Binary32 using (fun x y _ => ExecFloat.mul x y)
time_workload divSingle : Binary32 using (fun x y _ => ExecFloat.div x y)
time_workload sqrtSingle : Binary32 using (fun x _ _ => ExecFloat.sqrt x)
time_workload fmaSingle : Binary32 using (fun x y z => ExecFloat.fma x y z)
time_workload addDouble : Binary64 using (fun x y _ => ExecFloat.add x y)
time_workload subDouble : Binary64 using (fun x y _ => ExecFloat.sub x y)
time_workload mulDouble : Binary64 using (fun x y _ => ExecFloat.mul x y)
time_workload divDouble : Binary64 using (fun x y _ => ExecFloat.div x y)
time_workload sqrtDouble : Binary64 using (fun x _ _ => ExecFloat.sqrt x)
time_workload fmaDouble : Binary64 using (fun x y z => ExecFloat.fma x y z)

time_posit_workload addP16 : Posit16 using (fun x y _ => ExecFloat.add x y)
time_posit_workload subP16 : Posit16 using (fun x y _ => ExecFloat.sub x y)
time_posit_workload mulP16 : Posit16 using (fun x y _ => ExecFloat.mul x y)
time_posit_workload divP16 : Posit16 using (fun x y _ => ExecFloat.div x y)
time_posit_workload sqrtP16 : Posit16 using (fun x _ _ => ExecFloat.sqrt x)
time_posit_workload fmaP16 : Posit16 using (fun x y z => ExecFloat.fma x y z)
time_posit_workload addP32 : Posit32 using (fun x y _ => ExecFloat.add x y)
time_posit_workload subP32 : Posit32 using (fun x y _ => ExecFloat.sub x y)
time_posit_workload mulP32 : Posit32 using (fun x y _ => ExecFloat.mul x y)
time_posit_workload divP32 : Posit32 using (fun x y _ => ExecFloat.div x y)
time_posit_workload sqrtP32 : Posit32 using (fun x _ _ => ExecFloat.sqrt x)
time_posit_workload fmaP32 : Posit32 using (fun x y z => ExecFloat.fma x y z)
time_posit_workload addP64 : Posit64 using (fun x y _ => ExecFloat.add x y)
time_posit_workload subP64 : Posit64 using (fun x y _ => ExecFloat.sub x y)
time_posit_workload mulP64 : Posit64 using (fun x y _ => ExecFloat.mul x y)
time_posit_workload divP64 : Posit64 using (fun x y _ => ExecFloat.div x y)
time_posit_workload sqrtP64 : Posit64 using (fun x _ _ => ExecFloat.sqrt x)
time_posit_workload fmaP64 : Posit64 using (fun x y z => ExecFloat.fma x y z)

abbrev Wide1024 := ExecFloat.Binary 19 1023
abbrev Wide4096 := ExecFloat.Binary 19 4095
abbrev Limbs237 := ExecFloat.BinaryLimbs 19 236
abbrev Limbs1024 := ExecFloat.BinaryLimbs 19 1023
abbrev Limbs4096 := ExecFloat.BinaryLimbs 19 4095
time_workload addQuad : Binary128 using (fun x y _ => ExecFloat.add x y)
time_workload subQuad : Binary128 using (fun x y _ => ExecFloat.sub x y)
time_workload mulQuad : Binary128 using (fun x y _ => ExecFloat.mul x y)
time_workload divQuad : Binary128 using (fun x y _ => ExecFloat.div x y)
time_workload sqrtQuad : Binary128 using (fun x _ _ => ExecFloat.sqrt x)
time_workload fmaQuad : Binary128 using (fun x y z => ExecFloat.fma x y z)
time_workload addWide237 : Binary256 using (fun x y _ => ExecFloat.add x y)
time_workload subWide237 : Binary256 using (fun x y _ => ExecFloat.sub x y)
time_workload mulWide237 : Binary256 using (fun x y _ => ExecFloat.mul x y)
time_workload divWide237 : Binary256 using (fun x y _ => ExecFloat.div x y)
time_workload sqrtWide237 : Binary256 using (fun x _ _ => ExecFloat.sqrt x)
time_workload fmaWide237 : Binary256 using (fun x y z => ExecFloat.fma x y z)
time_workload addWide1024 : Wide1024 using (fun x y _ => ExecFloat.add x y)
time_workload subWide1024 : Wide1024 using (fun x y _ => ExecFloat.sub x y)
time_workload mulWide1024 : Wide1024 using (fun x y _ => ExecFloat.mul x y)
time_workload divWide1024 : Wide1024 using (fun x y _ => ExecFloat.div x y)
time_workload sqrtWide1024 : Wide1024 using (fun x _ _ => ExecFloat.sqrt x)
time_workload fmaWide1024 : Wide1024 using (fun x y z => ExecFloat.fma x y z)
time_workload addWide4096 : Wide4096 using (fun x y _ => ExecFloat.add x y)
time_workload subWide4096 : Wide4096 using (fun x y _ => ExecFloat.sub x y)
time_workload mulWide4096 : Wide4096 using (fun x y _ => ExecFloat.mul x y)
time_workload divWide4096 : Wide4096 using (fun x y _ => ExecFloat.div x y)
time_workload sqrtWide4096 : Wide4096 using (fun x _ _ => ExecFloat.sqrt x)
time_workload fmaWide4096 : Wide4096 using (fun x y z => ExecFloat.fma x y z)
instance : Inhabited Limbs237 := ⟨ExecFloat.Binary.ofNatBits 0⟩
time_limbs_workload addLimbs237 : Limbs237 using (fun x y _ => ExecFloat.add x y)
time_limbs_workload subLimbs237 : Limbs237 using (fun x y _ => ExecFloat.sub x y)
time_limbs_workload mulLimbs237 : Limbs237 using (fun x y _ => ExecFloat.mul x y)
time_limbs_workload divLimbs237 : Limbs237 using (fun x y _ => ExecFloat.div x y)
time_limbs_workload sqrtLimbs237 : Limbs237 using (fun x _ _ => ExecFloat.sqrt x)
time_limbs_workload fmaLimbs237 : Limbs237 using (fun x y z => ExecFloat.fma x y z)
instance : Inhabited Limbs1024 := ⟨ExecFloat.Binary.ofNatBits 0⟩
time_limbs_workload addLimbs1024 : Limbs1024 using (fun x y _ => ExecFloat.add x y)
time_limbs_workload subLimbs1024 : Limbs1024 using (fun x y _ => ExecFloat.sub x y)
time_limbs_workload mulLimbs1024 : Limbs1024 using (fun x y _ => ExecFloat.mul x y)
time_limbs_workload divLimbs1024 : Limbs1024 using (fun x y _ => ExecFloat.div x y)
time_limbs_workload sqrtLimbs1024 : Limbs1024 using (fun x _ _ => ExecFloat.sqrt x)
time_limbs_workload fmaLimbs1024 : Limbs1024 using (fun x y z => ExecFloat.fma x y z)
instance : Inhabited Limbs4096 := ⟨ExecFloat.Binary.ofNatBits 0⟩
time_limbs_workload addLimbs4096 : Limbs4096 using (fun x y _ => ExecFloat.add x y)
time_limbs_workload subLimbs4096 : Limbs4096 using (fun x y _ => ExecFloat.sub x y)
time_limbs_workload mulLimbs4096 : Limbs4096 using (fun x y _ => ExecFloat.mul x y)
time_limbs_workload divLimbs4096 : Limbs4096 using (fun x y _ => ExecFloat.div x y)
time_limbs_workload sqrtLimbs4096 : Limbs4096 using (fun x _ _ => ExecFloat.sqrt x)
time_limbs_workload fmaLimbs4096 : Limbs4096 using (fun x y z => ExecFloat.fma x y z)

/-- Decode the cases into one format, run `trials` timed passes of `loop`, and report. -/
def timeWith {T : Type} [Inhabited T] (ofBits : Nat → T)
    (loop : Array T → Array T → Array T → Nat → UInt64 → UInt64)
    (cases : Array (Nat × Nat × Nat)) (trials : Nat) : IO Unit := do
  let xs := cases.map fun (a, _, _) => ofBits a
  let ys := cases.map fun (_, b, _) => ofBits b
  let zs := cases.map fun (_, _, c) => ofBits c
  let mut check : UInt64 := 0
  for t in [0:trials] do
    let t0 ← IO.monoNanosNow
    let result ← IO.lazyPure fun _ => loop xs ys zs xs.size t.toUInt64
    let t1 ← IO.monoNanosNow
    check := check ^^^ result
    IO.println s!"ns_per_call,{(t1 - t0).toFloat / xs.size.toFloat}"
  IO.println s!"check,{check}"

def pick? (format name : String) : Option ((Array (Nat × Nat × Nat)) → Nat → IO Unit) :=
  match format, name with
  | "e5m10", "add" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary16) addHalf)
  | "e5m10", "sub" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary16) subHalf)
  | "e5m10", "mul" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary16) mulHalf)
  | "e5m10", "div" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary16) divHalf)
  | "e5m10", "sqrt" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary16) sqrtHalf)
  | "e5m10", "fma" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary16) fmaHalf)
  | "e8m7", "add" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → BFloat16) addBrain)
  | "e8m7", "sub" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → BFloat16) subBrain)
  | "e8m7", "mul" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → BFloat16) mulBrain)
  | "e8m7", "div" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → BFloat16) divBrain)
  | "e8m7", "sqrt" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → BFloat16) sqrtBrain)
  | "e8m7", "fma" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → BFloat16) fmaBrain)
  | "e8m23", "add" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary32) addSingle)
  | "e8m23", "sub" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary32) subSingle)
  | "e8m23", "mul" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary32) mulSingle)
  | "e8m23", "div" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary32) divSingle)
  | "e8m23", "sqrt" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary32) sqrtSingle)
  | "e8m23", "fma" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary32) fmaSingle)
  | "e11m52", "add" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary64) addDouble)
  | "e11m52", "sub" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary64) subDouble)
  | "e11m52", "mul" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary64) mulDouble)
  | "e11m52", "div" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary64) divDouble)
  | "e11m52", "sqrt" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary64) sqrtDouble)
  | "e11m52", "fma" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary64) fmaDouble)
  | "posit16", "add" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit16) addP16)
  | "posit16", "sub" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit16) subP16)
  | "posit16", "mul" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit16) mulP16)
  | "posit16", "div" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit16) divP16)
  | "posit16", "sqrt" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit16) sqrtP16)
  | "posit16", "fma" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit16) fmaP16)
  | "posit32", "add" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit32) addP32)
  | "posit32", "sub" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit32) subP32)
  | "posit32", "mul" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit32) mulP32)
  | "posit32", "div" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit32) divP32)
  | "posit32", "sqrt" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit32) sqrtP32)
  | "posit32", "fma" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit32) fmaP32)
  | "posit64", "add" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit64) addP64)
  | "posit64", "sub" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit64) subP64)
  | "posit64", "mul" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit64) mulP64)
  | "posit64", "div" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit64) divP64)
  | "posit64", "sqrt" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit64) sqrtP64)
  | "posit64", "fma" => some (timeWith (ExecFloat.Posit.ofNatBits : Nat → Posit64) fmaP64)
  | "e15m112", "add" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary128) addQuad)
  | "e15m112", "sub" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary128) subQuad)
  | "e15m112", "mul" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary128) mulQuad)
  | "e15m112", "div" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary128) divQuad)
  | "e15m112", "sqrt" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary128) sqrtQuad)
  | "e15m112", "fma" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary128) fmaQuad)
  | "e19m236", "add" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary256) addWide237)
  | "e19m236", "sub" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary256) subWide237)
  | "e19m236", "mul" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary256) mulWide237)
  | "e19m236", "div" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary256) divWide237)
  | "e19m236", "sqrt" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary256) sqrtWide237)
  | "e19m236", "fma" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Binary256) fmaWide237)
  | "e19m1023", "add" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Wide1024) addWide1024)
  | "e19m1023", "sub" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Wide1024) subWide1024)
  | "e19m1023", "mul" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Wide1024) mulWide1024)
  | "e19m1023", "div" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Wide1024) divWide1024)
  | "e19m1023", "sqrt" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Wide1024) sqrtWide1024)
  | "e19m1023", "fma" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Wide1024) fmaWide1024)
  | "e19m4095", "add" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Wide4096) addWide4096)
  | "e19m4095", "sub" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Wide4096) subWide4096)
  | "e19m4095", "mul" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Wide4096) mulWide4096)
  | "e19m4095", "div" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Wide4096) divWide4096)
  | "e19m4095", "sqrt" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Wide4096) sqrtWide4096)
  | "e19m4095", "fma" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Wide4096) fmaWide4096)
  | "limbs-e19m236", "add" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs237) addLimbs237)
  | "limbs-e19m236", "sub" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs237) subLimbs237)
  | "limbs-e19m236", "mul" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs237) mulLimbs237)
  | "limbs-e19m236", "div" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs237) divLimbs237)
  | "limbs-e19m236", "sqrt" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs237) sqrtLimbs237)
  | "limbs-e19m236", "fma" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs237) fmaLimbs237)
  | "limbs-e19m1023", "add" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs1024) addLimbs1024)
  | "limbs-e19m1023", "sub" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs1024) subLimbs1024)
  | "limbs-e19m1023", "mul" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs1024) mulLimbs1024)
  | "limbs-e19m1023", "div" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs1024) divLimbs1024)
  | "limbs-e19m1023", "sqrt" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs1024) sqrtLimbs1024)
  | "limbs-e19m1023", "fma" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs1024) fmaLimbs1024)
  | "limbs-e19m4095", "add" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs4096) addLimbs4096)
  | "limbs-e19m4095", "sub" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs4096) subLimbs4096)
  | "limbs-e19m4095", "mul" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs4096) mulLimbs4096)
  | "limbs-e19m4095", "div" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs4096) divLimbs4096)
  | "limbs-e19m4095", "sqrt" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs4096) sqrtLimbs4096)
  | "limbs-e19m4095", "fma" => some (timeWith (ExecFloat.Binary.ofNatBits : Nat → Limbs4096) fmaLimbs4096)
  | _, _ => none

end FloatLibBenchmarks.Public.TimeList

open FloatLibBenchmarks.Public.TimeList in
public def main (args : List String) : IO UInt32 := do
  let usage :=
    "usage: execFloatTimeList FORMAT add|sub|mul|div|sqrt|fma FILE TRIALS\n" ++
    "formats: e5m10, e8m7, e8m23, e11m52, e15m112, e19m236, e19m1023, e19m4095,\n" ++
    "         posit16, posit32, posit64, limbs-e19m236, limbs-e19m1023, limbs-e19m4095\n" ++
    "TRIALS must be a positive integer and FILE must contain at least one case"
  match args with
  | [format, name, path, trialsText] =>
      let some trials := trialsText.toNat? | IO.eprintln usage; return 1
      if trials == 0 then
        IO.eprintln usage
        return 1
      match pick? format name with
      | some action =>
          let cases ← readCases path
          if cases.isEmpty then
            IO.eprintln usage
            return 1
          action cases trials
          return 0
      | none => IO.eprintln usage; return 1
  | _ => IO.eprintln usage; return 1
